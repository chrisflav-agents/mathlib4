/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Submodules of presheaves of modules

Given a presheaf of modules `M` over a presheaf of rings `R` and a family of
submodules `N X` of `M.obj X` that is stable under the restriction maps of `M`,
we construct the corresponding subobject of `M` in the category
`PresheafOfModules R`, together with its inclusion monomorphism.

## Main definitions

- `PresheafOfModules.Submodule M`: a family of submodules of `M`, stable
  under restriction.
- `PresheafOfModules.Submodule.toPresheafOfModules`: the associated
  presheaf of modules.
- `PresheafOfModules.Submodule.ι`: the inclusion into `M`, a monomorphism.
- `PresheafOfModules.Submodule.toSubfunctor`: the subfunctor of the underlying
  type-valued presheaf induced by a submodule.

The families of submodules of `M` form a `CompleteLattice`, with order given by
pointwise inclusion and all lattice operations computed pointwise.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X` of `M.obj X`, for a presheaf of modules `M`, stable
under the restriction maps of `M`. This is the data needed to cut out a
subobject of `M` in `PresheafOfModules R`. -/
structure Submodule (M : PresheafOfModules.{v} R) where
  /-- the submodule of `M.obj X` -/
  obj (X : Cᵒᵖ) : _root_.Submodule (R.obj X) (M.obj X)
  /-- the family is stable under restriction -/
  map_mem ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) ⦃m : M.obj X⦄ (hm : m ∈ obj X) :
    M.map f m ∈ obj Y

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

@[ext]
lemma ext {N₁ N₂ : M.Submodule} (h : ∀ X, N₁.obj X = N₂.obj X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

set_option backward.isDefEq.respectTransparency false in
/-- The subobject of `M` cut out by the family of submodules `N`, as a presheaf of modules: over
`X` it is the submodule `N.obj X`, with restriction maps induced by those of `M`. -/
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.obj X)
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (N.obj Y)))
    { toFun := fun m ↦ ⟨M.map f m.val, N.map_mem f m.property⟩
      map_add' := fun a b ↦ Subtype.ext (map_add (M.map f).hom a.val b.val)
      map_smul' := fun r m ↦ Subtype.ext (M.map_smul f r m.val) }

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    (N.toPresheafOfModules).obj X = ModuleCat.of _ (N.obj X) := rfl

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.obj X) :
    ((N.toPresheafOfModules).map f m).val = M.map f m.val := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.obj X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

@[simp]
lemma ι_app_apply (X : Cᵒᵖ) (m : N.obj X) : (N.ι).app X m = m.val := rfl

lemma ι_app_injective (X : Cᵒᵖ) : Function.Injective ((N.ι).app X) :=
  Subtype.val_injective

instance : Mono N.ι := mono_of_injective N.ι_app_injective

lemma mem_iff {X : Cᵒᵖ} (m : M.obj X) :
    (∃ n : N.obj X, (N.ι).app X n = m) ↔ m ∈ N.obj X :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ n.property, fun hm ↦ ⟨⟨m, hm⟩, rfl⟩⟩

section Lattice

instance : PartialOrder M.Submodule where
  le N₁ N₂ := ∀ X, N₁.obj X ≤ N₂.obj X
  le_refl N X := le_rfl
  le_trans N₁ N₂ N₃ h₁ h₂ X := (h₁ X).trans (h₂ X)
  le_antisymm N₁ N₂ h₁ h₂ := ext fun X ↦ le_antisymm (h₁ X) (h₂ X)

lemma le_def {N₁ N₂ : M.Submodule} :
    N₁ ≤ N₂ ↔ ∀ X, N₁.obj X ≤ N₂.obj X := Iff.rfl

instance : InfSet M.Submodule where
  sInf S :=
    { obj X := ⨅ N ∈ S, N.obj X
      map_mem := fun _ Y f m hm => by
        have h : ∀ N ∈ S, m ∈ N.obj _ := fun N hN => by
          rw [_root_.Submodule.mem_iInf] at hm
          replace hm := hm N
          rw [_root_.Submodule.mem_iInf] at hm
          exact hm hN
        -- `M.map f m` lives in the restriction of scalars of `M.obj Y`, so we fix the module
        -- explicitly to `M.obj Y` for the membership in the infimum.
        exact (@_root_.Submodule.mem_iInf _ (↑(M.obj Y)) _ _ _ _ _ (M.map f m)).mpr fun N =>
          (@_root_.Submodule.mem_iInf _ (↑(M.obj Y)) _ _ _ _ _ (M.map f m)).mpr fun hN =>
            N.map_mem f (h N hN) }

@[simp]
lemma sInf_obj (S : Set M.Submodule) (X : Cᵒᵖ) :
    (sInf S).obj X = ⨅ N ∈ S, N.obj X := rfl

/-- The submodules of a presheaf of modules form a complete lattice, with order given by
pointwise inclusion. Infima are computed pointwise. -/
instance : CompleteLattice M.Submodule :=
  completeLatticeOfInf M.Submodule fun _ =>
    ⟨fun N hN _ => iInf₂_le N hN, fun _ hb X => le_iInf₂ fun _ hN => hb hN X⟩

end Lattice

/-- The subfunctor of the underlying type-valued presheaf of `M` induced by a submodule `N`. -/
def toSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) where
  obj X := {r : M.obj X | r ∈ N.obj X}
  map := fun {_ _} f _ hr ↦ N.map_mem f hr

@[simp]
lemma mem_toSubfunctor_obj {X : Cᵒᵖ} (r : M.obj X) :
    r ∈ N.toSubfunctor.obj X ↔ r ∈ N.obj X := Iff.rfl

end Submodule

end PresheafOfModules
