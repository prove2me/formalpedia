-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
-- name    : PretorsionImageClosed_IndecomposableClosures_ModuleTraces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:41:41.790645+00:00
-- url     : https://prove2.me/theorems/778d9696-dbb0-4637-94a1-73f78833e189
-- title:
--   Module Traces
-- statement:
--   Definitions and structural lemmas for Module Traces, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
structure SelectedMapTo (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : σ.sumOver index label ⟶ X
structure SelectedMapFrom (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : X ⟶ σ.sumOver index label
def trace (S : Set ι) (X : FGModuleCat.{w} R) : Submodule R X :=
  ⨆ f : σ.SelectedMapTo S X, LinearMap.range f.map.hom.hom
def reject (S : Set ι) (X : FGModuleCat.{w} R) : Submodule R X :=
  ⨅ f : σ.SelectedMapFrom S X, LinearMap.ker f.map.hom.hom
def SelectedMapTo.flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X)) :
    σ.SelectedMapTo S X := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : outer, (pick t).index)
  let a : J → ι :=
    fun p ↦ (pick p.1).label p.2
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  exact
    { index := J
      label := a
      mem := fun p ↦ (pick p.1).mem p.2
      map := flattenIso.inv ≫
        biproduct.desc (fun t ↦ (pick t).map) }
namespace SelectedMapFrom
def flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapFrom S X)) :
    σ.SelectedMapFrom S X := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapFrom S X :=
    fun t ↦ (F.equivFin.symm t).1
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : outer, (pick t).index)
  let a : J → ι :=
    fun p ↦ (pick p.1).label p.2
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  exact
    { index := J
      label := a
      mem := fun p ↦ (pick p.1).mem p.2
      map := biproduct.lift (fun t ↦ (pick t).map) ≫
        flattenIso.hom }
end SelectedMapFrom
end PretorsionImageClosed.IndecomposableSkeleton


