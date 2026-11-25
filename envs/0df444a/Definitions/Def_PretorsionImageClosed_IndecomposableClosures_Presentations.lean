-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
-- name    : PretorsionImageClosed_IndecomposableClosures_Presentations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:37:23.454304+00:00
-- url     : https://prove2.me/theorems/9d37b681-6953-43d2-98a0-eb89cd06a234
-- title:
--   Presentations
-- statement:
--   Definitions and structural lemmas for Presentations, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean

module
public import Mathlib.CategoryTheory.FintypeCat
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
abbrev sumOver (J : FintypeCat.{0}) (a : J → ι) : FGModuleCat.{w} R :=
  biproduct fun t ↦ σ.obj (a t)
structure AddPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  iso : X ≅ σ.sumOver index label
structure FacPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : σ.sumOver index label ⟶ X
  epi : Epi map
structure SubPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : X ⟶ σ.sumOver index label
  mono : Mono map
def InAdd (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.AddPresentation S X)
def InFac (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.FacPresentation S X)
def InSub (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.SubPresentation S X)
def qSet (S : Set ι) : Set ι :=
  {j | σ.InFac S (σ.obj j)}
def sSet (S : Set ι) : Set ι :=
  {j | σ.InSub S (σ.obj j)}
namespace FacPresentation
def of_subset {S T : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation S X) (hST : S ⊆ T) :
    σ.FacPresentation T X where
  index := P.index
  label := P.label
  mem t := hST (P.mem t)
  map := P.map
  epi := P.epi
end FacPresentation
namespace SubPresentation
def of_subset {S T : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.SubPresentation S X) (hST : S ⊆ T) :
    σ.SubPresentation T X where
  index := P.index
  label := P.label
  mem t := hST (P.mem t)
  map := P.map
  mono := P.mono
end SubPresentation
theorem qSet_monotone : Monotone σ.qSet := by
  intro S T hST j hj
  exact hj.map fun P ↦ FacPresentation.of_subset σ P hST
theorem sSet_monotone : Monotone σ.sSet := by
  intro S T hST j hj
  exact hj.map fun P ↦ SubPresentation.of_subset σ P hST
theorem subset_qSet (S : Set ι) : S ⊆ σ.qSet S := by
  intro j hj
  let a : Fin 1 → ι := fun _ ↦ j
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hj
    map := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom
    epi := inferInstance }⟩
theorem subset_sSet (S : Set ι) : S ⊆ σ.sSet S := by
  intro j hj
  let a : Fin 1 → ι := fun _ ↦ j
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hj
    map := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).inv
    mono := inferInstance }⟩
theorem inFac_trans {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation (σ.qSet S) X) :
    σ.InFac S X := by
  classical
  let inner : ∀ t : P.index,
      σ.FacPresentation S (σ.obj (P.label t)) :=
    fun t ↦ Classical.choice (P.mem t)
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : P.index, (inner t).index)
  let a : J → ι :=
    fun p ↦ (inner p.1).label p.2
  let flattenIso :
      (⨁ fun t : P.index ↦
        σ.sumOver (inner t).index (inner t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : P.index ↦ (inner t).index)
      (fun t s ↦ σ.obj ((inner t).label s))
  let g :
      σ.sumOver J a ⟶ X :=
    flattenIso.inv ≫
      biproduct.map (fun t ↦ (inner t).map) ≫ P.map
  refine ⟨{
    index := J
    label := a
    mem := ?_
    map := g
    epi := ?_ }⟩
  · intro p
    exact (inner p.1).mem p.2
  · letI (t : P.index) : Epi (inner t).map :=
      (inner t).epi
    letI : Epi P.map := P.epi
    dsimp only [g]
    infer_instance
theorem inSub_trans {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.SubPresentation (σ.sSet S) X) :
    σ.InSub S X := by
  classical
  let inner : ∀ t : P.index,
      σ.SubPresentation S (σ.obj (P.label t)) :=
    fun t ↦ Classical.choice (P.mem t)
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : P.index, (inner t).index)
  let a : J → ι :=
    fun p ↦ (inner p.1).label p.2
  let flattenIso :
      (⨁ fun t : P.index ↦
        σ.sumOver (inner t).index (inner t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : P.index ↦ (inner t).index)
      (fun t s ↦ σ.obj ((inner t).label s))
  let g :
      X ⟶ σ.sumOver J a :=
    P.map ≫
      biproduct.map (fun t ↦ (inner t).map) ≫ flattenIso.hom
  refine ⟨{
    index := J
    label := a
    mem := ?_
    map := g
    mono := ?_ }⟩
  · intro p
    exact (inner p.1).mem p.2
  · letI (t : P.index) : Mono (inner t).map :=
      (inner t).mono
    letI : Mono P.map := P.mono
    dsimp only [g]
    infer_instance
theorem qSet_idempotent (S : Set ι) :
    σ.qSet (σ.qSet S) = σ.qSet S := by
  apply Set.Subset.antisymm
  · intro j hj
    exact inFac_trans σ (Classical.choice hj)
  · exact qSet_monotone σ (subset_qSet σ S)
theorem sSet_idempotent (S : Set ι) :
    σ.sSet (σ.sSet S) = σ.sSet S := by
  apply Set.Subset.antisymm
  · intro j hj
    exact inSub_trans σ (Classical.choice hj)
  · exact sSet_monotone σ (subset_sSet σ S)
def qClosure : SetClosure ι where
  toFun := σ.qSet
  monotone' := qSet_monotone σ
  le_closure' := subset_qSet σ
  idempotent' := qSet_idempotent σ
def sClosure : SetClosure ι where
  toFun := σ.sSet
  monotone' := sSet_monotone σ
  le_closure' := subset_sSet σ
  idempotent' := sSet_idempotent σ
end PretorsionImageClosed.IndecomposableSkeleton


