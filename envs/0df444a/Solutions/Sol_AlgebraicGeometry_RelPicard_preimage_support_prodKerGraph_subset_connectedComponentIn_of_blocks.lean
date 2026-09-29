-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3861fa12-96c4-56c9-a51c-b230eb81dfc3

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

namespace A2HDGCOMP

theorem mem_support_prod_iff {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (x : ↥X) :
    x ∈ (∏ i ∈ s, I i).support ↔ ∃ i ∈ s, x ∈ (I i).support := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
    constructor
    · intro h
      have h' : x ∈ ((⊥ : TopologicalSpace.Closeds ↥X) : Set ↥X) := h
      rw [TopologicalSpace.Closeds.coe_bot] at h'
      exact h'.elim
    · rintro ⟨i, hi, -⟩
      simp at hi
  | cons i s hi ih =>
    rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup,
      Set.mem_union, SetLike.mem_coe, SetLike.mem_coe, ih]
    simp only [Finset.mem_cons, exists_eq_or_imp]

theorem exists_mem_support_ker_graphOver {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S}
    {r : ℕ} (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) (x : ↥(pullback f g))
    (hx : x ∈ (prodKerGraph f a ha).support) : ∃ i, x ∈ (graphOver f (a i) (ha i)).ker.support := by
  rw [prodKerGraph_eq_prod] at hx
  obtain ⟨i, -, hi⟩ := (mem_support_prod_iff Finset.univ (fun i => (graphOver f (a i) (ha i)).ker) x).mp hx
  exact ⟨i, hi⟩

theorem isClosedImmersion_graphOver_of_le {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {r : ℕ}
    (D : RelEffCartierDiv f r g) (a : T ⟶ 𝒞) (ha : a ≫ f = g) (hle : D.I ≤ (graphOver f a ha).ker) :
    IsClosedImmersion (graphOver f a ha) := by
  have hker : D.I.subschemeι.ker ≤ (graphOver f a ha).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]; exact hle
  let l := IsClosedImmersion.lift D.I.subschemeι (graphOver f a ha) hker
  have hl : l ≫ D.I.subschemeι = graphOver f a ha := IsClosedImmersion.lift_fac _ _ _
  haveI : IsFinite (D.I.subschemeι ≫ pullback.snd f g) := D.isFinite
  haveI : IsClosedImmersion (l ≫ (D.I.subschemeι ≫ pullback.snd f g)) := by
    rw [← Category.assoc, hl, graphOver_snd]; infer_instance
  haveI : IsClosedImmersion l := .of_comp l (D.I.subschemeι ≫ pullback.snd f g)
  rw [← hl]; infer_instance

theorem mem_range_graphOver_of_mem_support {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {r : ℕ}
    (D : RelEffCartierDiv f r g) (a : T ⟶ 𝒞) (ha : a ≫ f = g) (hle : D.I ≤ (graphOver f a ha).ker)
    (x : ↥(pullback f g)) (hx : x ∈ (graphOver f a ha).ker.support) : x ∈ Set.range (graphOver f a ha).base := by
  haveI := isClosedImmersion_graphOver_of_le f D a ha hle
  have h := (graphOver f a ha).support_ker
  rw [(graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq] at h
  have hx' : x ∈ ((graphOver f a ha).ker.support : Set ↥(pullback f g)) := hx
  rwa [h] at hx'

theorem exists_eq_of_mem_image_support {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {r : ℕ}
    (D : RelEffCartierDiv f r g) (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) (hDI : D.I = prodKerGraph f a ha)
    (y : ↥𝒞) (hy : y ∈ (D.I.subschemeι ≫ pullback.fst f g).base '' Set.univ) :
    ∃ (i : Fin r) (t : ↥T), (a i).base t = y := by
  obtain ⟨w, -, rfl⟩ := hy

  have hxs : D.I.subschemeι.base w ∈ (D.I.support : Set ↥(pullback f g)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩
  have hxs' : D.I.subschemeι.base w ∈ (prodKerGraph f a ha).support := by rw [← hDI]; exact hxs
  obtain ⟨i, hi⟩ := exists_mem_support_ker_graphOver f a ha _ hxs'
  have hle : D.I ≤ (graphOver f (a i) (ha i)).ker := Scheme.IdealSheafData.le_def.mpr fun V => by
    rw [hDI, ideal_prodKerGraph]
    exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  obtain ⟨t, ht⟩ := mem_range_graphOver_of_mem_support f D (a i) (ha i) hle _ hi
  refine ⟨i, t, ?_⟩
  change (a i).base t = (pullback.fst f g).base (D.I.subschemeι.base w)
  rw [← ht]
  change _ = (graphOver f (a i) (ha i) ≫ pullback.fst f g).base t
  rw [graphOver_fst]

theorem image_connectedComponentIn_subset' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) (F : Set α) (x : α) :
    f '' connectedComponentIn F x ⊆ connectedComponentIn (f '' F) (f x) := by
  by_cases hx : x ∈ F
  · exact hf.image_connectedComponentIn_subset hx
  · rw [connectedComponentIn_eq_empty hx, Set.image_empty]; exact Set.empty_subset _

end A2HDGCOMP

open A2HDGCOMP in

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    (A : Type u) [CommRing A] [Algebra R A]
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (deg : Fin M → ℕ)
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (hσfac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
    {e : ℕ} (a : Fin e → Fin M) (m : ∀ i, Fin (deg i))
    (D : RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDI : D.I = prodKerGraph (baseChange R c A) (fun j => (σ (a j) (m (a j))).1) (fun j => (σ (a j) (m (a j))).2)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (baseChange R c A) s) →
      (pullback.fst (baseChange R c A) s).base ⁻¹'
          ((D.I.subschemeι ≫ pullback.fst (baseChange R c A) (𝟙 _)).base '' Set.univ) ⊆
        connectedComponentIn
          ((pullback.fst (baseChange R c A) s ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
              (pullback (baseChange R c A) s).Opens) : Set ↥(pullback (baseChange R c A) s))
          (((sectionFibrePoint (sectionBaseChange A ε) s).1).base (IsLocalRing.closedPoint k)) := by
  intro k _ _ s _hns x hx

  have hκ := BaseChange.κ_hom_fst c A s

  obtain ⟨j, t, ht⟩ := exists_eq_of_mem_image_support (baseChange R c A) D
    (fun j => (σ (a j) (m (a j))).1) (fun j => (σ (a j) (m (a j))).2) hDI _ hx

  obtain ⟨y, hy⟩ := hσfac (a j) (m (a j))
  have hmem : (BaseChange.κ c A s).hom.base x ∈
      (pullback.fst c (s ≫ specMap R A)).base ⁻¹' Set.range (z (a j)).base := by
    refine Set.mem_preimage.mpr ⟨y.base t, ?_⟩
    change (y ≫ z (a j)).base t = ((BaseChange.κ c A s).hom ≫ pullback.fst c (s ≫ specMap R A)).base x
    rw [← hy, hκ]
    change (pullback.fst c (specMap R A)).base (((σ (a j) (m (a j))).1).base t) =
      (pullback.fst c (specMap R A)).base ((pullback.fst (baseChange R c A) s).base x)
    rw [ht]
  have hcomp := hzε k (s ≫ specMap R A) (a j) hmem

  have hcont : Continuous (BaseChange.κ c A s).inv.base := (BaseChange.κ c A s).inv.continuous
  have hx' : (BaseChange.κ c A s).inv.base ((BaseChange.κ c A s).hom.base x) = x := by
    change ((BaseChange.κ c A s).hom ≫ (BaseChange.κ c A s).inv).base x = x
    rw [Iso.hom_inv_id]; rfl
  have himg := image_connectedComponentIn_subset' hcont
    ((pullback.fst c (s ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s ≫ specMap R A)).Opens) : Set ↥(pullback c (s ≫ specMap R A)))
    (((sectionFibrePoint ε (s ≫ specMap R A)).1).base (IsLocalRing.closedPoint k))

  have hsub : (BaseChange.κ c A s).inv.base ''
      ((pullback.fst c (s ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s ≫ specMap R A)).Opens) : Set ↥(pullback c (s ≫ specMap R A))) ⊆
      ((pullback.fst (baseChange R c A) s ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
        (pullback (baseChange R c A) s).Opens) : Set ↥(pullback (baseChange R c A) s)) := by
    rintro _ ⟨w, hw, rfl⟩
    change (((BaseChange.κ c A s).inv ≫ pullback.fst (baseChange R c A) s) ≫ pullback.fst c (specMap R A)).base w ∈ U
    rw [Category.assoc, ← hκ, Iso.inv_hom_id_assoc]
    exact hw

  have hpt : (BaseChange.κ c A s).inv.base (((sectionFibrePoint ε (s ≫ specMap R A)).1).base (IsLocalRing.closedPoint k)) =
      ((sectionFibrePoint (sectionBaseChange A ε) s).1).base (IsLocalRing.closedPoint k) := by
    change (rigSection c (s ≫ specMap R A) ε ≫ (BaseChange.κ c A s).inv).base (IsLocalRing.closedPoint k) = _
    rw [BaseChange.rigSection_κ_inv]
    rfl
  rw [hpt] at himg
  exact connectedComponentIn_mono _ hsub (himg ⟨_, hcomp, hx'⟩)

end S_AlgebraicGeometry_RelPicard_preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks (solution)
