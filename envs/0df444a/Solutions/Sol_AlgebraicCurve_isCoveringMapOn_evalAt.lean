-- Prove2me | solution 1 for AlgebraicCurve.isCoveringMapOn_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b1ece540-6be5-5bf3-984b-80d017eb9cf5

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isCoveringMapOn_evalAt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 6400000

section SectRegion0

open AlgebraicCurve
open scoped Manifold ContDiff

namespace C0RegionB

p2m_open "AlgebraicCurve.Place"

private theorem _root_.C0RegionB.evalAt_sub_algebraMap {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

p2m_export "C0RegionB" "evalAt_sub_algebraMap"

theorem isOpen_setOf_mem_toValuationSubring {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)]
    {f : F} (hf0 : f ≠ 0) :
    IsOpen {P : Place ℂ F | f ∈ P.toValuationSubring} := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf0
  have hsub : {P : Place ℂ F | f ∉ P.toValuationSubring} ⊆ ↑D.support := by
    intro P hP
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD P]
    intro h0
    exact hP (P.mem_of_ord_nonneg hf0 (le_of_eq h0.symm))
  have hcl : IsClosed {P : Place ℂ F | f ∉ P.toValuationSubring} :=
    (Set.Finite.subset D.support.finite_toSet hsub).isClosed
  have : {P : Place ℂ F | f ∈ P.toValuationSubring}
      = {P : Place ℂ F | f ∉ P.toValuationSubring}ᶜ := by
    ext P; simp
  rw [this]
  exact hcl.isOpen_compl

theorem finite_setOf_evalAt_eq {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f) (t : ℂ) :
    {P : Place ℂ F | f ∈ P.toValuationSubring ∧ P.evalAt f = t}.Finite := by
  have hft : f - algebraMap ℂ F t ≠ 0 := by
    intro h
    exact hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap t)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) _ hft
  refine Set.Finite.subset D.support.finite_toSet ?_
  rintro P ⟨hmem, hval⟩
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD P]
  intro h0
  have h1 : P.evalAt (f - algebraMap ℂ F t) = 0 := by
    rw [evalAt_sub_algebraMap P (hrat P) hmem, hval, sub_self]
  exact P.evalAt_ne_zero_of_ord_eq_zero (hrat P) hft h0 h1

theorem read_center_eq {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (P : Place ℂ F) (f : F) :
    Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) f
      = P.evalAt f := by
  rw [extChartAt_to_inv]

theorem read_sub_eventuallyEq {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)] (hrat : ∀ P : Place ℂ F, P.IsRational)
    (P : Place ℂ F) {f : F} (hf0 : f ≠ 0) (hfP : f ∈ P.toValuationSubring) (c : ℂ) :
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) (f - algebraMap ℂ F c))
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)]
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f - c) := by
  have hopen := isOpen_setOf_mem_toValuationSubring (F := F) hf0
  have hcont : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P) :=
    continuousAt_extChartAt_symm P
  have hmemP : (extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)
      ∈ {Q : Place ℂ F | f ∈ Q.toValuationSubring} := by
    rw [extChartAt_to_inv]; exact hfP
  have hev : ∀ᶠ z in nhds (extChartAt 𝓘(ℂ, ℂ) P P),
      (extChartAt 𝓘(ℂ, ℂ) P).symm z ∈ {Q : Place ℂ F | f ∈ Q.toValuationSubring} :=
    hcont.eventually_mem (hopen.mem_nhds hmemP)
  filter_upwards [hev] with z hz
  exact evalAt_sub_algebraMap _ (hrat _) hz c

theorem exists_hasStrictDerivAt_read {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    (P : Place ℂ F) {f : F} (hf : Transcendental ℂ f) (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    ∃ d : ℂ, d ≠ 0 ∧ HasStrictDerivAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) d
      (extChartAt 𝓘(ℂ, ℂ) P P) := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hg0 : f - algebraMap ℂ F (P.evalAt f) ≠ 0 := by
    intro h
    exact hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap _)
  obtain ⟨hmer, horder⟩ := hF _ hg0 P
  have h1 : meromorphicOrderAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z)
        (f - algebraMap ℂ F (P.evalAt f)))
      (extChartAt 𝓘(ℂ, ℂ) P P) = ((1 : ℤ) : WithTop ℤ) := by
    rw [horder, hord]
  obtain ⟨g, hgan, hgne, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp h1
  have hstrict : HasStrictDerivAt
      (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      (g (extChartAt 𝓘(ℂ, ℂ) P P)) (extChartAt 𝓘(ℂ, ℂ) P P) := by
    have hid : HasStrictDerivAt (fun z : ℂ => z - extChartAt 𝓘(ℂ, ℂ) P P) (1 - 0)
        (extChartAt 𝓘(ℂ, ℂ) P P) :=
      (hasStrictDerivAt_id _).sub (hasStrictDerivAt_const _ _)
    have hmul := hid.mul hgan.hasStrictDerivAt
    have := hmul.const_add (P.evalAt f)
    simpa using this
  have hB5 := read_sub_eventuallyEq (F := F) hrat P hf0 hfP (P.evalAt f)
  have hval : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) f
      = P.evalAt f := read_center_eq P f
  have heq : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)]
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
    have hne : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
        =ᶠ[nhdsWithin (extChartAt 𝓘(ℂ, ℂ) P P) {extChartAt 𝓘(ℂ, ℂ) P P}ᶜ]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
      filter_upwards [hgeq, hB5.filter_mono nhdsWithin_le_nhds] with z h2 h3
      have h4 : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f - P.evalAt f
          = (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z := by
        rw [← h3, h2]
        simp [smul_eq_mul]
      linear_combination -h4
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne ?_
    simp
  exact ⟨g (extChartAt 𝓘(ℂ, ℂ) P P), hgne, hstrict.congr_of_eventuallyEq heq⟩

end C0RegionB

end SectRegion0

section SectRegion1

open AlgebraicCurve Topology
open scoped Manifold ContDiff

namespace C0RegionB

p2m_open "AlgebraicCurve.Place"

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  [T2Space (Place ℂ F)]

theorem continuousAt_evalAt
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (P : Place ℂ F) {f : F} (hfP : f ∈ P.toValuationSubring) :
    ContinuousAt (fun Q : Place ℂ F => Place.evalAt Q f) P := by
  have han := Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF P hfP
  have h1 : (fun Q : Place ℂ F => Place.evalAt Q f)
      =ᶠ[nhds P] (fun Q : Place ℂ F =>
        Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P Q)) f) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) P] with Q hQ
    rw [PartialEquiv.left_inv _ hQ]
  exact ContinuousAt.congr_of_eventuallyEq
    (han.continuousAt.comp (continuousAt_extChartAt P)) h1

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in

theorem eventually_notMem_of_pole
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (P : Place ℂ F) {f : F} (hf0 : f ≠ 0) (hP : f ∉ P.toValuationSubring)
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ Q in nhds P, ¬ (f ∈ Q.toValuationSubring ∧ Place.evalAt Q f ∈ K) := by
  obtain ⟨hmer, horder⟩ := hF f hf0 P
  have hordneg : P.ord f < 0 := by
    by_contra h
    exact hP (P.mem_of_ord_nonneg hf0 (not_lt.mp h))
  have hneg : meromorphicOrderAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) P P) < 0 := by
    rw [horder]
    exact_mod_cast hordneg
  have htend := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  have htop : Filter.Tendsto
      (fun z : ℂ => ‖Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f‖)
      (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) P P) {extChartAt 𝓘(ℂ, ℂ) P P}ᶜ) Filter.atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr htend
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hK.isBounded
  have hev1 : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ, ℂ) P P) {extChartAt 𝓘(ℂ, ℂ) P P}ᶜ,
      r < ‖Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f‖ :=
    htop.eventually_gt_atTop r
  have hev2 : ∀ᶠ z in nhds (extChartAt 𝓘(ℂ, ℂ) P P),
      z ≠ extChartAt 𝓘(ℂ, ℂ) P P →
        r < ‖Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f‖ := by
    have := eventually_nhdsWithin_iff.mp hev1
    filter_upwards [this] with z hz hzne
    exact hz (by simpa using hzne)
  have hch := (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) P).eventually hev2
  filter_upwards [hch, extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) P] with Q hQ hQs
  rintro ⟨hmem, hval⟩
  by_cases hQP : Q = P
  · exact hP (hQP ▸ hmem)
  · have hne : extChartAt 𝓘(ℂ, ℂ) P Q ≠ extChartAt 𝓘(ℂ, ℂ) P P := by
      intro h
      exact hQP ((extChartAt 𝓘(ℂ, ℂ) P).injOn hQs (mem_extChartAt_source P) h)
    have hgt := hQ hne
    rw [PartialEquiv.left_inv _ hQs] at hgt
    have hle : ‖Place.evalAt Q f‖ ≤ r := by
      simpa [Complex.dist_eq, Metric.mem_closedBall] using hr hval
    exact absurd hgt (not_lt.mpr hle)

theorem isClosedMap_evalAt_subtype [CompactSpace (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    {f : F} (hf : Transcendental ℂ f) :
    IsClosedMap (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
      Place.evalAt P.1 f) := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hcont : Continuous (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
      Place.evalAt P.1 f) := by
    rw [continuous_iff_continuousAt]
    intro P
    exact (continuousAt_evalAt hF P.1 P.2).comp continuous_subtype_val.continuousAt
  refine (isProperMap_iff_isCompact_preimage.mpr ⟨hcont, fun K hK => ?_⟩).isClosedMap
  have hA : IsClosed {P : Place ℂ F | f ∈ P.toValuationSubring ∧ Place.evalAt P f ∈ K} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro P hP
    by_cases hpole : f ∈ P.toValuationSubring
    · have hval : Place.evalAt P f ∈ Kᶜ := by
        by_contra h
        exact hP ⟨hpole, not_not.mp h⟩
      have hev := (continuousAt_evalAt hF P hpole).preimage_mem_nhds
        (hK.isClosed.isOpen_compl.mem_nhds hval)
      filter_upwards [hev] with Q hQ
      rintro ⟨-, hQK⟩
      exact hQ hQK
    · filter_upwards [eventually_notMem_of_pole hF P hf0 hpole hK] with Q hQ
      exact hQ
  have hAcomp : IsCompact {P : Place ℂ F | f ∈ P.toValuationSubring ∧ Place.evalAt P f ∈ K} :=
    hA.isCompact
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himg : (Subtype.val '' ((fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
        Place.evalAt P.1 f) ⁻¹' K))
      = {P : Place ℂ F | f ∈ P.toValuationSubring ∧ Place.evalAt P f ∈ K} := by
    ext P
    constructor
    · rintro ⟨⟨Q, hQ⟩, hQK, rfl⟩
      exact ⟨hQ, hQK⟩
    · rintro ⟨hP, hPK⟩
      exact ⟨⟨P, hP⟩, hPK, rfl⟩
  rw [himg]
  exact hAcomp

end C0RegionB

end SectRegion1

section SectRegion2

open AlgebraicCurve Polynomial

namespace C0RegionT

noncomputable def towerHom {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f) : RatFunc ℂ →ₐ[ℂ] F :=
  RatFunc.liftAlgHom (Polynomial.aeval f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hf))

theorem towerHom_injective {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f) : Function.Injective (towerHom hf) :=
  (towerHom hf).injective

theorem towerHom_X {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f) : towerHom hf RatFunc.X = f := by
  rw [← RatFunc.algebraMap_X, ← div_one ((algebraMap ℂ[X] (RatFunc ℂ)) Polynomial.X),
    ← map_one (algebraMap ℂ[X] (RatFunc ℂ))]
  rw [towerHom, RatFunc.liftAlgHom_apply_div]
  simp

theorem exists_towerHom_eq {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f) {y : F}
    (hy : y ∈ IntermediateField.adjoin ℂ ({f} : Set F)) :
    ∃ r : RatFunc ℂ, towerHom hf r = y := by
  have hle : IntermediateField.adjoin ℂ ({f} : Set F) ≤ (towerHom hf).fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨RatFunc.X, towerHom_X hf⟩
  exact hle hy

theorem finiteDimensional_towerHom {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({f} : Set F)) F] :
    letI := (towerHom hf).toAlgebra
    FiniteDimensional (RatFunc ℂ) F := by
  letI := (towerHom hf).toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Submodule (IntermediateField.adjoin ℂ ({f} : Set F)) F).FG :=
    Module.finite_def.mp inferInstance
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span (IntermediateField.adjoin ℂ ({f} : Set F)) (s : Set F) := by
    rw [hs]; trivial
  refine Submodule.span_induction (fun y hy => Submodule.subset_span hy)
    (Submodule.zero_mem _) (fun y z _ _ hy hz => Submodule.add_mem _ hy hz)
    (fun c y _ hy => ?_) hx
  obtain ⟨r, hr⟩ := exists_towerHom_eq hf c.2
  have hcy : c • y = r • y := by
    rw [IntermediateField.smul_def, smul_eq_mul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hr]
  rw [hcy]
  exact Submodule.smul_mem _ r hy

theorem isScalarTower_towerHom {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f) :
    letI := (towerHom hf).toAlgebra
    IsScalarTower ℂ (RatFunc ℂ) F := by
  letI := (towerHom hf).toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [RingHom.algebraMap_toAlgebra]
  exact ((towerHom hf).comp_algebraMap).symm

theorem isRational_of_tower {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({f} : Set F)) F]
    (v : Place ℂ F) : v.IsRational := by
  letI := (towerHom hf).toAlgebra
  haveI := finiteDimensional_towerHom hf
  haveI := isScalarTower_towerHom hf
  exact Place.isRational_of_isAlgClosed v

end C0RegionT

end SectRegion2

section SectRegion4

open scoped Manifold ContDiff Topology
open Set Filter AlgebraicCurve

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem read_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) z =
      Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f := rfl

theorem eventually_read_eq_read_comp (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w), ∀ f : F,
      Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f =
        Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm
          (extChartAt 𝓘(ℂ, ℂ) w ((extChartAt 𝓘(ℂ, ℂ) v).symm z))) f := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w) :=
    continuousAt_extChartAt_symm' hw
  have hmem : (extChartAt 𝓘(ℂ, ℂ) w).source ∈
      𝓝 ((extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w)) := by
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
    exact (isOpen_extChartAt_source w).mem_nhds (mem_extChartAt_source w)
  filter_upwards [hc.preimage_mem_nhds hmem] with z hz f
  rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hz]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_coordChange (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm)
      (extChartAt 𝓘(ℂ, ℂ) w Q) := by
  have hy : extChartAt 𝓘(ℂ, ℂ) w Q ∈
      ((extChartAt 𝓘(ℂ, ℂ) w).symm ≫ extChartAt 𝓘(ℂ, ℂ) P).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨(extChartAt 𝓘(ℂ, ℂ) w).map_source hw, ?_⟩
    rw [mem_preimage, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact hP
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) P w hy
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.analyticAt

theorem deriv_coordChange_ne_zero (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    deriv (extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v w) ≠ 0 := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  set σ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hσ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  have hσa : AnalyticAt ℂ σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) := by
    rw [hτw]
    exact analyticAt_coordChange w v w (mem_extChartAt_source w) hw
  have hid : (σ ∘ τ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v w)] id := by
    have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w), z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target :=
      (isOpen_extChartAt_target v).mem_nhds ((extChartAt 𝓘(ℂ, ℂ) v).map_source hw)
    have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w) :=
      continuousAt_extChartAt_symm' hw
    have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w),
        (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) w).source := by
      refine hc.preimage_mem_nhds ?_
      rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
      exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) w).mem_nhds (mem_extChartAt_source w)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hz2, (extChartAt 𝓘(ℂ, ℂ) v).right_inv hz1]
  have hcomp : HasDerivAt (σ ∘ τ)
      (deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) v w))
      (extChartAt 𝓘(ℂ, ℂ) v w) :=
    HasDerivAt.comp _ hσa.differentiableAt.hasDerivAt hτa.differentiableAt.hasDerivAt
  have hone : deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) v w) = 1 := by
    rw [← (hcomp.congr_of_eventuallyEq hid.symm).deriv, deriv_id]
  intro h0
  rw [h0, mul_zero] at hone
  exact zero_ne_one hone

theorem meromorphicOrderAt_read_eq (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (f : F) :
    meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v w) =
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) w w) := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f) hτa
    (deriv_coordChange_ne_zero v w hw)
  rw [hτw] at hcomp
  rw [← hcomp]
  refine meromorphicOrderAt_congr ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_read_eq_read_comp v w hw)]
    with z hz
  simp only [Function.comp_apply, hτ]
  exact hz f

theorem meromorphicAt_read_of_meromorphicAt (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) (f : F)
    (h : MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) w w)) :
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v w) := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  rw [← hτw] at h
  refine (h.comp_analyticAt hτa).congr ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_read_eq_read_comp v w hw)]
    with z hz
  simp only [Function.comp_apply, hτ]
  exact (hz f).symm

theorem analyticAt_read_of_analyticAt (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) (f : F)
    (h : AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) w w)) :
    AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v w) := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  have hcomp := h.comp_of_eq hτa hτw
  refine hcomp.congr ?_
  filter_upwards [eventually_read_eq_read_comp v w hw] with z hz
  simp only [Function.comp_apply, hτ]
  exact (hz f).symm

section Compatible

variable (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
include hF

theorem meromorphicAt_read (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F}
    (hf : f ≠ 0) :
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v w) ∧
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v w) = (w.ord f : WithTop ℤ) :=
  ⟨meromorphicAt_read_of_meromorphicAt v w hw f (hF f hf w).1,
    (meromorphicOrderAt_read_eq v w hw f).trans (hF f hf w).2⟩

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

theorem analyticAt_read_of_mem (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source)
    {f : F} (hf : f ∈ w.toValuationSubring) :
    AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v w) :=
  analyticAt_read_of_analyticAt v w hw f
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf)

end Compatible

end ChartTransition

namespace C0RegionG

p2m_open "AlgebraicCurve AlgebraicCurve.Place Topology Filter"

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [IsCurveOver ℂ F]

theorem evalAt_sub_algebraMap {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

theorem ord_pos_of_evalAt_eq_zero {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hz : v.evalAt g = 0) : 0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd hz (v.evalAt_ne_zero_of_ord_eq_zero hv hg h.symm)

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem read_sub_eventuallyEq' (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F} (hf0 : f ≠ 0)
    (hfw : f ∈ w.toValuationSubring) (hrat : ∀ u : Place ℂ F, u.IsRational) (c : ℂ) :
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) (f - algebraMap ℂ F c))
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) v w)]
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f - c) := by
  have hopen : IsOpen {P : Place ℂ F | f ∈ P.toValuationSubring} := by
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf0
    have hsub : {P : Place ℂ F | f ∉ P.toValuationSubring} ⊆ ↑D.support := by
      intro P hP
      by_contra hPD
      refine hP (P.mem_of_ord_nonneg hf0 ?_)
      have hz : D P = 0 := by
        simpa [Finsupp.mem_support_iff, not_not] using hPD
      have := hD P
      omega
    rw [← isClosed_compl_iff]
    exact (Set.Finite.subset D.support.finite_toSet hsub).isClosed
  have hcont : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w) :=
    continuousAt_extChartAt_symm'' ((extChartAt 𝓘(ℂ, ℂ) v).map_source hw)
  have hev : ∀ᶠ z in nhds (extChartAt 𝓘(ℂ, ℂ) v w),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
    have hwmem : (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w)
        ∈ {P : Place ℂ F | f ∈ P.toValuationSubring} := by
      rw [PartialEquiv.left_inv _ hw]; exact hfw
    exact hcont.eventually_mem (hopen.mem_nhds hwmem)
  filter_upwards [hev] with z hz
  exact evalAt_sub_algebraMap _ (hrat _) hz c

section WithHF

variable (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))

include hF in

theorem deriv_read_eq_zero_of_critical (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F} (htr : Transcendental ℂ f)
    (hrat : ∀ u : Place ℂ F, u.IsRational)
    (hfw : f ∈ w.toValuationSubring)
    (hcrit : 2 ≤ w.ord (f - algebraMap ℂ F (w.evalAt f))) :
    deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v w) = 0 := by
  have hf0 : f ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have hg0 : f - algebraMap ℂ F (w.evalAt f) ≠ 0 := fun h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap _)
  set z₀ := extChartAt 𝓘(ℂ, ℂ) v w with hz₀
  set n := w.ord (f - algebraMap ℂ F (w.evalAt f)) with hn
  have hmer := (ChartTransition.meromorphicAt_read (hF := hF) v w hw hg0).1
  have horder := (ChartTransition.meromorphicAt_read (hF := hF) v w hw hg0).2
  rw [← hz₀] at hmer horder
  rw [← hn] at horder
  rw [meromorphicOrderAt_eq_int_iff hmer] at horder
  obtain ⟨h, hh, hh0, hev⟩ := horder
  have hn0 : n ≠ 0 := by omega
  have hcentre : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z₀)
      (f - algebraMap ℂ F (w.evalAt f)) = 0 := by
    rw [hz₀, PartialEquiv.left_inv _ hw,
      evalAt_sub_algebraMap _ (hrat w) hfw, sub_self]
  have hfull : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z)
      (f - algebraMap ℂ F (w.evalAt f)))
      =ᶠ[nhds z₀] (fun z : ℂ => (z - z₀) ^ n • h z) := by
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hev ?_
    rw [hcentre, sub_self, zero_zpow n hn0, zero_smul]
  obtain ⟨m, hm, hm2⟩ : ∃ m : ℕ, n = (m : ℤ) ∧ 2 ≤ m :=
    ⟨n.toNat, by omega, by omega⟩
  have hmodel : HasDerivAt (fun z : ℂ => (z - z₀) ^ n • h z) 0 z₀ := by
    have heq : (fun z : ℂ => (z - z₀) ^ n • h z)
        = fun z : ℂ => (z - z₀) ^ m * h z := by
      funext z
      rw [hm, zpow_natCast, smul_eq_mul]
    rw [heq]
    have hp : HasDerivAt (fun z : ℂ => (z - z₀) ^ m)
        ((m : ℂ) * (z₀ - z₀) ^ (m - 1) * 1) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).pow m
    have hh' : HasDerivAt h (deriv h z₀) z₀ := hh.differentiableAt.hasDerivAt
    have hmul := hp.mul hh'
    convert hmul using 1
    all_goals try rfl
    rw [sub_self, zero_pow (show m - 1 ≠ 0 by omega), zero_pow (show m ≠ 0 by omega)]
    ring
  have hderg : deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z)
      (f - algebraMap ℂ F (w.evalAt f))) z₀ = 0 := by
    rw [hfull.deriv_eq]
    exact hmodel.deriv
  have hsubev := read_sub_eventuallyEq' v w hw hf0 hfw hrat (w.evalAt f)
  rw [← hz₀] at hsubev
  calc deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) z₀
      = deriv (fun z : ℂ =>
          Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f - w.evalAt f) z₀ :=
        (deriv_sub_const _).symm
    _ = deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z)
          (f - algebraMap ℂ F (w.evalAt f))) z₀ := hsubev.deriv_eq.symm
    _ = 0 := hderg

include hF in

theorem finite_critical [CompactSpace (Place ℂ F)]
    {f : F} (htr : Transcendental ℂ f) (hrat : ∀ u : Place ℂ F, u.IsRational) :
    {w : Place ℂ F | f ∈ w.toValuationSubring
      ∧ 2 ≤ w.ord (f - algebraMap ℂ F (w.evalAt f))}.Finite := by
  classical
  have hf0 : f ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  set S := {w : Place ℂ F | f ∈ w.toValuationSubring
      ∧ 2 ≤ w.ord (f - algebraMap ℂ F (w.evalAt f))} with hS
  by_contra hfin
  have hinf : S.Infinite := hfin
  have hball : ∀ v : Place ℂ F, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) v v) r ⊆ (extChartAt 𝓘(ℂ, ℂ) v).target := by
    intro v
    have ht : (extChartAt 𝓘(ℂ, ℂ) v).target ∈ nhds (extChartAt 𝓘(ℂ, ℂ) v v) :=
      extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) v
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ht
    exact ⟨r, hr, hsub⟩
  choose r hrpos hrsub using hball
  set U : Place ℂ F → Set (Place ℂ F) := fun v =>
    (extChartAt 𝓘(ℂ, ℂ) v).source
      ∩ (extChartAt 𝓘(ℂ, ℂ) v) ⁻¹' (Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v)) with hU
  have hUopen : ∀ v, IsOpen (U v) := fun v =>
    (continuousOn_extChartAt v).isOpen_inter_preimage
      (isOpen_extChartAt_source v) Metric.isOpen_ball
  have hUmem : ∀ v, v ∈ U v := fun v =>
    ⟨mem_extChartAt_source v, Metric.mem_ball_self (hrpos v)⟩
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩)
  have hpiece : ∃ v ∈ t, (S ∩ U v).Infinite := by
    by_contra hall
    push Not at hall
    refine hinf ?_
    have hcover : S ⊆ ⋃ v ∈ t, S ∩ U v := by
      intro w hw
      obtain ⟨v, hvt, hvU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ w))
      exact Set.mem_iUnion₂.mpr ⟨v, hvt, hw, hvU⟩
    exact Set.Finite.subset
      (Set.Finite.biUnion t.finite_toSet (fun v hv => hall v hv)) hcover
  obtain ⟨v, -, hvinf⟩ := hpiece
  have hinj : Set.InjOn (extChartAt 𝓘(ℂ, ℂ) v) (S ∩ U v) :=
    (extChartAt 𝓘(ℂ, ℂ) v).injOn.mono (fun w hw => hw.2.1)
  have himg_inf : ((extChartAt 𝓘(ℂ, ℂ) v) '' (S ∩ U v)).Infinite :=
    hvinf.image hinj
  have himg_sub : (extChartAt 𝓘(ℂ, ℂ) v) '' (S ∩ U v)
      ⊆ Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) v v) (r v) := by
    rintro - ⟨w, hw, rfl⟩
    exact Metric.ball_subset_closedBall hw.2.2
  obtain ⟨z₀, hz₀K, hacc⟩ :=
    himg_inf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) himg_sub
  have hz₀t : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) v).target := hrsub v hz₀K
  set Q := (extChartAt 𝓘(ℂ, ℂ) v).symm z₀ with hQ
  have hQs : Q ∈ (extChartAt 𝓘(ℂ, ℂ) v).source := (extChartAt 𝓘(ℂ, ℂ) v).map_target hz₀t
  have hz₀Q : extChartAt 𝓘(ℂ, ℂ) v Q = z₀ := (extChartAt 𝓘(ℂ, ℂ) v).right_inv hz₀t
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      z ∈ (extChartAt 𝓘(ℂ, ℂ) v) '' (S ∩ U v) := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨y, hy⟩ := (Filter.inf_principal_neBot_iff.mp hacc) V hV
    exact ⟨y, hy.1, hy.2⟩
  have hfreq0 : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) z = 0 := by
    refine hfreq.mono ?_
    rintro - ⟨w, ⟨⟨hwf, hwcrit⟩, hwU⟩, rfl⟩
    exact deriv_read_eq_zero_of_critical hF v w hwU.1 htr hrat hwf hwcrit
  set c : ℂ := if f ∈ Q.toValuationSubring then Q.evalAt f else 0 with hc
  set g := f - algebraMap ℂ F c with hgdef
  have hg0 : g ≠ 0 := fun h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
  have hm_ne : Q.ord g ≠ 0 := by
    by_cases hQf : f ∈ Q.toValuationSubring
    · have hc' : c = Q.evalAt f := by rw [hc, if_pos hQf]
      have hmem : g ∈ Q.toValuationSubring := by
        rw [hgdef]
        exact sub_mem hQf (Q.algebraMap_mem' _)
      have hpos : 0 < Q.ord g := by
        refine ord_pos_of_evalAt_eq_zero Q (hrat Q) hg0 hmem ?_
        rw [hgdef, hc', evalAt_sub_algebraMap _ (hrat Q) hQf, sub_self]
      omega
    · have hc' : c = 0 := by rw [hc, if_neg hQf]
      have hgf : g = f := by rw [hgdef, hc', map_zero, sub_zero]
      have hneg : ¬ 0 ≤ Q.ord f := fun hge => hQf (Q.mem_of_ord_nonneg hf0 hge)
      rw [hgf]
      omega
  have hsubev : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
      =ᶠ[nhds z₀]
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f - c) := by
    by_cases hQf : f ∈ Q.toValuationSubring
    · have hc' : c = Q.evalAt f := by rw [hc, if_pos hQf]
      have := read_sub_eventuallyEq' v Q hQs hf0 hQf hrat c
      rwa [hz₀Q] at this
    · have hc' : c = 0 := by rw [hc, if_neg hQf]
      have hgf : g = f := by rw [hgdef, hc', map_zero, sub_zero]
      rw [hgf, hc']
      filter_upwards with z
      rw [sub_zero]
  have hfreqg : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g) z = 0 := by
    have hde : deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        =ᶠ[nhds z₀]
        deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) := by
      refine hsubev.deriv.trans ?_
      filter_upwards with z
      rw [deriv_sub_const]
    exact (hfreq0.and_eventually (hde.filter_mono nhdsWithin_le_nhds)).mono
      (fun z hz => hz.2.trans hz.1)
  have hmerg : MeromorphicAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g) z₀ := by
    have := (ChartTransition.meromorphicAt_read (hF := hF) v Q hQs hg0).1
    rwa [hz₀Q] at this
  have horderg : meromorphicOrderAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g) z₀
      = (Q.ord g : WithTop ℤ) := by
    have := (ChartTransition.meromorphicAt_read (hF := hF) v Q hQs hg0).2
    rwa [hz₀Q] at this
  have h0 : deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
      =ᶠ[nhdsWithin z₀ {z₀}ᶜ] 0 :=
    (MeromorphicAt.frequently_zero_iff_eventuallyEq_zero hmerg.deriv).mp hfreqg
  rw [meromorphicOrderAt_eq_int_iff hmerg] at horderg
  obtain ⟨h, hh, hh0, hev⟩ := horderg
  set m := Q.ord g with hmdef
  have hevm : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
      =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun z => (z - z₀) ^ m * h z) := by
    refine hev.mono fun z hz => ?_
    simpa [smul_eq_mul] using hz
  obtain ⟨O₁, hO₁, hO₁open, hO₁mem⟩ := eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hevm)
  obtain ⟨O₂, hO₂, hO₂open, hO₂mem⟩ := eventually_nhds_iff.mp
    hh.eventually_analyticAt
  set W := O₁ ∩ O₂ with hW
  have hWopen : IsOpen W := hO₁open.inter hO₂open
  have hWmem : z₀ ∈ W := ⟨hO₁mem, hO₂mem⟩
  have hWp_open : IsOpen (W ∩ {z₀}ᶜ) := hWopen.inter isClosed_singleton.isOpen_compl
  have hfinal : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
      (m : ℂ) * h z + (z - z₀) * deriv h z = 0 := by
    have hWev : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∈ W ∩ {z₀}ᶜ := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [hWopen.eventually_mem hWmem] with y hy hyne
      exact ⟨hy, hyne⟩
    filter_upwards [h0, hWev] with z hz0 hzW
    have hzne : z ≠ z₀ := hzW.2
    have hloc : (fun y : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm y) g)
        =ᶠ[nhds z] (fun y => (y - z₀) ^ m * h y) :=
      (hWp_open.eventually_mem hzW).mono (fun y hy => hO₁ y hy.1.1 hy.2)
    have hzp : HasDerivAt (fun y : ℂ => (y - z₀) ^ m)
        ((m : ℂ) * (z - z₀) ^ (m - 1) * 1) z := by
      have h1 := hasDerivAt_zpow m (z - z₀) (Or.inl (sub_ne_zero.mpr hzne))
      have h2 := (hasDerivAt_id z).sub_const z₀
      simpa [Function.comp_def] using h1.comp z h2
    have hdz : HasDerivAt (fun y : ℂ => (y - z₀) ^ m * h y)
        ((m : ℂ) * (z - z₀) ^ (m - 1) * 1 * h z + (z - z₀) ^ m * deriv h z) z :=
      hzp.mul ((hO₂ z hzW.1.2).differentiableAt.hasDerivAt)
    have hder_eq : deriv (fun y : ℂ =>
        Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm y) g) z
        = (m : ℂ) * (z - z₀) ^ (m - 1) * 1 * h z + (z - z₀) ^ m * deriv h z := by
      rw [hloc.deriv_eq]
      exact hdz.deriv
    rw [hder_eq] at hz0
    have hfac : (m : ℂ) * (z - z₀) ^ (m - 1) * 1 * h z + (z - z₀) ^ m * deriv h z
        = (z - z₀) ^ (m - 1) * ((m : ℂ) * h z + (z - z₀) * deriv h z) := by
      have hsplit : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
        conv_lhs => rw [show m = (m - 1) + 1 by ring]
        rw [zpow_add_one₀ (sub_ne_zero.mpr hzne)]
      rw [hsplit]
      ring
    rw [hfac] at hz0
    exact (mul_eq_zero.mp hz0).resolve_left (zpow_ne_zero _ (sub_ne_zero.mpr hzne))
  set Φ : ℂ → ℂ := fun z => (m : ℂ) * h z + (z - z₀) * deriv h z with hΦ
  have hΦcont : ContinuousAt Φ z₀ := by
    apply ContinuousAt.add
    · exact continuousAt_const.mul hh.continuousAt
    · exact (continuousAt_id.sub continuousAt_const).mul hh.deriv.continuousAt
  have ht1 : Filter.Tendsto Φ (nhdsWithin z₀ {z₀}ᶜ) (nhds (Φ z₀)) :=
    hΦcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Filter.Tendsto Φ (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    rw [Filter.tendsto_congr' hfinal]
    exact tendsto_const_nhds
  have huniq := tendsto_nhds_unique ht1 ht2
  have hΦz₀ : Φ z₀ = (m : ℂ) * h z₀ := by
    rw [hΦ]
    simp
  rw [hΦz₀] at huniq
  rcases mul_eq_zero.mp huniq with hmz | hhz
  · exact hm_ne (by exact_mod_cast hmz)
  · exact hh0 hhz

end WithHF

end C0RegionG

end SectRegion4

section SectAssembly

p2m_open "AlgebraicCurve Topology Filter Polynomial AlgebraicCurve.Place"
open scoped Manifold ContDiff

namespace C0Assembly

variable {F : Type*} [Field F] [Algebra ℂ F]

theorem transcendental_adjoin_self {f : F}
    (htr : Transcendental ℂ f) :
    Transcendental ℂ (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
      ↥(IntermediateField.adjoin ℂ ({f} : Set F))) := by
  intro halg
  apply htr
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply
    (IntermediateField.val (IntermediateField.adjoin ℂ ({f} : Set F)))
    ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ p
  rw [hp, map_zero] at h2
  simpa using h2

theorem generator_adjoin (f : F) :
    ∀ y : ↥(IntermediateField.adjoin ℂ ({f} : Set F)), ∃ pn pd : ℂ[X],
      y = Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
            ↥(IntermediateField.adjoin ℂ ({f} : Set F))) pn
        / Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
            ↥(IntermediateField.adjoin ℂ ({f} : Set F))) pd := by
  intro y
  obtain ⟨pn, pd, h⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (y : F)).mp y.2
  refine ⟨pn, pd, ?_⟩
  have hc : ∀ p : ℂ[X],
      ((Polynomial.aeval
        (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
          ↥(IntermediateField.adjoin ℂ ({f} : Set F))) p : _) : F)
      = Polynomial.aeval f p := by
    intro p
    exact (Polynomial.aeval_algHom_apply
      (IntermediateField.val (IntermediateField.adjoin ℂ ({f} : Set F)))
      ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ p).symm
  apply Subtype.coe_injective
  push_cast [hc]
  exact h

theorem finiteDimensional_adjoin_gen (f : F) :
    FiniteDimensional
      (↥(IntermediateField.adjoin ℂ
        ({(⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
            ↥(IntermediateField.adjoin ℂ ({f} : Set F)))} :
          Set (↥(IntermediateField.adjoin ℂ ({f} : Set F))))))
      (↥(IntermediateField.adjoin ℂ ({f} : Set F))) := by
  classical
  set E₀ := ↥(IntermediateField.adjoin ℂ ({f} : Set F))
  set x₀ : E₀ := ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩
  have htop : IntermediateField.adjoin ℂ ({x₀} : Set E₀) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨pn, pd, hy⟩ := generator_adjoin f y
    have hx : x₀ ∈ IntermediateField.adjoin ℂ ({x₀} : Set E₀) :=
      IntermediateField.mem_adjoin_simple_self ℂ x₀
    have haev : ∀ p : Polynomial ℂ,
        Polynomial.aeval x₀ p ∈ IntermediateField.adjoin ℂ ({x₀} : Set E₀) := by
      intro p
      have h1 : Polynomial.aeval x₀ p ∈ Algebra.adjoin ℂ ({x₀} : Set E₀) :=
        Polynomial.aeval_mem_adjoin_singleton ℂ x₀
      exact (IntermediateField.algebra_adjoin_le_adjoin ℂ _) h1
    rw [hy]
    exact div_mem (haev pn) (haev pd)
  rw [htop]
  have hspan : Submodule.span (↥(⊤ : IntermediateField ℂ E₀)) ({(1 : E₀)} : Set E₀) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have : y = (⟨y, trivial⟩ : ↥(⊤ : IntermediateField ℂ E₀)) • (1 : E₀) := by
      simp [IntermediateField.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have : Module.Finite (↥(⊤ : IntermediateField ℂ E₀)) E₀ :=
    ⟨⟨{1}, by rw [Finset.coe_singleton]; exact hspan⟩⟩
  exact this

theorem isRational_adjoinField {f : F} (htr : Transcendental ℂ f)
    (u : Place ℂ (↥(IntermediateField.adjoin ℂ ({f} : Set F)))) : u.IsRational := by
  have htr₀ := transcendental_adjoin_self htr
  letI := (C0RegionT.towerHom htr₀).toAlgebra
  haveI := finiteDimensional_adjoin_gen f
  haveI := C0RegionT.finiteDimensional_towerHom htr₀
  haveI := C0RegionT.isScalarTower_towerHom htr₀
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed u

variable [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  [T2Space (Place ℂ F)]

theorem exists_oph
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational) {f : F} (htr : Transcendental ℂ f)
    (e : {P : Place ℂ F // f ∈ P.toValuationSubring})
    (hord : e.1.ord (f - algebraMap ℂ F (Place.evalAt e.1 f)) = 1) :
    ∃ φ : OpenPartialHomeomorph {P : Place ℂ F // f ∈ P.toValuationSubring} ℂ,
      e ∈ φ.source ∧
      ⇑φ = fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} => Place.evalAt P.1 f := by
  classical
  have hf0 : f ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  obtain ⟨d, hd0, hsd⟩ :=
    C0RegionB.exists_hasStrictDerivAt_read hF hrat e.1 htr e.2 hord
  have hopen : IsOpen {P : Place ℂ F | f ∈ P.toValuationSubring} :=
    C0RegionB.isOpen_setOf_mem_toValuationSubring hf0
  set SOp : TopologicalSpace.Opens (Place ℂ F) := ⟨_, hopen⟩ with hSOp
  have hne : Nonempty ↥SOp := ⟨⟨e.1, e.2⟩⟩
  set φ₁ : OpenPartialHomeomorph ↥SOp ℂ := (chartAt ℂ e.1).subtypeRestr hne with hφ₁
  set ψ₂ : OpenPartialHomeomorph ℂ ℂ :=
    (hsd.hasStrictFDerivAt_equiv hd0).toOpenPartialHomeomorph _ with hψ₂
  set ψ : OpenPartialHomeomorph ↥SOp ℂ := φ₁.trans ψ₂ with hψ

  have hchart : ∀ P : Place ℂ F, (chartAt ℂ e.1) P = extChartAt 𝓘(ℂ, ℂ) e.1 P := by
    intro P; simp [extChartAt]
  have hchartsymm : ∀ z : ℂ,
      (extChartAt 𝓘(ℂ, ℂ) e.1).symm z = (chartAt ℂ e.1).symm z := by
    intro z; simp [extChartAt]

  have hsrc₁ : ∀ P : ↥SOp, P ∈ ψ.source → (P : Place ℂ F) ∈ (chartAt ℂ e.1).source := by
    intro P hP
    have h1 : P ∈ φ₁.source := (OpenPartialHomeomorph.trans_source φ₁ ψ₂) ▸ hP |>.1
    rw [hφ₁] at h1
    simpa [OpenPartialHomeomorph.subtypeRestr_source] using h1
  have hagree : ∀ P : ↥SOp, P ∈ ψ.source →
      ψ P = Place.evalAt (P : Place ℂ F) f := by
    intro P hP
    have h1 : ψ P = ψ₂ (φ₁ P) := rfl
    have h2 : φ₁ P = (chartAt ℂ e.1) (P : Place ℂ F) := by
      rw [hφ₁]; simp [OpenPartialHomeomorph.subtypeRestr_coe]
    have h3 : ⇑ψ₂ = fun z : ℂ =>
        Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) e.1).symm z) f := by
      rw [hψ₂]; exact (hsd.hasStrictFDerivAt_equiv hd0).toOpenPartialHomeomorph_coe

    have h4 : (extChartAt 𝓘(ℂ, ℂ) e.1).symm ((chartAt ℂ e.1) (P : Place ℂ F))
        = (P : Place ℂ F) := by
      rw [hchartsymm]
      exact (chartAt ℂ e.1).left_inv (hsrc₁ P hP)
    rw [h1, h2, h3]
    simp only []
    rw [h4]

  refine ⟨⟨⟨⟨fun P : ↥SOp => Place.evalAt (P : Place ℂ F) f,
      ψ.invFun, ψ.source, ψ.target, ?_, ψ.map_target', ?_, ?_⟩,
      ?_, ψ.continuousOn_invFun⟩, ψ.open_source, ψ.open_target⟩, ?_, rfl⟩
  ·
    intro P hP
    show Place.evalAt (P : Place ℂ F) f ∈ ψ.target
    rw [show Place.evalAt (P : Place ℂ F) f = ψ P from (hagree P hP).symm]
    exact ψ.map_source' hP
  ·
    intro P hP
    show ψ.invFun (Place.evalAt (P : Place ℂ F) f) = P
    rw [show Place.evalAt (P : Place ℂ F) f = ψ P from (hagree P hP).symm]
    exact ψ.left_inv' hP
  ·
    intro t ht
    have h1 := ψ.map_target' ht
    show Place.evalAt ((ψ.invFun t : ↥SOp) : Place ℂ F) f = t
    rw [show Place.evalAt ((ψ.invFun t : ↥SOp) : Place ℂ F) f
        = ψ (ψ.invFun t) from (hagree _ h1).symm]
    exact ψ.right_inv' ht
  ·
    refine ψ.continuousOn_toFun.congr ?_
    intro P hP
    exact (hagree P hP).symm
  ·
    show e ∈ ψ.source
    have hmem₁ : e ∈ φ₁.source := by
      rw [hφ₁, OpenPartialHomeomorph.subtypeRestr_source]
      exact mem_chart_source ℂ e.1
    have himg : φ₁ e = (chartAt ℂ e.1) e.1 := by
      rw [hφ₁]; simp [OpenPartialHomeomorph.subtypeRestr_coe]
    have hmem₂ : (chartAt ℂ e.1) e.1 ∈ ψ₂.source := by
      have h5 : extChartAt 𝓘(ℂ, ℂ) e.1 e.1 ∈ ψ₂.source := by
        rw [hψ₂]
        exact (hsd.hasStrictFDerivAt_equiv hd0).mem_toOpenPartialHomeomorph_source
      rwa [← hchart] at h5
    rw [hψ, OpenPartialHomeomorph.trans_source]
    exact ⟨hmem₁, by rw [Set.mem_preimage, himg]; exact hmem₂⟩

end C0Assembly

end SectAssembly

section SectMain

open AlgebraicCurve Topology Filter
open scoped Manifold ContDiff

namespace C0Assembly

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  [T2Space (Place ℂ F)]

variable (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))

include hF in

theorem surjective_evalAt [CompactSpace (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hrat : ∀ P : Place ℂ F, P.IsRational) {f : F} (htr : Transcendental ℂ f) (t : ℂ) :
    ∃ w : Place ℂ F, f ∈ w.toValuationSubring ∧ Place.evalAt w f = t := by
  classical
  have hf0 : f ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  set Im : Set ℂ :=
    Set.range (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
      Place.evalAt P.1 f) with hIm

  have hclosed : IsClosed Im :=
    (C0RegionB.isClosedMap_evalAt_subtype hF htr).isClosed_range

  have hopen : IsOpen Im := by
    rw [isOpen_iff_mem_nhds]
    rintro t₀ ⟨P₀, hP₀⟩
    set w₀ := P₀.1
    set z₀ := extChartAt 𝓘(ℂ, ℂ) w₀ w₀ with hz₀

    have han : AnalyticAt ℂ
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z) f) z₀ :=
      AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w₀ P₀.2

    have hmemopen : IsOpen {P : Place ℂ F | f ∈ P.toValuationSubring} :=
      C0RegionB.isOpen_setOf_mem_toValuationSubring hf0
    have hcont : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) w₀).symm z₀ :=
      continuousAt_extChartAt_symm'' ((extChartAt 𝓘(ℂ, ℂ) w₀).map_source
        (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) w₀))
    have hev : ∀ᶠ z in nhds z₀,
        f ∈ ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).toValuationSubring := by
      have hwmem : (extChartAt 𝓘(ℂ, ℂ) w₀).symm z₀
          ∈ {P : Place ℂ F | f ∈ P.toValuationSubring} := by
        rw [hz₀, extChartAt_to_inv]; exact P₀.2
      exact hcont.eventually_mem (hmemopen.mem_nhds hwmem)

    rcases han.eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso

      have hg0 : f - algebraMap ℂ F t₀ ≠ 0 := fun h =>
        htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap t₀)
      obtain ⟨hmer, horder⟩ := hF _ hg0 w₀
      have hsub := C0RegionG.read_sub_eventuallyEq' w₀ w₀
        (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) w₀) hf0 P₀.2 hrat t₀
      have hval : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z₀) f = t₀ := by
        rw [hz₀, extChartAt_to_inv]
        exact hP₀
      have hzero : (fun z : ℂ =>
          Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z) (f - algebraMap ℂ F t₀))
          =ᶠ[nhds z₀] (fun _ => (0 : ℂ)) := by
        refine hsub.trans ?_
        filter_upwards [hconst] with z hz
        rw [hz, hval, sub_self]
      have htop : meromorphicOrderAt
          (fun z : ℂ =>
            Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z) (f - algebraMap ℂ F t₀))
          z₀ = ⊤ := by
        rw [meromorphicOrderAt_eq_top_iff]
        exact (hzero.filter_mono nhdsWithin_le_nhds).mono (fun z hz => hz)
      rw [← hz₀] at horder
      rw [horder] at htop
      exact (WithTop.coe_ne_top) htop
    ·
      have hval : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z₀) f = t₀ := by
        rw [hz₀, extChartAt_to_inv]
        exact hP₀
      have h1 : Im ∈ Filter.map
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z) f)
          (nhds z₀) := by
        rw [Filter.mem_map]
        filter_upwards [hev] with z hz
        exact ⟨⟨(extChartAt 𝓘(ℂ, ℂ) w₀).symm z, hz⟩, rfl⟩
      have h2 := hle h1
      rwa [hval] at h2

  have hnonempty : Im.Nonempty := by

    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf0
    have hpole : {P : Place ℂ F | f ∉ P.toValuationSubring} ⊆ ↑D.support := by
      intro P hP
      by_contra hPD
      refine hP (P.mem_of_ord_nonneg hf0 ?_)
      have hz : D P = 0 := by
        simpa [Finsupp.mem_support_iff, not_not] using hPD
      have := hD P
      omega
    have hinfinite : Infinite (Place ℂ F) := by
      by_contra hfin
      rw [not_infinite_iff_finite] at hfin

      have hP : Nonempty (Place ℂ F) := inferInstance
      obtain ⟨P⟩ := hP
      have hopen' : IsOpen (chartAt ℂ P).target := (chartAt ℂ P).open_target
      have hinf' : (chartAt ℂ P).target.Infinite := by
        have hmemt : (chartAt ℂ P).target ∈ nhds ((chartAt ℂ P) P) :=
          hopen'.mem_nhds ((chartAt ℂ P).map_source (mem_chart_source ℂ P))
        exact infinite_of_mem_nhds _ hmemt
      have hfin' : (chartAt ℂ P).target.Finite := by
        have : (chartAt ℂ P).target ⊆
            (chartAt ℂ P) '' (chartAt ℂ P).source := by
          rw [OpenPartialHomeomorph.image_source_eq_target]
        exact (Set.Finite.image _ (Set.toFinite _)).subset this
      exact hinf' hfin'
    have : {P : Place ℂ F | f ∉ P.toValuationSubring} ≠ Set.univ := by
      intro h
      have h1 : (Set.univ : Set (Place ℂ F)).Finite :=
        (D.support.finite_toSet.subset (h ▸ hpole))
      exact Set.infinite_univ h1
    obtain ⟨P, hP⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp this
    rw [Set.mem_setOf_eq, not_not] at hP
    exact ⟨Place.evalAt P f, ⟨⟨P, hP⟩, rfl⟩⟩

  have huniv : Im = Set.univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩) hnonempty
  have ht : t ∈ Im := huniv ▸ Set.mem_univ t
  obtain ⟨P, hP⟩ := ht
  exact ⟨P.1, P.2, hP⟩

end C0Assembly

end SectMain

section SectSolution

open AlgebraicCurve
open scoped Manifold ContDiff

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (f : F) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({f} : Set F)) F] :
    ∃ B : Finset ℂ,
      IsCoveringMapOn
        (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} => Place.evalAt P.1 f)
        ((↑B : Set ℂ)ᶜ) ∧
      ∀ t : ℂ, t ∉ B →
        Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ Place.evalAt P f = t} =
          Module.finrank (IntermediateField.adjoin ℂ ({f} : Set F)) F := by
  classical
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hrat : ∀ P : Place ℂ F, P.IsRational := fun P =>
    C0RegionT.isRational_of_tower hf P
  have hratE : ∀ u : Place ℂ (↥(IntermediateField.adjoin ℂ ({f} : Set F))),
      u.IsRational := fun u => C0Assembly.isRational_adjoinField hf u
  have hcritfin := C0RegionG.finite_critical hF hf hrat
  set B : Finset ℂ :=
    (hcritfin.image (fun w : Place ℂ F => Place.evalAt w f)).toFinset with hB

  have hord1 : ∀ t : ℂ, t ∉ B → ∀ w : Place ℂ F, f ∈ w.toValuationSubring →
      Place.evalAt w f = t → w.ord (f - algebraMap ℂ F t) = 1 := by
    intro t ht w hwm hwv
    have hnotcrit : ¬ (2 ≤ w.ord (f - algebraMap ℂ F (Place.evalAt w f))) := by
      intro h2
      refine ht ?_
      rw [hB, Set.Finite.mem_toFinset]
      exact ⟨w, ⟨hwm, h2⟩, hwv⟩
    rw [hwv] at hnotcrit
    have hgne : f - algebraMap ℂ F t ≠ 0 := fun h =>
      hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap t)
    have hmem : f - algebraMap ℂ F t ∈ w.toValuationSubring :=
      sub_mem hwm (w.algebraMap_mem' t)
    have hevz : w.evalAt (f - algebraMap ℂ F t) = 0 := by
      rw [C0RegionG.evalAt_sub_algebraMap w (hrat w) hwm, hwv, sub_self]
    have hpos := C0RegionG.ord_pos_of_evalAt_eq_zero w (hrat w) hgne hmem hevz
    omega
  refine ⟨B, ?_, ?_⟩
  ·
    refine (C0RegionB.isClosedMap_evalAt_subtype hF hf).isCoveringMapOn_of_openPartialHomeomorph
        ?_ ?_
    · intro t ht
      have hfin := C0RegionB.finite_setOf_evalAt_eq hrat hf t
      have hsub : ((fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
          Place.evalAt P.1 f) ⁻¹' {t})
          ⊆ Subtype.val ⁻¹' {P : Place ℂ F | f ∈ P.toValuationSubring
              ∧ Place.evalAt P f = t} := by
        intro P hP
        exact ⟨P.2, hP⟩
      exact (hfin.preimage Subtype.val_injective.injOn).subset hsub
    · intro e he
      have ht : Place.evalAt e.1 f ∉ B := he
      have hord := hord1 _ ht e.1 e.2 rfl
      obtain ⟨φ, hmem, hcoe⟩ := C0Assembly.exists_oph hF hrat hf e hord
      exact ⟨φ, hmem, hcoe.symm⟩
  ·
    intro t ht
    obtain ⟨w₀, h₀m, h₀v⟩ := C0Assembly.surjective_evalAt hF hrat hf t
    exact AlgebraicCurve.Place.card_fiber_eq_finrank_adjoin_of_ord_eq_one F hf hrat hratE t w₀ h₀m h₀v (hord1 t ht)

end SectSolution

end S_AlgebraicCurve_isCoveringMapOn_evalAt
end P2MW
export P2MW.S_AlgebraicCurve_isCoveringMapOn_evalAt (solution)
