-- Prove2me | Definitions.Def_OAIQ068A046
-- name    : OAIQ068A046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:35:01.42779+00:00
-- url     : https://prove2.me/theorems/ddf265b6-9482-4846-b91c-f74dfc5d661c
-- title:
--   Definitions bundle OAIQ068A046 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 26 definitions, 3 instances and 17 theorems. The definitions and types are `OAI.PiExponent.AdmissibleCurveModel.degreeData`, `OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplexIso`, `OAI.PiExponent.NumericalAmpleness.LowerClosedNumericalCriterion`, `OAI.PiExponent.NumericalAmpleness.eulerSlopeCoefficient`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial`, `OAI.PiExponent.NumericalAmpleness.mixedEuler`, `OAI.PiExponent.NumericalAmpleness.topEuler`, `OAI.PiExponent.ProjectiveCoefficientBound.EventualBound`, `OAI.PiExponent.ProjectiveCoefficientBound.HomogeneousPullbackBound`, `OAI.PiExponent.ProjectiveSectionInterface.pullback`, `OAI.PiExponent.ReesSectionInclusion.HasFrozenValues`, `OAI.PiExponent.ReesSectionInclusion.chartMap`, `OAI.PiExponent.ReesSheafCechBase.chartFrameTyped`, `OAI.PiExponent.ReesSheafCechBase.chartHomEquiv`, `OAI.PiExponent.ReesSheafCechBase.cochainAddCommGroup`, `OAI.PiExponent.ReesSheafCechBase.cochainEquiv`, `OAI.PiExponent.ReesSheafCechBase.genericChartHomEquiv`, `OAI.PiExponent.ReesSheafCechBase.tupleHomEquiv`, `OAI.PiExponent.ReesSheafCechNaturality.chartMap`, `OAI.PiExponent.ReesSheafCechRecovery.cochainAddCommGroup`, `OAI.PiExponent.ReesSheafCechRecovery.cyclesEquiv`, `OAI.PiExponent.ReesSheafCechRecovery.globalCyclesEquiv`, `OAI.PiExponent.ReesSheafCechRecovery.gradedCycles`, `OAI.PiExponent.ReesSheafCechRecovery.ordinaryAugmentation`, `OAI.PiExponent.ReesSheafCechRecovery.ordinaryGlobalSection`, `OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleCurveModelDegrees`, `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Ampleness_ExceptionalTypedTransportNaturality`, `PiExponent_Ampleness_ReesFixedFrames`, `PiExponent_Ampleness_ReesProductFrames`, `PiExponent_Ampleness_ReesSectionInclusion`, `PiExponent_Approximation_NumericalSlopeInduction`, `PiExponent_Cohomology_CartierEulerPair`, `PiExponent_Cohomology_MixedEulerSlope`, `PiExponent_Cohomology_MixedEulerTop`, `PiExponent_Cohomology_ReesSheafCechBase`, `PiExponent_Cohomology_ReesSheafCechNaturality`, `PiExponent_Cohomology_ReesSheafCechRecovery`, `PiExponent_Geometry_ProjectiveCoefficientBound`, `PiExponent_Geometry_ProjectiveSectionInterface`.
--
--   **Imports.** It imports the bundles `OAIQ068A043` and `OAIQ068A044` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_PiExponent_NumericalAmpleness_ample_slope_of_polynomial_pos_of_lower_criterion`, `OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_eval_nat_div`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_margin`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_pos_of_ample`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_isAmple_of_lower_numerical_criterion`, `OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68`, `OAI_PiExponent_NumericalAmpleness_topEuler_slopeBundle_eq`, `OAI.PiExponent.NumericalAmpleness.topEuler_slopeBundle_eq_q68`, `OAI_PiExponent_ReesSheafCechRecovery_eventually_recovery_and_cohomology`, `OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68`, `OAI_PiExponent_WeightedPullbackDegree_pullback_supportBound` and `OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68`; the proofs of `OAI_PiExponent_AdmissibleBlowupGeometry_uniform_curve_margin`, `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68`, `OAI_PiExponent_AdmissibleMatrixInterpolation_eventual_packets_of_eventual_jetRestriction`, `OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68`, `OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation_of_eventual_jetRestriction`, `OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction_q68`, `OAI_PiExponent_AffineReesCanonicalRecovery_eventually_comap_bijective`, `OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68`, `OAI_PiExponent_NumericalAmpleness_ample_slope_of_polynomial_pos_of_lower_criterion`, `OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_eval_nat_div`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_margin`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68`, `OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_pos_of_ample`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_euler_power_dimension_difference_eq_zero`, `OAI.PiExponent.NumericalAmpleness.euler_power_dimension_difference_eq_zero_q68`, `OAI_PiExponent_NumericalAmpleness_exists_nonzero_power_section_of_euler_growth`, `OAI.PiExponent.NumericalAmpleness.exists_nonzero_power_section_of_euler_growth_q68`, `OAI_PiExponent_NumericalAmpleness_isAmple_of_lower_numerical_criterion`, `OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68`, `OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample`, `OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_topEuler_slopeBundle_eq`, `OAI.PiExponent.NumericalAmpleness.topEuler_slopeBundle_eq_q68`, `OAI_PiExponent_ReesSheafCechRecovery_eventually_recovery_and_cohomology`, `OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68`, `OAI_PiExponent_WeightedPullbackDegree_pullback_supportBound`, `OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68` and `OAI.PiExponent.main`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A043
import Definitions.Def_OAIQ068A044

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem localIdeal_length_eq_logContact [X.IsSeparated]
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : Fin K) (hcenter : CurveCenters.Centered z (Fin.cases 1 (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸
        localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
          (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * PlaceCenteredBranch.logContact p z (c k) hcenter
        (CurveContactFamily.nonconstant z (c k) hz) v := by
  let a := PlaceCenteredBranch.lift p z (Fin.cases 1 (c k)) hcenter
  have ha : (Fin.cases (a 0) (fun i => a i.succ) : Fin (m+1) → PlaceValuationRing.ring p) = a := by
    funext i
    cases i using Fin.cases <;> rfl
  have hy := PlaceCenteredBranch.lift_residue p z (Fin.cases 1 (c k)) hcenter 0
  have hx := fun i : Fin m =>
    PlaceCenteredBranch.lift_residue p z (Fin.cases 1 (c k)) hcenter i.succ
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (c k) hcenter,
    localIdeal_compactIdeal]
  have hm := JetProductLocalization.map_polynomialIdeal_eq_selected
    c hc T e (a 0) (fun i => a i.succ) k hy hx
  rw [ha] at hm
  rw [hm]
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv (c k)
    (a 0) (fun i => a i.succ) hy hx
    (PlaceCenteredBranch.logLift_nonconstant p z (c k) hcenter
      (CurveContactFamily.nonconstant z (c k) hz)) T hT R e he

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated]
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = CompactLogJetIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal (CompactLogJetIdeal.compactIdeal c T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ CurveContactFamily.places hfinite z c hz,
        CurveContactFamily.contact hres hfinite z c hz v p := by
  classical
  let I := CompactLogJetIdeal.compactIdeal c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf c T e j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := CurveContactFamily.places hfinite z c hz
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((CompactLogJetIdeal.compactIdeal c T e j).support : Set X) at hmem
      rw [CompactLogJetIdeal.support_compactIdeal c T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : CompactLogJetIdeal.point (c k) a = CompactJetPolynomial.centerPoint (c k) := by
        have h := Set.mem_range_self (f := CompactLogJetIdeal.point (c k)) a
        rw [CompactLogJetIdeal.range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (CompactJetPolynomial.centerPoint (c k)) := by
        exact ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (CurveContactFamily.mem_places hfinite z c hz p).mpr
        ⟨k, JetCenterIdentification.centered_of_closedPoint_eq p z (c k) j _ hfield hclosed⟩
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * CurveContactFamily.contact hres hfinite z c hz v p := by
    let := hres p
    have hp' : p ∈ CurveContactFamily.places hfinite z c hz := hp
    let k := CurveContactFamily.center hfinite z c hz p hp
    have hcenter := CurveContactFamily.centered hfinite z c hz p hp
    have h := localIdeal_length_eq_logContact f hf c hc T e v hv R he hT j (g ≫ π)
      z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [CurveContactFamily.contact, dite_eq_left hp', I, k] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, CurveContactFamily.contact hres hfinite z c hz v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

end Curve

theorem admissible_degree_eq_neg_contactSum
    {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ AdmissibleBlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      AdmissibleBlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        AdmissibleBlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((AdmissibleBlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
        BlowupCurveMargin.contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  have hc : Function.Injective d.curveCenters := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)
  have h := compactIdeal_degree_eq_neg_contact_sum f hf d.curveCenters hc
    (AdmissibleBlowupGeometry.logCutoff d) (AdmissibleBlowupGeometry.scale d).jetPowers
    (AdmissibleBlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (AdmissibleBlowupGeometry.scale d).radius (AdmissibleBlowupGeometry.scale d).jetPowers_eq
    (AdmissibleBlowupGeometry.logCutoff_strict d) (AdmissibleBlowupGeometry.affineChart d)
    (AdmissibleBlowupGeometry.compactificationStructureMap d)
    (AdmissibleBlowupGeometry.affineChart_over d)
    (AdmissibleBlowupGeometry.projection d) (AdmissibleBlowupGeometry.J d)
    (AdmissibleBlowupGeometry.exceptionalInclusion d)
    (AdmissibleBlowupGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ)
  exact_mod_cast h

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleCurveModelDegrees
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveModel
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def degreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (r : ModelData d C) : AdmissibleBlowupMargin.AffineCurveDegreeData d C := by
  letI := r.field
  letI := r.algebra
  letI := r.essFiniteType
  letI := r.parameterFinite
  letI := r.normalizationFinite
  letI := r.chartIso
  let y := r.coordinates 0
  let x := fun i : Fin d.m => r.coordinates i.succ
  have htuple : (Fin.cases y x : Fin (d.m+1) → r.E) = r.coordinates := by
    funext i
    cases i using Fin.cases <;> rfl
  have hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → r.E)) = ⊤ := by
    rw [htuple]
    exact r.coordinates_generate
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
  have hA : (NumericalAmpleness.curveDegree (structureMap d) (A d) C : ℝ) =
      ((scale d).radius : ℝ) * BlowupCurveMargin.poleDegree d y x r.trdeg_one := by
    change _ = ((scale d).radius : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases y x) d.curveDegreeWeights
    rw [htuple]
    exact CurveNormalizedDegreeTransfer.weighted_curveDegree
      (exponents d) r.coordinates (constantIndex d)
      ((scale d).exponents_constant d.curveDegreeWeights_pos)
      (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty
      (projection d) r.generic_coordinates d.curveDegreeWeights d.curveDegreeWeights_pos
      (by exact_mod_cast (scale d).radius_pos) (scale d).degreePowers
      (scale d).degreePowers_eq (pureIndex d)
      ((scale d).exponents_pure d.curveDegreeWeights_pos)
      ((scale d).budget d.curveDegreeWeights_pos) hfinite
  have hgeneric : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
      (r.normalization ≫ C.embedding) ≫ projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        affineChart d := by
    have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
      apply RingHom.ext
      intro P
      exact MvPolynomial.aeval_def r.coordinates P
    rw [htuple, heval]
    simpa only [Category.assoc, CurveMonomialMap.genericMonomialMap, affineChart] using
      r.generic_coordinates
  have hJ : (NumericalAmpleness.curveDegree (structureMap d) (J d) C : ℝ) =
      -((scale d).radius : ℝ) * BlowupCurveMargin.contactSum d y x hgen r.trdeg_one := by
    have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty (J d)
    have hn := ExceptionalCurveDegree.admissible_degree_eq_neg_contactSum
      d y x hgen r.trdeg_one r.parameter r.parameter_transcendental
      (r.normalization ≫ C.embedding) hgeneric
    exact (congrArg (fun n : ℤ => (n : ℝ)) hd).trans hn
  exact { E := r.E
          field := r.field
          algebra := r.algebra
          essFiniteType := r.essFiniteType
          y := y
          x := x
          coordinates_generate := hgen
          trdeg_one := r.trdeg_one
          hyperplane_degree := hA
          exceptional_degree := hJ }

end PiExponent.AdmissibleCurveModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalTypedTransportNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (hchart : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

theorem transportSections_restrict (L : LineBundle Y) (n : ℕ)
    {U V : Y.Opens} (hU : j.opensRange = U) (hV : j'.opensRange = V)
    (hVU : V ≤ U) (b : freeOpen Y.ringCatSheaf U ⟶ (L.pow n).sheaf) :
    transportSections j' L n hV (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b) =
      restrictSections j j' θ hchart L n (transportSections j L n hU b) := by
  subst U V
  simp [transportSections, restrictSections, freeOpenMap]
  change (𝟙 _ ≫ (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b)) =
    freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ (𝟙 _ ≫ b)
  exact (Category.id_comp _).trans
    (congrArg (fun c => freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ c)
      (Category.id_comp b).symm)

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)
variable {p : J} (hp : p ∈ s)
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.idealChartFrame

include hp in

theorem chartFrame_nonempty :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme) := by
  rw [exceptionalLineBundle_sheaf_eq]
  exact ⟨ExceptionalAffineChart.idealChartFrame (Y := affineBlowup I) (chartMorphism I a hs) (exceptionalIdeal I)
    (chartEquation I a (s := s) (p := p))
    (exceptional_chart I a hs hp) (chartEquation_regular I a hp)⟩

end PiExponent.ReesProductPowerSections
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem frame_nonempty_congr {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U = V)
    (he : Nonempty (M.restrict U.ι ≅ PiExponentSeshadri.Frames.O U.toScheme)) :
    Nonempty (M.restrict V.ι ≅ PiExponentSeshadri.Frames.O V.toScheme) := by
  subst V
  exact he

theorem chartFrame_nonempty {p : J} (hp : p ∈ s) :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme) :=
  frame_nonempty_congr (exceptionalLineBundle I).sheaf (chartOpen_eq I a hs).symm
    (ReesProductPowerSections.chartFrame_nonempty I a hs hp)

end
end PiExponent.ReesFrozenChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

attribute [local instance] OAI.PiExponent.ReesSheafCechBase.frozenChartOpenImmersion
def genericChartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s)
    (L : PiExponentSeshadri.Geometry.LineBundle (affineBlowup I))
    (ι : L.sheaf ⟶ PiExponentSeshadri.Frames.O (affineBlowup I))
    (hL : PiExponentSeshadri.Geometry.PresentsPullbackIdeal
      (PiExponentSeshadri.IdealPullback.specIdeal I) (projection I) L ι)
    (e : ExceptionalRepresentedTypes.Frame (chartMap I a hs) L)
    (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs) L n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  (ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
    (chartMap I a hs)
    (ReesFrozenChart.base I a s)
    (ReesFrozenChart.chart_projection I a hs) L ι hL e n).trans
      (ReesFrozenPower.pieceEquiv I a hp n).symm

attribute [local irreducible] genericChartHomEquiv

theorem chartFrameTyped_nonempty {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) :
    Nonempty (ExceptionalRepresentedTypes.Frame (chartMap I a hs)
      (exceptionalLineBundle I)) := by
  exact ExceptionalRepresentedTypes.frame_nonempty_of_open
    (chartMap I a hs) (exceptionalLineBundle I)
    (U := (ReesFrozenChart.chartOpen I a hs).1) rfl
    (ReesFrozenChart.chartFrame_nonempty I a hs hp)

def chartFrameTyped {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) :
    ExceptionalRepresentedTypes.Frame (chartMap I a hs) (exceptionalLineBundle I) :=
  (chartFrameTyped_nonempty I a hs hp).some

def chartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  genericChartHomEquiv I a hs hp (exceptionalLineBundle I) (exceptionalInclusion I)
    (exceptional_presents I) (chartFrameTyped I a hs hp) n

theorem chartHomEquiv_pieceEquiv {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n) :
    ReesFrozenPower.pieceEquiv I a hp n (chartHomEquiv I a hs hp n b) =
      ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
        (chartMap I a hs)
        (ReesFrozenChart.base I a s)
        (ReesFrozenChart.chart_projection I a hs)
        (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)
        (chartFrameTyped I a hs hp) n b := by
  unfold chartHomEquiv genericChartHomEquiv
  exact (ReesFrozenPower.pieceEquiv I a hp n).apply_symm_apply _

def tupleHomEquiv (n q : ℕ) (t : Fin (q + 1) → J) :
    (schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n) ≃+ ReesLocalizedIntersections.Piece I a (tupleSet t) n :=
  (ExceptionalRepresentedTypes.transportSections
    (chartMap I a (tuple_nonempty q t)) (exceptionalLineBundle I) n
    (tupleOpen_eq I a q t)).trans
      (chartHomEquiv I a (tuple_nonempty q t) (tuple_mem q t 0) n)

local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def cochainEquiv (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  letI (t : Fin (q + 1) → J) : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact AddEquiv.piCongrRight (fun t => tupleHomEquiv I a n q t)

omit [Fintype J] [DecidableEq J] in

theorem iSup_opens (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    (⨆ j, opens I a j) = ⊤ := ReesFiniteCover.iSup_generator_opensRange I a ha

end
end PiExponent.ReesSheafCechBase

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesSectionInclusion
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSectionInclusion
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance chartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

def HasFrozenValues (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) (r : R) : Prop :=
  ∀ t : Fin 1 → J,
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top) u t))).val =
      ReesFrozenChart.base I a (tupleSet t) r

end
end PiExponent.ReesSectionInclusion

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerPair
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

namespace CartierEulerPair

def rightComplexIso (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    rightComplex p L B M t n ≅ tensorSectionComplex p B (source L M (n+1)) t :=
  ShortComplex.isoMk (Iso.refl _) (middleIso L B M n) (Iso.refl _)
    (by simpa only [rightComplex] using!
      iso_middle_comm (tensorSectionComplex p B (source L M (n+1)) t).f (middleIso L B M n))
    (by simpa only [rightComplex] using!
      (Category.comp_id ((middleIso L B M n).hom ≫
        (tensorSectionComplex p B (source L M (n+1)) t).g)).symm)

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NumericalSlopeInduction
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def LowerClosedNumericalCriterion (p : X ⟶ Spec (CommRingCat.of ℂ))
    (H : LineBundle X) (d : ℕ) : Prop :=
  ∀ (I : X.IdealSheafData), topologicalKrullDim I.subscheme ≤ d →
    ∀ (M : LineBundle I.subscheme) (δ : ℝ), 0 < δ →
      (∀ C : IntegralCurve I.subscheme,
        δ * (curveDegree (I.subschemeι ≫ p) (H.pullback I.subschemeι) C : ℝ) ≤
          (curveDegree (I.subschemeι ≫ p) M C : ℝ)) → M.IsAmple

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerTop
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def topEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ) (L : LineBundle X) : ℤ :=
  (fwdDiff (1 : ℕ))^[d] (fun n => eulerCharacteristic p d (L.pow n).sheaf) 0

def mixedEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (ls : List (LineBundle X)) : ℤ := mixedTop (lineEuler p d) ls

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerSlope
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def eulerSlopeCoefficient (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) : ℝ :=
  mixedEuler p d (List.replicate k H ++ List.replicate (d-k) L)

def eulerSlopePolynomial (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) : Polynomial ℝ :=
  mixedSlopePolynomial d (eulerSlopeCoefficient p d L H)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechNaturality
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
open PiExponent.ReesSheafCechBase PiExponent.ReesFrozenChart
open PiExponent.ReesFrozenPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections
  PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ExceptionalRepresentedTypes.restrictSections
  PiExponent.ExceptionalRepresentedTypes.transportSections
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (coordinateRing I a s)) ⟶ affineBlowup I :=
  chart I a hs

local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

theorem chartHomEquiv_restrict {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty)
    {p r : J} (hp : p ∈ s) (hr : r ∈ t) (hst : s ⊆ t) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs) (exceptionalLineBundle I) n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartHomEquiv I a ht hr n
      (ExceptionalRepresentedTypes.restrictSections (chartMap I a hs) (chartMap I a ht)
        (restriction I a hst) (restriction_chart I a hs ht hst)
        (exceptionalLineBundle I) n b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem hst n (chartHomEquiv I a hs hp n b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (pieceEquiv I a hr n).injective
  apply Subtype.ext
  rw [chartHomEquiv_pieceEquiv, pieceEquiv_restriction I a hp hr hst n,
    chartHomEquiv_pieceEquiv]
  exact ExceptionalRepresentedTypes.representedSectionsTyped_restrict
    (chartMap I a hs) (chartMap I a ht) (restriction I a hst)
    (restriction_chart I a hs ht hst) I (projection I)
    (base I a s) (chart_projection I a hs) (exceptionalLineBundle I)
    (exceptionalInclusion I) (exceptional_presents I) (chartFrameTyped I a hs hp)
    (base I a t) (chart_projection I a ht) (chartFrameTyped I a ht hr) n b

theorem tupleHomEquiv_restrict (n q : ℕ) (t : Fin (q + 2) → J) (k : Fin (q + 2))
    (b : schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) (t ∘ k.succAbove)) ⟶ exceptionalPower I n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    tupleHomEquiv I a n (q+1) t
      (CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
        (tupleHomEquiv I a n q (t ∘ k.succAbove) b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change chartHomEquiv I a _ _ n
    (ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty (q+1) t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a (q+1) t)
      (freeOpenMap _ (homOfLE (CechHigher.faceLE (opens I a) t k)) ≫ b)) = _
  rw [ExceptionalRepresentedTypes.transportSections_restrict
    (chartMap I a (tuple_nonempty q (t ∘ k.succAbove)))
    (chartMap I a (tuple_nonempty (q+1) t))
    (restriction I a (tupleSet_comp_subset t k.succAbove))
    (restriction_chart I a (tuple_nonempty q (t ∘ k.succAbove))
      (tuple_nonempty (q+1) t) (tupleSet_comp_subset t k.succAbove))
    (exceptionalLineBundle I) n
    (tupleOpen_eq I a q (t ∘ k.succAbove)) (tupleOpen_eq I a (q+1) t)
    (CechHigher.faceLE (opens I a) t k) b]
  exact chartHomEquiv_restrict I a (tuple_nonempty q (t ∘ k.succAbove))
    (tuple_nonempty (q+1) t) (tuple_mem q (t ∘ k.succAbove) 0)
    (tuple_mem (q+1) t 0) (tupleSet_comp_subset t k.succAbove) n _

theorem cochainEquiv_differential (n q : ℕ)
    (c : CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    cochainEquiv I a n (q+1) (CechHigher.differential _ (opens I a) (exceptionalPower I n) c) =
      GradedCech.differential (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (cochainEquiv I a n q c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  funext t
  let : AddCommGroup (ReesLocalizedIntersections.Piece I a (tupleSet t) n) :=
    AddSubgroup.toAddCommGroup _
  let : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  change tupleHomEquiv I a n (q+1) t
    (∑ k : Fin (q+2), (-1 : ℤ)^k.val •
      CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) (c (t ∘ k.succAbove))) = _
  exact AddEquivSignedSum.map_signed_sum_eq
    (A := (schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) t) ⟶ exceptionalPower I n))
    (B := ReesLocalizedIntersections.Piece I a (tupleSet t) n)
    (tupleHomEquiv I a n (q+1) t) q
    (fun k => CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k)
      (c (t ∘ k.succAbove)))
    (fun k => GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
      (tupleHomEquiv I a n q (t ∘ k.succAbove) (c (t ∘ k.succAbove))))
    (fun k => tupleHomEquiv_restrict I a n q t k (c (t ∘ k.succAbove)))

end
end PiExponent.ReesSheafCechNaturality

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def gradedCycles (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    AddSubgroup (GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n q).ker

instance gradedCyclesGroup (n q : ℕ) : AddCommGroup (gradedCycles I a n q) :=
  AddSubgroup.toAddCommGroup _

instance (priority := 2000) gradedCyclesAddZero (n q : ℕ) : AddZero (gradedCycles I a n q) :=
  groupAddZero (gradedCyclesGroup I a n q)

instance (priority := 2000) gradedCyclesAddZeroClass (n q : ℕ) :
    AddZeroClass (gradedCycles I a n q) :=
  groupAddZeroClass (gradedCyclesGroup I a n q)

def cyclesEquiv (n q : ℕ) :
    CechZeroAdditive.cycles (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      gradedCycles I a n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact AdditiveKernelTransport.kernelEquiv
    (cochainEquiv I a n q) (cochainEquiv I a n (q+1))
    (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
      (opens I a) (exceptionalPower I n) q)
    (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q)
    (fun c => cochainEquiv_differential I a n q c)

def ordinaryAugmentation (n : ℕ) : ↥(I^n : Ideal R) →+ gradedCycles I a n 0 := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ((GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n).comp (ordinaryPowerEquivIntegerPiece I n).toAddMonoidHom).codRestrict
    (gradedCycles I a n 0) (fun b =>
      GradedCech.differential_augmentation _ _ _ _ _ _)

def globalCyclesEquiv (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) ≃+
      gradedCycles I a n 0 := by
  letI : AddCommGroup (freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact (CechZeroAdditive.sectionsEquiv (affineBlowup I).ringCatSheaf (opens I a)
    (exceptionalPower I n) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])).trans
      (cyclesEquiv I a n 0)

def ordinarySectionHom (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) :=
  (globalCyclesEquiv I a ha n).symm.toAddMonoidHom.comp (ordinaryAugmentation I a n)

def ordinaryGlobalSection (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ Γ(exceptionalPower I n, ⊤) :=
  (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).toAddMonoidHom.comp
    (ordinarySectionHom I a ha n)

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionInterface
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSectionInterface
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetCoefficientInterface

variable {X Y : Scheme.{0}}

@[simp]
theorem ofSectionHom_sectionHom (L : LineBundle X) (n : ℕ) (s : Sections L n) :
    ofSectionHom L n (sectionHom L n s) = s := rfl

def pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    Sections L n → Sections (L.pullback f) n := fun s =>
  ofSectionHom (L.pullback f) n (pullbackPowerSection L f n (sectionHom L n s))

@[simp]
theorem sectionHom_pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : Sections L n) :
    sectionHom (L.pullback f) n (pullback L f n s) =
      pullbackPowerSection L f n (sectionHom L n s) := rfl

attribute [local irreducible] AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections

end
end PiExponent.ProjectiveSectionInterface

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoefficientBound
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveCoefficientBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.AffineJetCoefficientInterface PiExponent.WeightedSliceDegree

def EventualBound {X : Scheme} {K ι : Type} [Field K]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (L : LineBundle X) (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ e : Frame φ L, ∀ s : Sections L n,
    SupportBound ρ ((n : ℝ) * B) (AffineJetCoefficientInterface.coefficient φ L n e s)

variable {X : Scheme.{0}} {K ι σ : Type} [Field K] [Fintype σ] [Nonempty σ]

def HomogeneousPullbackBound
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∀ n, ∀ e : Frame φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f),
    ∀ t : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n,
    ∀ p : MvPolynomial.homogeneousSubmodule σ K n,
    (∀ z, dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n t)) →
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient φ
        ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ)) f n t))

end PiExponent.ProjectiveCoefficientBound
end

end OAI
end


