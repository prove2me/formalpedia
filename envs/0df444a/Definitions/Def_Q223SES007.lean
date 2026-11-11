-- Prove2me | Definitions.Def_Q223SES007
-- name    : Q223SES007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:57:40.539217+00:00
-- url     : https://prove2.me/theorems/45401d64-a713-478b-8aea-ec2f771b99b7
-- title:
--   Definitions bundle Q223SES007 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 53 definitions, 3 instances and 40 theorems. The definitions and types are `OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles`, `OAI.MaximalSeshadri.Geometry.BaseSections.tripleBaseCohomologyTwo`, `OAI.MaximalSeshadri.Geometry.BaseSections.twoBaseCohomologyOne`, `OAI.MaximalSeshadri.Geometry.IsBlowup.complementLift`, `OAI.MaximalSeshadri.Geometry.LineBundle.tensor`, `OAI.MaximalSeshadri.Geometry.affineCoefficient`, `OAI.MaximalSeshadri.Geometry.affineCoefficientLinear`, `OAI.MaximalSeshadri.Geometry.affineMapCoefficient`, `OAI.MaximalSeshadri.Geometry.affine_section_quotient`, `OAI.MaximalSeshadri.Geometry.finiteTensor`, `OAI.MaximalSeshadri.Geometry.finiteTensorFrame`, `OAI.MaximalSeshadri.Geometry.finiteTensorInclusion`, `OAI.MaximalSeshadri.Geometry.frameOnSmaller`, `OAI.MaximalSeshadri.Geometry.globalPlaneIntersection`, `OAI.MaximalSeshadri.Geometry.idealPowerFrame`, `OAI.MaximalSeshadri.Geometry.idealPowerInclusion`, `OAI.MaximalSeshadri.Geometry.lineTensorInterchange`, `OAI.MaximalSeshadri.Geometry.lineTensorPower`, `OAI.MaximalSeshadri.Geometry.lineTwistPower`, `OAI.MaximalSeshadri.Geometry.mixedEuler`, `OAI.MaximalSeshadri.Geometry.openSectionExt`, `OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap`, `OAI.MaximalSeshadri.Geometry.pullbackSectionLinear`, `OAI.MaximalSeshadri.Geometry.restrictCokernelIso`, `OAI.MaximalSeshadri.Geometry.sectionPostcompose`, `OAI.MaximalSeshadri.Geometry.sectionQuotientLocalComplex`, `OAI.MaximalSeshadri.Geometry.sectionQuotientLocalMap`, `OAI.MaximalSeshadri.Geometry.tensorCokernelComplexEquiv`, `OAI.MaximalSeshadri.Geometry.tensorCokernelGlobalEquiv`, `OAI.MaximalSeshadri.Geometry.tensorCokernelLocalIso`, `OAI.MaximalSeshadri.Geometry.tensorFrame`, `OAI.MaximalSeshadri.Geometry.tensorInclusion`, `OAI.MaximalSeshadri.Geometry.tensorUnitTwist`, `OAI.MaximalSeshadri.Geometry.tripleCohomologyTwo`, `OAI.MaximalSeshadri.Geometry.tripleCokernelBoundary`, `OAI.MaximalSeshadri.Geometry.tripleHomExtEquiv`, `OAI.MaximalSeshadri.Geometry.tripleSectionBoundary`, `OAI.MaximalSeshadri.Geometry.tripleTopHomCohomologyOne`, `OAI.MaximalSeshadri.Geometry.tripleTopHomExtEquiv`, `OAI.MaximalSeshadri.Geometry.twistIdealPowerIso` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: `Seshadri_Blowup_BlowupIntegral`, `Seshadri_Blowup_BlowupSectionDimensions`, `Seshadri_Blowup_OrderContraction`, `Seshadri_Blowup_PointSmoothness`, `Seshadri_Cohomology_BaseCech`, `Seshadri_Cohomology_CurveCech`, `Seshadri_Cohomology_PlaneRelationCycles`, `Seshadri_Cohomology_PlaneVertex`, `Seshadri_Cohomology_SurfaceBaseCech`, `Seshadri_Cohomology_SurfaceCech`, `Seshadri_Cohomology_SurfaceH0Finite`, `Seshadri_Cohomology_SurfaceH1Finite`, `Seshadri_Cohomology_TripleComplex`, `Seshadri_Cohomology_TripleExt`, `Seshadri_Cohomology_TripleFree`, `Seshadri_Cohomology_TripleTopExt`, `Seshadri_Divisors_AffineSectionQuotient`, `Seshadri_Divisors_CartierSection`, `Seshadri_Divisors_CenteredSections`, `Seshadri_Divisors_IdealSectionLifting`, `Seshadri_Divisors_SectionCoefficientOrder`, `Seshadri_Divisors_SectionCokernel`, `Seshadri_Divisors_SectionGermSystem`, `Seshadri_Geometry_FiniteSupportTwist`, `Seshadri_Intersection_CurveDegreeAdditivity`, `Seshadri_Intersection_IdealProductDegree`, `Seshadri_Intersection_LocalSectionDegree`, `Seshadri_Intersection_SurfaceTwistEuler`, `Seshadri_Jets_CenteredJetChart`, `Seshadri_LocalAlgebra_PowerIdeal`, `Seshadri_LocalAlgebra_TwistedIdealPower`, `Seshadri_Projective_FramedMaps`, `Seshadri_Projective_PullbackProjective`, `Seshadri_Projective_QuarticSubsystem`, `Seshadri_Projective_SectionMaps`, `Seshadri_Sheaves_AffineOrderRestriction`, `Seshadri_Sheaves_FramedPullback`, `Seshadri_Sheaves_PullbackSectionLinear`, `Seshadri_Sheaves_TensorCurveEuler`, `Seshadri_Sheaves_TensorDivision`, `Seshadri_Sheaves_TensorInclusion`, `Seshadri_Sheaves_TensorPowerDistribution`.
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`; the bundles `Q223SES004` and `Q223SES005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q223SES009`; the statements `OAI_MaximalSeshadri_Geometry_BaseSections_plane_boundaries_lift`, `OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01`, `OAI_MaximalSeshadri_Geometry_BaseSections_relationCycles_edge1`, `OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge1_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_residual_order`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order_s01`, `OAI_MaximalSeshadri_Geometry_IsBlowup_ample_exceptional_twist`, `OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist_s01`, `OAI_MaximalSeshadri_Geometry_IsBlowup_eventual_ample_power_twist`, `OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension_s01`, `OAI_MaximalSeshadri_Geometry_PointBlowup_effective_twist_bound`, `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_exceptional_square_squeeze`, `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01`, `OAI_MaximalSeshadri_Geometry_Surface_blowup_intersections`, `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01`, `OAI_MaximalSeshadri_Geometry_Surface_effective_mixed_nonneg`, `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventual_etale_affine_section_test`, `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_arbitrary_jet_frames`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_jets`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI_MaximalSeshadri_Geometry_Surface_exists_all_section_quadrilateral_etale`, `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01`, `OAI_MaximalSeshadri_Geometry_Surface_positive_square_eventually_effective`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_general`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01`, `OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_pow`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01`, `OAI_MaximalSeshadri_Geometry_curveDegree_tensor`, `OAI.MaximalSeshadri.Geometry.curveDegree_tensor_s01`, `OAI_MaximalSeshadri_Geometry_curve_lower_of_homogeneous_section_test`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_left_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_left_general_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general_s01`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_left_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_left_general_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_right_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_right_general_s01`, `OAI_MaximalSeshadri_Geometry_section_bound_of_curve_bound`, `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01`, `OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01` and `OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed_s01`; the proofs of `OAI_MaximalSeshadri_FinitePointBlowup_finite_point_power_contraction`, `OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01`, `OAI.MaximalSeshadri.FinitePointBlowup.smooth_finite_point_blowup_s01`, `OAI_MaximalSeshadri_Geometry_BaseSections_plane_boundaries_lift`, `OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01`, `OAI_MaximalSeshadri_Geometry_BaseSections_relationCycles_edge1`, `OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge1_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_residual_order`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio_s01`, `OAI_MaximalSeshadri_Geometry_PointBlowup_total_ideal_degree`, `OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01`, `OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso_s01`, `OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01`, `OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_left_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_left_general_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_left_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_left_general_s01`, `OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01` and `OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed_s01`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES004
import Definitions.Def_Q223SES005

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
end OAIVecTail
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PointSmoothness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.isIso_over_complement (hπ : IsBlowup I π) :
    IsIso (pullback.fst (Scheme.Opens.ι (X := X) I.support.compl) π) := by
  apply (hπ.open_baseChange (Scheme.Opens.ι (X := X) I.support.compl)).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end
end MaximalSeshadri.Geometry


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

def IsBlowup.complementLift (hπ : IsBlowup I π) : (centreComplement I).toScheme ⟶ B := by
  let := hπ.isIso_over_complement
  exact inv (pullback.fst (centreComplement I).ι π) ≫
    pullback.snd (centreComplement I).ι π

@[reassoc (attr := simp)]
lemma IsBlowup.complementLift_comp (hπ : IsBlowup I π) :
    hπ.complementLift ≫ π = (centreComplement I).ι := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

instance instIsOpenImmersionComplementLift (hπ : IsBlowup I π) : IsOpenImmersion hπ.complementLift := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  infer_instance

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_OrderContraction
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading TensorProduct
variable (K : Type) [Field K]

def exceptionalChartIdeal (i : Fin 2) : Ideal (chart (originIdeal K) (coordinate K i)) :=
  Ideal.span {chartBase (originIdeal K) (coordinate K i) (X i)}

end
end MaximalSeshadri.PlaneBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def atlasOfFramedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (𝒰 : X.OpenCover)
    (e : ∀ i, M.restrict (𝒰.f i) ≅ O (𝒰.X i)) (index : 𝒰.I₀ → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (𝒰.f i) (s (index i))) = 1) :
    CoordinateAtlas (K := K) (σ := σ) X where
  cover := 𝒰
  scalars i := (𝒰.f i).appTop.hom.comp k
  coordinates i q := coefficient (e i) (restrictSection (𝒰.f i) (s q))
  index := index
  normalized := hnorm
  scalarOverlap i j := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun f : pullback (𝒰.f i) (𝒰.f j) ⟶ X => f.appTop.hom)
        (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))
  coordinateOverlap i j := by
    obtain ⟨c, hc⟩ := overlap_coefficients (𝒰.f i) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) (e i) (e j)
    exact ⟨c, fun q => hc (s q)⟩

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque

variable {X : Scheme.{0}}

local instance curveCechFreeHomGroup_rf0a496_1 (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _
local instance curveCechFreeHomModule_rf0a496_1 (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _
lemma twoChartImage_eq (M : X.Modules) (U V : X.Opens) :
    (LinearMap.range (Linear.leftComp (C := X.Modules)
      (X := FiniteCoverCohomology.freeOpenModule (U ⊓ V))
      (Y := FiniteCoverCohomology.freeOpenModule U ⊞
        FiniteCoverCohomology.freeOpenModule V) Γ(X,⊤) M
      (ModuleMayerVietoris.shortComplex (X := X.carrier) X.ringCatSheaf U V).f)).map
      (freeOpenLinearEquiv M (U ⊓ V)).toLinearMap = twoChartImage M U V := by
  let P := twoChartImage M U V
  let leftMap : FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶
      FiniteCoverCohomology.freeOpenModule U :=
    freeOpenMap X.ringCatSheaf (homOfLE inf_le_left)
  let rightMap : FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶
      FiniteCoverCohomology.freeOpenModule V :=
    freeOpenMap X.ringCatSheaf (homOfLE inf_le_right)
  let sectionEquiv : (FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶ M) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ V) := freeOpenLinearEquiv M (U ⊓ V)
  have leftNaturality (morphism : FiniteCoverCohomology.freeOpenModule U ⟶ M) :
      sectionEquiv (leftMap ≫ morphism) =
        openRestriction M inf_le_left (freeOpenLinearEquiv M U morphism) :=
    freeOpenLinearEquiv_naturality M inf_le_left morphism
  have rightNaturality (morphism : FiniteCoverCohomology.freeOpenModule V ⟶ M) :
      sectionEquiv (rightMap ≫ morphism) =
        openRestriction M inf_le_right (freeOpenLinearEquiv M V morphism) :=
    freeOpenLinearEquiv_naturality M inf_le_right morphism
  apply le_antisymm
  · rintro x ⟨f,⟨g,rfl⟩,rfl⟩
    have he : biprod.lift leftMap (-rightMap) ≫ g =
        leftMap ≫ (biprod.inl ≫ g) - rightMap ≫ (biprod.inr ≫ g) := by
      simp only [biprod.lift_eq,
        Preadditive.add_comp, Category.assoc, Preadditive.neg_comp, sub_eq_add_neg]
    change sectionEquiv (biprod.lift leftMap (-rightMap) ≫ g) ∈ P
    rw [he, map_sub, leftNaturality, rightNaturality]
    exact P.sub_mem
      ((show (openRestriction M inf_le_left).range ≤ P from le_sup_left)
        ((openRestriction M inf_le_left).mem_range_self _))
      ((show (openRestriction M inf_le_right).range ≤ P from le_sup_right)
        ((openRestriction M inf_le_right).mem_range_self _))
  · apply sup_le
    · rintro x ⟨a,rfl⟩
      let morphism : FiniteCoverCohomology.freeOpenModule U ⟶ M :=
        (freeOpenLinearEquiv M U).symm a
      refine ⟨_, ⟨biprod.desc morphism 0,rfl⟩, ?_⟩
      change sectionEquiv (biprod.lift leftMap (-rightMap) ≫
        biprod.desc morphism 0) = _
      rw [biprod.lift_desc, comp_zero, add_zero, leftNaturality]
      exact congrArg (openRestriction M inf_le_left)
        ((freeOpenLinearEquiv M U).apply_symm_apply a)
    · rintro x ⟨b,rfl⟩
      let morphism : FiniteCoverCohomology.freeOpenModule V ⟶ M :=
        (freeOpenLinearEquiv M V).symm b
      refine ⟨_, ⟨biprod.desc 0 (-morphism),rfl⟩, ?_⟩
      change sectionEquiv (biprod.lift leftMap (-rightMap) ≫
        biprod.desc 0 (-morphism)) = _
      rw [biprod.lift_desc, comp_zero, zero_add, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, rightNaturality]
      exact congrArg (openRestriction M inf_le_right)
        ((freeOpenLinearEquiv M V).apply_symm_apply b)

def twoAffineUnionExtOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊔ V)) M 1 := by
  have hmid (y : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule U ⊞ FiniteCoverCohomology.freeOpenModule V) M 1) :
      y = 0 := by
    apply (Ext.biprodAddEquiv (C := X.Modules)).injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        FiniteCoverCohomology.affine_open_ext_zero U hU M 0
          ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        FiniteCoverCohomology.affine_open_ext_zero V hV M 0
          ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  let complex : ShortComplex X.Modules :=
    ModuleMayerVietoris.shortComplex X.ringCatSheaf U V
  let sectionEquiv : (complex.X₁ ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M (U ⊓ V) :=
    freeOpenLinearEquiv M (U ⊓ V)
  let e := Submodule.Quotient.equiv (LinearMap.range
      (Linear.leftComp Γ(X,⊤) M complex.f)) (twoChartImage M U V) sectionEquiv
    (twoChartImage_eq M U V)
  exact e.symm.trans (ExtCokernel.quotientEquiv (C := X.Modules) (S := complex)
    (ModuleMayerVietoris.shortComplex_shortExact X.ringCatSheaf U V) M hmid)

def twoAffineCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)] cohomology M 1 := by
  let e := twoAffineUnionExtOne M U V hU hV
  rw [hcover] at e
  exact e.trans (extSourceIso (FreeOpenUnit.freeTopIso X.ringCatSheaf) M 1)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_BaseCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                  
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseCohomologyOne [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hc : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) k
    (Sections k M (U ⊓ V) ⧸ twoBaseImage k M U V) ≃ₗ[K] cohomology M 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 1) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (U ⊓ V)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let baseImage : Submodule K (OpenSections M (U ⊓ V)) := twoBaseImage k M U V
  have he : baseImage = (twoChartImage M U V).restrictScalars K := by
    apply Submodule.ext
    intro x
    have baseMem := Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))
      (p := (res k M (show U ⊓ V ≤ U from inf_le_left)).range)
      (p' := (res k M (show U ⊓ V ≤ V from inf_le_right)).range) (x := x)
    have chartMem := Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))
      (p := (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range)
      (p' := (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range) (x := x)
    exact baseMem.trans chartMem.symm
  let E := Submodule.Quotient.restrictScalarsEquiv K (twoChartImage M U V)
  let F := (twoAffineCohomologyOne M U V hU hV hc).restrictScalars K
  exact (Submodule.quotEquivOfEq _ _ he).trans (E.trans F)
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma LineBundle.isoOpen_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : isoOpen s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hx,⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hc : coefficient e (restrictSection V.ι s) ≠ 0 := by
    intro h
    apply hs
    apply L.restricted_coefficient_injective V.ι e
    change coefficient e (restrictSection V.ι s) =
      coefficient e (restrictSection V.ι (0 : O X ⟶ L.sheaf))
    rw [restrictSection_zero]
    exact h.trans (coefficient_zero e).symm
  intro hz
  have he := preimage_isoOpen s V.ι e
  rw [hz] at he
  have hb : V.toScheme.basicOpen (coefficient e (restrictSection V.ι s)) = ⊥ := by
    simpa only [Scheme.Hom.preimage_bot] using he.symm
  exact hc (eq_zero_of_basicOpen_eq_bot _ hb)

lemma LineBundle.cokernel_support_finite [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    ((isoOpen s : Set X)ᶜ).Finite := by
  apply proper_closed_finite_of_dimension_one hd (isoOpen s).isOpen.isClosed_compl
  intro he
  have hb : isoOpen s = ⊥ := by
    apply SetLike.coe_injective
    simpa using he
  exact L.isoOpen_ne_bot s hs hb

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_AffineSectionQuotient
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma affine_global_sections_surjective [IsAffine X] [IsNoetherian X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Function.Surjective (S.g.app ⊤) := by
  intro m
  let t : O X ⟶ S.X₃ := (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃).symm m
  have hz : (Ext.mk₀ t).comp hS.extClass (show 0+1=1 from rfl) = 0 :=
    AffineSchemeCohomology.affine_ext_zero X S.X₁ 0 _
  obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₃ (O X) hS (Ext.mk₀ t) rfl hz
  obtain ⟨u,rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  have hu : u ≫ S.g = t := by
    apply (Ext.mk₀_bijective _ _).injective
    rwa [Ext.mk₀_comp_mk₀] at hz
  refine ⟨FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂ u, ?_⟩
  change FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃ (u ≫ S.g) = m
  exact (congrArg (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃) hu).trans
    (Equiv.apply_symm_apply _ m)

lemma frameCokernelMap_surjective [IsIntegral X] [IsNoetherian X] [IsAffine X]
    (L : LineBundle X) (e : L.sheaf ≅ O X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    Function.Surjective (frameCokernelMap e s) := by
  let B : LineBundle X := ⟨O X, fun _ =>
    ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (O X).IsQuasicoherent := B.quasicoherent
  have hp := affine_global_sections_surjective (L.section_shortExact s hs)
  have he := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e.symm).app (Opposite.op ⊤)).hom).surjective
  exact hp.comp he

def affine_section_quotient [IsIntegral X] [IsNoetherian X] [IsAffine X]
    (L : LineBundle X) (e : L.sheaf ≅ O X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    (Γ(X,⊤) ⧸ Ideal.span {coefficient e s}) ≃ₗ[Γ(X,⊤)] Γ(cokernel s,⊤) := by
  have he := (frameCokernelMap e s).quotKerEquivOfSurjective
    (frameCokernelMap_surjective L e s hs)
  rw [frameCokernelMap_ker L e s hs] at he
  exact he
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_LocalSectionDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

def restrictCokernelIso {M : X.Modules} (s : O X ⟶ M)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (cokernel s).restrict f ≅ cokernel (restrictSection f s) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) s ≪≫
    cokernel.mapIso _ _ (Scheme.Modules.restrictUnitIso f) (Iso.refl _)
      (by
        let unitIso : (O X).restrict f ≅ O Y := Scheme.Modules.restrictUnitIso f
        change (Scheme.Modules.restrictFunctor f).map s ≫ 𝟙 _ =
          unitIso.hom ≫ unitIso.inv ≫ (Scheme.Modules.restrictFunctor f).map s
        rw [Category.comp_id, unitIso.hom_inv_id_assoc])

lemma LineBundle.restrict_nonzero [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : restrictSection f s ≠ 0 := by
  intro h
  apply hs
  apply L.restrict_sections_injective f
  let unitIso : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi unitIso.inv).mp
  change restrictSection f s = restrictSection f 0
  simpa only [restrictSection_zero] using h

def sectionQuotientLocalMap [IsIntegral X] [IsNoetherian X]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Γ(cokernel s,⊤) →ₛₗ[f.appTop.hom]
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  letI : IsIntegral Y := isIntegral_of_isOpenImmersion f
  let E := (moduleIsoTop (restrictCokernelIso s f)).trans
    (affine_section_quotient (L.restrict f) e (restrictSection f s)
      (L.restrict_nonzero f s hs)).symm
  exact E.toLinearMap.comp (sectionRestrictionLinear (cokernel s) f)

def sectionQuotientLocalComplex [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
    letI := Module.compHom
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
    Γ(cokernel s,⊤) →ₗ[ℂ]
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  letI := Module.compHom
    (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
  refine { toFun := sectionQuotientLocalMap L s hs f e
           map_add' := (sectionQuotientLocalMap L s hs f e).map_add
           map_smul' := ?_ }
  intro r x
  change (sectionQuotientLocalMap L s hs f e) (baseScalars p r • x) =
    baseScalars (f ≫ p) r • (sectionQuotientLocalMap L s hs f e) x
  rw [baseScalars_comp_actual]
  exact (sectionQuotientLocalMap L s hs f e).map_smulₛₗ (baseScalars p r) x

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

def framedSectionsMorphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm).morphism

@[reassoc]
lemma framedSectionsMorphism_local (i : ι) :
    (U i).ι ≫ framedSectionsMorphism k s U hc e a hnorm =
      coordinatesMap (U i).toScheme ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))) (a i) (hnorm i) :=
  CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm) i

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_PullbackProjective
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso_all (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme, ∀ s : O X ⟶ M,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso_all F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e)
  refine ⟨eF, ?_⟩
  intro s
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have restrict_pullback : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) =
        uF.inv ≫ F.map s := by
      exact (congrArg (fun sectionMap =>
        (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫ sectionMap)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
          (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s))).trans
        (Category.assoc _ _ _).symm
    have pullback_restrict : pullbackSection (f ∣_ U) (restrictSection U.ι s) =
        uG.inv ≫ G.map s := by
      exact (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
        ((Scheme.Modules.pullback (f ∣_ U)).map_comp
          (Scheme.Modules.restrictUnitIso U.ι).inv
          ((Scheme.Modules.restrictFunctor U.ι).map s))).trans
        (Category.assoc _ _ _).symm
    exact (congrArg (coefficient eF) restrict_pullback).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e))
        pullback_restrict).symm)
  rw [he', coefficient_pullback]

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorDivision
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def frameOnSmaller {M : X.Modules} {U : X.Opens} (e : M.restrict U.ι ≅ O U.toScheme)
    (V : X.Opens) (h : V ≤ U) : M.restrict V.ι ≅ O V.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  obtain ⟨A,hA,⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨B,hB,⟨f⟩⟩ := M.locallyRankOne x
  obtain ⟨_,⟨U,hUa,rfl⟩,hx,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ A ⊓ B from ⟨hA,hB⟩)
      (A ⊓ B).isOpen
  exact ⟨⟨U,hUa⟩,hx,⟨frameOnSmaller e U (fun _ hy => (hU hy).1)⟩,
    ⟨frameOnSmaller f U (fun _ hy => (hU hy).2)⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e f ≪≫ moduleTensorUnit (O U.1.toScheme)⟩⟩

lemma sectionMultiply_eq (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    sectionMultiply L M s = (moduleTensorUnit M.sheaf).inv ≫
      moduleTensorMap s (𝟙 M.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let sheafification : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let counit : sheafification.obj M.sheaf.val ≅ M.sheaf :=
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M.sheaf
  change counit.inv ≫ sheafification.map
      ((λ_ M.sheaf.val).inv ≫ (s.val ⊗ₘ 𝟙 M.sheaf.val)) =
    (counit.inv ≫ sheafification.map (λ_ M.sheaf.val).inv) ≫
      sheafification.map (s.val ⊗ₘ 𝟙 M.sheaf.val)
  rw [sheafification.map_comp, Category.assoc]

def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma tensor_multiply_framed (L M : LineBundle X) (s : O X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiply L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let c : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let unitRestriction : F.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : F.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (F.obj (O X)) (F.obj M.sheaf) :=
    moduleTensorRestrict U (O X) M.sheaf
  let targetRestriction : F.obj (moduleTensor X L.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (F.obj L.sheaf) (F.obj M.sheaf) :=
    moduleTensorRestrict U L.sheaf M.sheaf
  let tensorMap : moduleTensor X (O X) M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    moduleTensorMap s (𝟙 M.sheaf)
  let multiplication : M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    sectionMultiply L M s
  have multiplication_eq : multiplication = sourceUnit.inv ≫ tensorMap :=
    sectionMultiply_eq L M s
  have he : F.map s ≫ e.hom = unitRestriction.hom ≫ c := by
    change F.map s ≫ e.hom = unitRestriction.hom ≫
      (unitRestriction.inv ≫ F.map s) ≫ e.hom
    exact ((Category.assoc _ _ _).trans
      (unitRestriction.hom_inv_id_assoc (F.map s ≫ e.hom))).symm
  have ht : moduleTensorMap (F.map s ≫ e.hom) f.hom =
      moduleTensorMap unitRestriction.hom f.hom ≫
        moduleTensorMap c (𝟙 (O U.toScheme)) := by
    rw [← moduleTensorMap_comp (X := U.toScheme),Category.comp_id,← he]
  have naturality : F.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (F.map s) (𝟙 (F.obj M.sheaf)) := by
    have naturality' : F.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (F.map s) (F.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U s (𝟙 M.sheaf)
    simpa only [F.map_id] using naturality'
  change f.inv ≫ F.map multiplication ≫ targetRestriction.hom ≫
      moduleTensorMap (X := U.toScheme) e.hom f.hom ≫ targetUnit.hom =
    (f.inv ≫ F.map sourceUnit.inv ≫ sourceRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom) ≫ c
  rw [multiplication_eq, F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map tensorMap), naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) (F.map s) (𝟙 _)),
    ← moduleTensorMap_comp (X := U.toScheme),
    Category.id_comp]
  rw [ht,Category.assoc]
  have hscalar : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ c := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id c))
  rw [hscalar]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorCurveEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma tensor_multiply_isoOpen (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    isoOpen (sectionMultiply L M s) = isoOpen s := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (sectionMultiply L M s) = U.1.ι ⁻¹ᵁ isoOpen s := by
    let restrictedMultiply : M.sheaf.restrict U.1.ι ⟶
        (L.tensor M).sheaf.restrict U.1.ι :=
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiply L M s)
    let tensorTrivialization : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
      tensorFrame L M U.1 e f
    calc
      _ = isoOpen restrictedMultiply := (isoOpen_restrict (sectionMultiply L M s) U.1.ι).symm
      _ = isoOpen (restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_postcomp restrictedMultiply tensorTrivialization).symm
      _ = isoOpen (f.inv ≫ restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_precomp f.symm (restrictedMultiply ≫ tensorTrivialization.hom)).symm
      _ = isoOpen ((tensorUnitTwist M U.1 f).hom ≫ (restrictSection U.1.ι s ≫ e.hom)) :=
        congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => isoOpen morphism)
          (tensor_multiply_framed L M s U.1 e f)
      _ = isoOpen (restrictSection U.1.ι s ≫ e.hom) :=
        isoOpen_precomp (tensorUnitTwist M U.1 f) _
      _ = isoOpen (restrictSection U.1.ι s) := isoOpen_postcomp _ e
      _ = _ := isoOpen_restrictSection s U.1.ι
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_FiniteSupportTwist
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

def tensorCokernelLocalIso (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (cokernel (sectionMultiply L M s)).restrict U.ι ≅ (cokernel s).restrict U.ι := by
  let t : M.sheaf.restrict U.ι ⟶ (L.tensor M).sheaf.restrict U.ι :=
    (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiply L M s)
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let frame : (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
    tensorFrame L M U e f
  let p := f ≪≫ twist
  let q := frame ≪≫ e.symm
  have framed : f.inv ≫ t ≫ frame.hom =
      twist.hom ≫ restrictSection U.ι s ≫ e.hom :=
    tensor_multiply_framed L M s U e f
  have he : t ≫ q.hom = p.hom ≫ restrictSection U.ι s := by
    apply (cancel_epi f.inv).mp
    apply (cancel_mono e.hom).mp
    simpa only [p,q,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.inv_hom_id_assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id] using framed
  exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) _ ≪≫
    cokernel.mapIso t (restrictSection U.ι s) p q he ≪≫
      (restrictCokernelIso s U.ι).symm

lemma LineBundle.sectionSupport_closed_points [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (x : X) (hx : x ∉ isoOpen s) :
    IsClosed ({x} : Set X) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hc : closure ({x} : Set X) ⊆ S :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
  have hsub : (closure ({x} : Set X)).Subsingleton := by
    apply proper_irreducible_closed_subsingleton hd isClosed_closure
      isIrreducible_singleton.closure
    intro he
    have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
    exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hsub hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact he ▸ isClosed_closure

def tensorCokernelGlobalEquiv [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    Γ(cokernel (sectionMultiply L M s),⊤) ≃ₗ[Γ(X,⊤)] Γ(cokernel s,⊤) := by
  classical
  apply finiteSupportLocallyIsoGlobal _ _ (isoOpen s : Set X)ᶜ
    (L.cokernel_support_finite hd s hs) (L.sectionSupport_closed_points hd s hs)
  · intro x hx
    apply cokernel_stalk_subsingleton (sectionMultiply L M s) x
    rw [tensor_multiply_isoOpen]
    exact not_not.mp hx
  · intro x hx
    exact cokernel_stalk_subsingleton s x (not_not.mp hx)
  · intro x _
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨tensorCokernelLocalIso L M s U.1 e f⟩⟩

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveDegreeAdditivity
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

def tensorCokernelComplexEquiv (p : X ⟶ Spec (CommRingCat.of ℂ))
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    letI := Module.compHom Γ(cokernel (sectionMultiply L M s),⊤) (baseScalars p)
    letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
    Γ(cokernel (sectionMultiply L M s),⊤) ≃ₗ[ℂ] Γ(cokernel s,⊤) := by
  letI := Module.compHom Γ(cokernel (sectionMultiply L M s),⊤) (baseScalars p)
  letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let e := tensorCokernelGlobalEquiv hd L M s hs
  let f : Γ(cokernel (sectionMultiply L M s),⊤) →ₗ[ℂ] Γ(cokernel s,⊤) :=
    { toFun := fun x => e x
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (baseScalars p r • x) = baseScalars p r • e x
        exact e.map_smul _ _ }
  exact LinearEquiv.ofBijective f e.bijective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def shortComplexMap {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    shortComplex R U V ⟶ shortComplex R U' V' where
  τ₁ := freeOpenMap R (homOfLE (inf_le_inf hU hV))
  τ₂ := biprod.map (freeOpenMap R (homOfLE hU)) (freeOpenMap R (homOfLE hV))
  τ₃ := freeOpenMap R (homOfLE (sup_le_sup hU hV))
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [shortComplex, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
        biprod.lift_fst, freeOpenMap_comp]
      rfl
    · simp only [shortComplex, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
        biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg, freeOpenMap_comp]
      rfl
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [shortComplex, biprod.inl_map_assoc, biprod.inl_desc_assoc,
        biprod.inl_desc, freeOpenMap_comp]
      rfl
    · simp only [shortComplex, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        biprod.inr_desc, freeOpenMap_comp]
      rfl
end
end MaximalSeshadri.ModuleMayerVietoris

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}

attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechLinear
attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechHasExt
local instance surfaceCechFreeHomGroup_rf0a496_1 (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _
local instance surfaceCechFreeHomModule_rf0a496_1 (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _
lemma openBoundary_left (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_left))).comp x
        (zero_add n)) = 0 := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let projection : complex.X₂ ⟶ FiniteCoverCohomology.freeOpenModule U :=
    biprod.fst (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V)
  let inclusion : complex.X₁ ⟶
      FiniteCoverCohomology.freeOpenModule U :=
    freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_left)
  have factor : complex.f ≫ projection = inclusion := by
    exact biprod.lift_fst (C := X.Modules)
      (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V) _ _
  have boundaryZero := exactness.extClass_comp_assoc (C := X.Modules)
    (h := show 1 + n = n + 1 by omega)
    ((Ext.mk₀ (C := X.Modules) projection).comp x (zero_add n))
  rw [Ext.mk₀_comp_mk₀_assoc (C := X.Modules), factor] at boundaryZero
  exact boundaryZero

lemma openBoundary_right (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule V) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_right))).comp x
        (zero_add n)) = 0 := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let projection : complex.X₂ ⟶ FiniteCoverCohomology.freeOpenModule V :=
    -(biprod.snd (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V))
  let inclusion : complex.X₁ ⟶
      FiniteCoverCohomology.freeOpenModule V :=
    freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_right)
  have factor : complex.f ≫ projection = inclusion := by
    exact (Preadditive.comp_neg _ _).trans
      ((congrArg Neg.neg (biprod.lift_snd (C := X.Modules)
        (X := FiniteCoverCohomology.freeOpenModule U)
        (Y := FiniteCoverCohomology.freeOpenModule V) _ _)).trans (neg_neg _))
  have boundaryZero := exactness.extClass_comp_assoc (C := X.Modules)
    (h := show 1 + n = n + 1 by omega)
    ((Ext.mk₀ (C := X.Modules) projection).comp x (zero_add n))
  rw [Ext.mk₀_comp_mk₀_assoc (C := X.Modules), factor] at boundaryZero
  exact boundaryZero

lemma openBoundary_natural (M : X.Modules) {U V U' V' : X.Opens}
    (hU : U ≤ U') (hV : V ≤ V') (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U' ⊓ V')) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (inf_le_inf hU hV)))).comp x
        (zero_add n)) =
      (Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (sup_le_sup hU hV)))).comp
        (openBoundary M U' V' n x) (zero_add (n+1)) := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let complex' : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U' V'
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let exactness' : complex'.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U' V'
  let morphism : complex ⟶ complex' := shortComplexMap (X := X.carrier) X.ringCatSheaf hU hV
  let extension : Ext.{1} (C := X.Modules) complex'.X₁ M n := x
  have naturality := exactness.extClass_naturality exactness' morphism
  change exactness.extClass.comp ((Ext.mk₀ (C := X.Modules) morphism.τ₁).comp extension (zero_add n))
      (show 1 + n = n + 1 by omega) =
    (Ext.mk₀ (C := X.Modules) morphism.τ₃).comp
      (exactness'.extClass.comp extension (show 1 + n = n + 1 by omega)) (zero_add (n+1))
  rw [← Ext.comp_assoc_of_second_deg_zero, naturality]
  exact Ext.comp_assoc _ _ _ (by omega) (by omega) (by omega)

def tripleSectionBoundary (M : X.Modules) (U V W : X.Opens) :
    OpenSections M (tripleOpen U V W) →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W)) M 2 :=
  (openBoundary M (U ⊔ V) W 1).comp
    ((extSourceIso (overlapIso U V W) M 1).toLinearMap.comp
      ((openBoundary M (U ⊓ W) (V ⊓ W) 0).comp
        ((Ext.linearEquiv₀ (C := X.Modules) (R := Γ(X,⊤))
          (X := FiniteCoverCohomology.freeOpenModule (tripleOpen U V W)) (Y := M)).symm.toLinearMap.comp
          (freeOpenLinearEquiv M (tripleOpen U V W)).symm.toLinearMap)))

def openSectionExt (M : X.Modules) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M 0 := by
  let sectionEquiv : (FiniteCoverCohomology.freeOpenModule U ⟶ M) ≃ₗ[Γ(X,⊤)]
      OpenSections M U := freeOpenLinearEquiv M U
  exact sectionEquiv.symm.trans (Ext.linearEquiv₀ (C := X.Modules)
    (X := FiniteCoverCohomology.freeOpenModule U) (Y := M)).symm

lemma openSectionExt_restrict (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections M V) :
    openSectionExt M U (openRestriction M h x) =
      (Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE h))).comp
        (openSectionExt M V x) (zero_add 0) := by
  have he : (freeOpenLinearEquiv M U).symm (openRestriction M h x) =
      freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE h) ≫ (freeOpenLinearEquiv M V).symm x := by
    apply (freeOpenLinearEquiv M U).injective
    rw [LinearEquiv.apply_symm_apply, freeOpenLinearEquiv_naturality,
      LinearEquiv.apply_symm_apply]
  exact (congrArg (Ext.mk₀ (C := X.Modules)) he).trans
    (Ext.mk₀_comp_mk₀ (C := X.Modules) _ _).symm

lemma tripleSectionBoundary_apply (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (tripleOpen U V W)) :
    tripleSectionBoundary M U V W x =
      openBoundary M (U ⊔ V) W 1
        ((Ext.mk₀ (overlapIso U V W).inv).comp
          (openBoundary M (U ⊓ W) (V ⊓ W) 0 (openSectionExt M _ x)) (zero_add 1)) := rfl

lemma tripleSectionBoundary_left (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (U ⊓ W)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ U ⊓ W from inf_le_left) x
  have hb := openBoundary_left M (U ⊓ W) (V ⊓ W) 0
    (openSectionExt M (U ⊓ W) x)
  rw [tripleSectionBoundary_apply]
  have he := (congrArg (openBoundary M (U ⊓ W) (V ⊓ W) 0) hx).trans hb
  dsimp only [tripleOpen] at he
  let F := (openBoundary M (U ⊔ V) W 1).comp
    (extSourceIso (overlapIso U V W) M 1).toLinearMap
  exact (congrArg F he).trans F.map_zero

lemma tripleSectionBoundary_right (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (V ⊓ W)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ V ⊓ W from inf_le_right) x
  have hb := openBoundary_right M (U ⊓ W) (V ⊓ W) 0
    (openSectionExt M (V ⊓ W) x)
  rw [tripleSectionBoundary_apply]
  have he := (congrArg (openBoundary M (U ⊓ W) (V ⊓ W) 0) hx).trans hb
  dsimp only [tripleOpen] at he
  let F := (openBoundary M (U ⊔ V) W 1).comp
    (extSourceIso (overlapIso U V W) M 1).toLinearMap
  exact (congrArg F he).trans F.map_zero

lemma tripleSectionBoundary_top (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (U ⊓ V)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
        inf_le_inf inf_le_left inf_le_left) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ U ⊓ V from inf_le_inf inf_le_left inf_le_left) x
  have hn := openBoundary_natural M (show U ⊓ W ≤ U from inf_le_left)
    (show V ⊓ W ≤ V from inf_le_left) 0 (openSectionExt M (U ⊓ V) x)
  have he : (overlapIso U V W).inv ≫
      freeOpenMap (X := X.carrier) X.ringCatSheaf
        (homOfLE (sup_le_sup (show U ⊓ W ≤ U from inf_le_left)
          (show V ⊓ W ≤ V from inf_le_left))) =
      freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (show (U ⊔ V) ⊓ W ≤ U ⊔ V from
        inf_le_left)) := by
    change (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).map _ ≫
      (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).map _ = _
    rw [← Functor.map_comp]
    rfl
  dsimp only [tripleOpen] at hx
  rw [tripleSectionBoundary_apply]
  erw [hx, hn, Ext.mk₀_comp_mk₀_assoc, he]
  exact openBoundary_left M (U ⊔ V) W 1 (openBoundary M U V 0 (openSectionExt M _ x))

lemma tripleChartImage_le_ker (M : X.Modules) (U V W : X.Opens) :
    tripleChartImage M U V W ≤ (tripleSectionBoundary M U V W).ker := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_left M U V W x
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_right M U V W x
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_top M U V W x

def tripleCokernelBoundary (M : X.Modules) (U V W : X.Opens) :
    (OpenSections M (tripleOpen U V W) ⧸ tripleChartImage M U V W) →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W)) M 2 :=
  (tripleChartImage M U V W).liftQ (tripleSectionBoundary M U V W)
    (tripleChartImage_le_ker M U V W)

def tripleCohomologyTwo (M : X.Modules) (U V W : X.Opens)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    (OpenSections M (tripleOpen U V W) ⧸ tripleChartImage M U V W) →ₗ[Γ(X,⊤)]
      cohomology M 2 := by
  let F := tripleCokernelBoundary M U V W
  let e : FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W) ≅ structureSheaf X :=
    (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso hc) ≪≫
    FreeOpenUnit.freeTopIso X.ringCatSheaf
  exact (extSourceIso e M 2).toLinearMap.comp F

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceBaseCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def tripleBaseCohomologyTwo (k : K →+* Γ(X,⊤))
    (M : X.Modules) (U V W : X.Opens) (hc : (U ⊔ V) ⊔ W = ⊤) :
    letI := Module.compHom (cohomology M 2) k
    (Sections k M (tripleOpen U V W) ⧸ tripleBaseImage k M U V W) →ₗ[K]
      cohomology M 2 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 2) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 2) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (tripleOpen U V W)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (tripleOpen U V W)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have he : tripleBaseImage k M U V W = (tripleChartImage M U V W).restrictScalars K := by
    have hsup := Submodule.restrictScalars_sup K
      ((openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
       (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range)
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
        inf_le_inf inf_le_left inf_le_left)).range
    conv_rhs at hsup => rw [Submodule.restrictScalars_sup]
    exact hsup.symm
  let F := ((tripleCohomologyTwo M U V W hc).comp
    (tripleChartImage M U V W).mkQ).restrictScalars K
  refine (tripleBaseImage k M U V W).liftQ F ?_
  intro z hz
  have hz' : z ∈ tripleChartImage M U V W := by
    change z ∈ (tripleChartImage M U V W).restrictScalars K
    rw [← he]
    exact hz
  change tripleCohomologyTwo M U V W hc
    ((tripleChartImage M U V W).mkQ z) = 0
  rw [show (tripleChartImage M U V W).mkQ z = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr hz', map_zero]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneVertex
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeVertex (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i : Fin 3) :=
  (chartRes k L.sheaf (planeTriple_le s i)).range

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceH0Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma global_plane_vertex (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (L : LineBundle X) (m : Sections k L.sheaf ⊤) (i : Fin 3) :
    (chartTop k L.sheaf (planeTriple s)).symm
      (res k L.sheaf (show planeTriple s ≤ ⊤ from le_top) m) ∈ planeVertex k s L i := by
  refine ⟨(chartTop k L.sheaf (SectionOpens.isoOpen (s i))).symm
    (res k L.sheaf (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top) m),?_⟩
  apply (chartTop k L.sheaf (planeTriple s)).injective
  rw [chartTop_nested,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,res_comp]

def globalPlaneIntersection (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    Sections k L.sheaf ⊤ →ₗ[K]
      ↥((planeVertex k s L 0 ⊓ planeVertex k s L 1) ⊓ planeVertex k s L 2) :=
  (((chartTop k L.sheaf (planeTriple s)).symm.toLinearMap).comp
    (res k L.sheaf (show planeTriple s ≤ ⊤ from le_top))).codRestrict _
      (fun m => ⟨⟨global_plane_vertex k s L m 0,global_plane_vertex k s L m 1⟩,
        global_plane_vertex k s L m 2⟩)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def affineCoefficient {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) : Γ(X,U.1) :=
  U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionGermSystem
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma global_smul_eq_scalarEnd {M : X.Modules} (r : Γ(X,⊤)) (s : O X ⟶ M) :
    r • s = scalarEnd r ≫ s := by
  ext U a
  change Γ(X,U) at a
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • s.app U a =
    s.app U ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) * a)
  exact (s.app_smul _ _).symm

def affineCoefficientLinear (g : X ⟶ Spec (CommRingCat.of ℂ))
    {M : X.Modules} (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    letI := complexSectionModule g M
    letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    GlobalSections X M →ₗ[ℂ] Γ(X,U.1) := by
  letI := complexSectionModule g M
  letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
  refine { toFun := affineCoefficient U e
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    exact (congrArg (fun sectionValue => U.1.topIso.hom (coefficient e sectionValue))
      (restrictSection_add U.1.ι s t)).trans
      ((congrArg U.1.topIso.hom
        (coefficient_add e (restrictSection U.1.ι s) (restrictSection U.1.ι t))).trans
        (map_add U.1.topIso.hom.hom _ _))
  · intro c s
    change affineCoefficient U e (baseScalars g c • s) =
      openScalars g U.1 c * affineCoefficient U e s
    refine (congrArg (affineCoefficient U e)
      (global_smul_eq_scalarEnd (baseScalars g c) s)).trans ?_
    refine (congrArg U.1.topIso.hom
      (coefficient_restrict_scalar_comp U.1.ι e (baseScalars g c) s)).trans ?_
    refine (map_mul U.1.topIso.hom.hom _ _).trans ?_
    apply congrArg (fun value => value * affineCoefficient U e s)
    change (U.1.ι.appTop ≫ U.1.topIso.hom) (baseScalars g c) = openScalars g U.1 c
    have H := congrArg (fun f : ℂ →+* Γ(X,U.1) => f c) (topIso_baseScalars g U.1)
    rw [baseScalars_comp_actual] at H
    exact H

lemma affineCoefficientLinear_injective [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Function.Injective (affineCoefficientLinear g U e) := by
  intro s t h
  apply L.restricted_coefficient_injective U.1.ι e
  exact (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective h

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineOrderRestriction
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma frameOnSmaller_coefficient {M : X.Modules} (U V : X.Opens) (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (frameOnSmaller e V h) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold frameOnSmaller
  rw [coefficient_transport]
  change coefficient ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    restrictFrame (X.homOfLE h) e) (restrictSection V.ι s ≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M) = _
  rw [restrictSection_congr,coefficient_restrict_comp]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorInclusion
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_PowerIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def idealPowerInclusion (J : LineBundle X) (ι : J.sheaf ⟶ O X) :
    ∀ n : ℕ, (J.pow n).sheaf ⟶ O X
  | 0 => 𝟙 _
  | n+1 => tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n

def idealPowerFrame (J : LineBundle X) (U : X.Opens)
    (e : J.sheaf.restrict U.ι ≅ O U.toScheme) :
    ∀ n : ℕ, (J.pow n).sheaf.restrict U.ι ≅ O U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n+1 => tensorFrame J (J.pow n) U e (idealPowerFrame J U e n)

def affineMapCoefficient {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) : Γ(X,U.1) :=
  U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a ≫ f.hom))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_IdealSectionLifting
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_affine_coefficient (f : Y ⟶ X) (V : X.affineOpens)
    {M : X.Modules} (e : M.restrict V.1.ι ≅ O V.1.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ V.1).ι ≅
      O (f ⁻¹ᵁ V.1).toScheme,
      ∀ (W : Y.affineOpens) (h : W.1 ≤ f ⁻¹ᵁ V.1) (s : O X ⟶ M),
        affineCoefficient W (frameOnSmaller eF W.1 h) (pullbackSection f s) =
          f.appLE V.1 W.1 h (affineCoefficient V e s) := by
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f V.1 e
  refine ⟨eF,fun W h s => ?_⟩
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient,he s]
  have hmap : (f.resLE V.1 W.1 h).appTop ≫ W.1.topIso.hom =
      V.1.topIso.hom ≫ f.appLE V.1 W.1 h :=
    (arrowResLEAppIso f V.1 W.1 h).hom.w.symm
  exact congrArg (fun restriction : Γ(V.1.toScheme, ⊤) ⟶ Γ(Y, W.1) =>
    restriction (coefficient e (restrictSection V.1.ι s))) hmap

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PullbackSectionLinear
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullbackSection_linear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (∀ s t : (O X ⟶ L.sheaf), pullbackSection f (s+t) = pullbackSection f s + pullbackSection f t) ∧
    (∀ (c : ℂ) (s : (O X ⟶ L.sheaf)), pullbackSection f (c • s) = c • (pullbackSection f s : (O Y ⟶ (L.pullback f).sheaf))) := by
  classical
  let (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
  let (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
  let y : Y := Classical.arbitrary Y
  obtain ⟨V,hyV,⟨eV⟩,-⟩ := common_affine_frames L L (f y)
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  obtain ⟨_,⟨W,hW,rfl⟩,hyW,hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ f ⁻¹ᵁ V.1 from hyV) (f ⁻¹ᵁ V.1).isOpen
  let U : Y.affineOpens := ⟨W,hW⟩
  let eU := frameOnSmaller eF U.1 hWV
  let : Nonempty U.1 := ⟨⟨y,hyW⟩⟩
  let : Algebra ℂ Γ(X,V.1) := (openScalars g V.1).toAlgebra
  let : Algebra ℂ Γ(Y,U.1) := (openScalars h U.1).toAlgebra
  let A := affineCoefficientLinear h U eU
  let B := affineCoefficientLinear g V eV
  let F := affineMapAlgHom h g f hf V U hWV
  have hA := affineCoefficientLinear_injective h (L.pullback f) U eU
  have he (s : (O X ⟶ L.sheaf)) : A (pullbackSection f s) = F (B s) := heF U hWV s
  let := complexSectionModule g L.sheaf
  let := complexSectionModule h ((Scheme.Modules.pullback f).obj L.sheaf)
  constructor
  · intro s t
    apply hA
    change A (pullbackSection f (s+t)) = A (pullbackSection f s + pullbackSection f t)
    calc
      A (pullbackSection f (s+t)) = F (B (s+t)) := he _
      _ = F (B s + B t) := congrArg F (B.map_add s t)
      _ = F (B s) + F (B t) := map_add F _ _
      _ = A (pullbackSection f s) + A (pullbackSection f t) :=
        congrArg₂ (· + ·) (he s).symm (he t).symm
      _ = A (pullbackSection f s + pullbackSection f t) := (A.map_add _ _).symm
  · intro c s
    apply hA
    change A (pullbackSection f (c • s)) = A (c • pullbackSection f s)
    calc
      A (pullbackSection f (c • s)) = F (B (c • s)) := he _
      _ = F (c • B s) := congrArg F (B.map_smul c s)
      _ = c • F (B s) := map_smul F c (B s)
      _ = c • A (pullbackSection f s) := congrArg (c • ·) (he s).symm
      _ = A (c • pullbackSection f s) := (A.map_smul c _).symm

def pullbackSectionLinear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (O X ⟶ L.sheaf) →ₗ[ℂ] (O Y ⟶ (L.pullback f).sheaf) := by
  letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
  letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
  exact { toFun := pullbackSection f
          map_add' := (pullbackSection_linear g h f hf L).1
          map_smul' := (pullbackSection_linear g h f hf L).2 }

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupSectionDimensions
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

def sectionPostcompose {X : Scheme.{0}} (g : X ⟶ complexBase) {M N : X.Modules}
    (φ : M ⟶ N) :
    letI (P : X.Modules) : Module ℂ (O X ⟶ P) := complexSectionModule g P
    (O X ⟶ M) →ₗ[ℂ] (O X ⟶ N) := by
  let (P : X.Modules) : Module ℂ (O X ⟶ P) := complexSectionModule g P
  refine { toFun := fun s => s ≫ φ
           map_add' := fun s t => Preadditive.add_comp _ _ _ s t φ
           map_smul' := fun c s => ?_ }
  exact Linear.smul_comp _ _ _ (baseScalars g c) s φ

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleFree
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_hom_ext {A B Q : Opens X} (hA : A ≤ Q) (hB : B ≤ Q) (h : A ⊔ B = Q)
    {N : SheafOfModules R} {f g : freeOpen R Q ⟶ N}
    (ha : freeOpenMap R (homOfLE hA) ≫ f = freeOpenMap R (homOfLE hA) ≫ g)
    (hb : freeOpenMap R (homOfLE hB) ≫ f = freeOpenMap R (homOfLE hB) ≫ g) : f = g := by
  subst Q
  apply CategoryTheory.IsPushout.hom_ext (freeOpen_isPushout R A B) ha hb

lemma freeOpen_glue3 {U V W : Opens X} {N : SheafOfModules R}
    (f : freeOpen R U ⟶ N) (g : freeOpen R V ⟶ N) (h : freeOpen R W ⟶ N)
    (hfg : freeOpenMap R (homOfLE (show U ⊓ V ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ V ≤ V from inf_le_right)) ≫ g)
    (hfh : freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ W ≤ W from inf_le_right)) ≫ h)
    (hgh : freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫ g =
      freeOpenMap R (homOfLE (show V ⊓ W ≤ W from inf_le_right)) ≫ h) :
    ∃ l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N,
      freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)) ≫ l = f ∧
      freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)) ≫ l = g ∧
      freeOpenMap R (homOfLE le_sup_right) ≫ l = h := by
  let p : freeOpen R (U ⊔ V) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R U V) f g hfg
  have hpU : freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫ p = f :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R U V) f g hfg
  have hpV : freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫ p = g :=
    CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R U V) f g hfg
  have hp : freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ U ⊔ V from inf_le_left)) ≫ p =
      freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ W from inf_le_right)) ≫ h := by
    apply freeOpen_hom_ext R (A := U ⊓ W) (B := V ⊓ W)
      (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl) (inf_sup_right U V W).symm
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_left)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show U ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_left)) =
        freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpU]
      exact hfh
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_right)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show V ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_right)) =
        freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpV]
      exact hgh
  let l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  have hl : freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) ≫ l = p :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  refine ⟨l,?_,?_,CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp⟩
  · rw [show freeOpenMap R (homOfLE (show U ≤ (U ⊔ V) ⊔ W from le_sup_left.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpU]
  · rw [show freeOpenMap R (homOfLE (show V ≤ (U ⊔ V) ⊔ W from le_sup_right.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpV]

end
end MaximalSeshadri.ModuleMayerVietoris

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleComplex
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

instance tripleG_epi (U V W : Opens X) : Epi (tripleG R U V W) := by
  constructor
  intro N f g h
  apply freeOpen_hom_ext R (A := U ⊔ V) (B := W) le_sup_left le_sup_right rfl
  · apply freeOpen_hom_ext R (A := U) (B := V) le_sup_left le_sup_right rfl
    · have hh := congrArg (fun z => biprod.inl ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
    · have hh := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
  · have hh := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) h
    simpa [tripleG,Category.assoc] using hh

def tripleG_isCokernel (U V W : Opens X) :
    IsColimit (CokernelCofork.ofπ (tripleG R U V W) (tripleDG R U V W)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro N k hk
  have hab := congrArg (fun z => biprod.inl ≫ z) hk
  have hac := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) hk
  have hbc := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) hk
  simp only [tripleD,Category.assoc,biprod.inl_desc_assoc,biprod.inr_desc_assoc,
    Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,Limits.comp_zero] at hab hac hbc
  apply Classical.indefiniteDescription
  obtain ⟨l,hl0,hl1,hl2⟩ := freeOpen_glue3 R (biprod.inl ≫ k)
    (biprod.inl ≫ biprod.inr ≫ k) (biprod.inr ≫ biprod.inr ≫ k)
    (sub_eq_zero.mp hab) (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using (sub_eq_zero.mp (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using hac)).symm)
    (sub_eq_zero.mp hbc)
  refine ⟨l,?_⟩
  apply biprod.hom_ext'
  · simpa [tripleG,Category.assoc] using hl0
  · apply biprod.hom_ext'
    · simpa [tripleG,Category.assoc] using hl1
    · simpa [tripleG,Category.assoc] using hl2

instance tripleToRelations_epi (U V W : Opens X) : Epi (tripleToRelations R U V W) := by
  let S := ShortComplex.mk (tripleD R U V W) (tripleG R U V W) (tripleDG R U V W)
  exact S.exact_iff_epi_kernel_lift.mp (S.exact_of_g_is_cokernel (tripleG_isCokernel R U V W))

abbrev tripleKernelComplex (U V W : Opens X) :=
  ShortComplex.mk (kernel.ι (tripleG R U V W)) (tripleG R U V W) (kernel.condition _)
lemma tripleKernelComplex_shortExact (U V W : Opens X) :
    (tripleKernelComplex R U V W).ShortExact := by
  exact ⟨(tripleKernelComplex R U V W).exact_of_f_is_kernel (kernelIsKernel _)⟩

end
end MaximalSeshadri.ModuleMayerVietoris

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneRelationCycles
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] baseHomModule

def relationCycles (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K]
      cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2) :=
  ((relationA k s L).prod ((relationB k s L).prod (relationC k s L))).codRestrict _ (by
    intro f
    let morphism : planeRelations s ⟶ L.sheaf := f
    have h := tripleToRelations_cycle X.ringCatSheaf (planeTriple_le s 0) (planeTriple_le s 1) (planeTriple_le s 2)
    let post : (freeOpen X.ringCatSheaf (planeTriple s) ⟶ planeRelations s) →+
        BaseHom k (freeOpen X.ringCatSheaf (planeTriple s)) L.sheaf :=
      { toFun := fun arrow => arrow ≫ morphism
        map_zero' := Limits.zero_comp
        map_add' := fun first second => Preadditive.add_comp _ _ _ first second morphism }
    let evaluate := (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s)).toAddMonoidHom.comp post
    have evaluate_map {chart : X.Opens} (restriction : planeTriple s ≤ chart)
        (arrow : freeOpen X.ringCatSheaf chart ⟶ planeRelations s) :
        evaluate (freeOpenMap X.ringCatSheaf (homOfLE restriction) ≫ arrow) =
          homChart k L.sheaf restriction (arrow ≫ morphism) :=
      (congrArg (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s))
        (Category.assoc _ _ _)).trans (homChart_natural k L.sheaf le_rfl restriction _)
    have he := congrArg evaluate h
    simp only [map_add, map_zero, evaluate_map] at he
    exact he)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleExt
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}

attribute [local instance] OAI.MaximalSeshadri.Geometry.tripleExtLinear
attribute [local instance] OAI.MaximalSeshadri.Geometry.tripleExtHasExt
def tripleHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) complex.X₃ M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let exactness : complex.ShortExact :=
    tripleKernelComplex_shortExact (X := X.carrier) X.ringCatSheaf U V W
  refine ExtCokernel.quotientEquiv (C := X.Modules) (K := Γ(X,⊤))
    (S := complex) exactness M ?_
  change ∀ middleClass : Ext.{1} (C := X.Modules)
    (FiniteCoverCohomology.freeOpenModule U ⊞
      (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W))
    M 1, middleClass = 0
  intro middleClass
  apply (Ext.biprodAddEquiv (C := X.Modules)).injective
  apply Prod.ext
  · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
       FiniteCoverCohomology.affine_open_ext_zero (X := X) U hU M 0
        ((Ext.mk₀ biprod.inl).comp middleClass (zero_add _))
  · have h (z : Ext.{1} (C := X.Modules)
        (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W)
        M 1) : z = 0 := by
      apply (Ext.biprodAddEquiv (C := X.Modules)).injective
      apply Prod.ext
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) V hV M 0
            ((Ext.mk₀ biprod.inl).comp z (zero_add _))
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) W hW M 0
            ((Ext.mk₀ biprod.inr).comp z (zero_add _))
    simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
      h ((Ext.mk₀ biprod.inr).comp middleClass (zero_add _))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleTopExt
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}

attribute [local instance] OAI.MaximalSeshadri.Geometry.tripleTopExtLinear
local instance tripleTopExtHasExt_rf0a496_1 : HasExt.{1} X.Modules := schemeHasExt
def tripleTopHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let topIso : complex.X₃ ≅ structureSheaf X :=
    eqToIso (congrArg (FiniteCoverCohomology.freeOpenModule (X := X)) hc) ≪≫
      FreeOpenUnit.freeTopIso X.ringCatSheaf
  exact (tripleHomExtEquiv (X := X) M U V W hU hV hW).trans
    (extSourceIso (X := X) topIso M 1)

def tripleTopHomCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    (complex.X₁ ⟶ M) →ₗ[Γ(X,⊤)] cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  exact (tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc).toLinearMap.comp
    (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ

lemma tripleTopHomCohomologyOne_zero [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ∀ (x : complex.X₁ ⟶ M),
      x ∈ (Linear.leftComp Γ(X,⊤) M complex.f).range →
      tripleTopHomCohomologyOne M U V W hU hV hW hc x = 0 := by
  intro complex relation inRange
  let quotientEquiv := tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc
  have class_zero : (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ relation = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr inRange
  exact (congrArg quotientEquiv class_zero).trans quotientEquiv.map_zero
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceH1Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections ModuleFlasque ModuleMayerVietoris
open MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] baseHomModule

def planeBaseCohomologyOneMap [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) →ₗ[K]
      cohomology L.sheaf 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology L.sheaf 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology L.sheaf 1) := .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (planeRelations s ⟶ L.sheaf) := Module.compHom (planeRelations s ⟶ L.sheaf) k
  letI : IsScalarTower K Γ(X,⊤) (planeRelations s ⟶ L.sheaf) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have hc : (SectionOpens.isoOpen (s 0) ⊔ SectionOpens.isoOpen (s 1)) ⊔
      SectionOpens.isoOpen (s 2) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs ▸ hx)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  let F := (tripleTopHomCohomologyOne L.sheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)) (h 0) (h 1) (h 2) hc).restrictScalars K
  refine (relationBoundaries k s L).liftQ F ?_
  intro x hx
  exact tripleTopHomCohomologyOne_zero L.sheaf _ _ _ (h 0) (h 1) (h 2) hc x hx

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CenteredSections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ] {X : Scheme}

local instance instDecidableEq_solutions_rf0a496_1 : DecidableEq σ := Classical.decEq σ
@[simp] lemma scalarEnd_zero : scalarEnd (0 : Γ(X, ⊤)) = 0 := by
  apply endValue_injective
  rw [endValue_scalarEnd]
  rfl

@[simp] lemma scalarEnd_one : scalarEnd (1 : Γ(X, ⊤)) = 𝟙 (O X) := by
  apply endValue_injective
  simp

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_IdealProductDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def finiteTensor : (n : ℕ) → (Fin n → LineBundle X) → LineBundle X
  | 0, _ => { sheaf := O X, locallyRankOne := fun x =>
      ⟨⊤,by trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩ }
  | n+1, J => (J 0).tensor (finiteTensor n (fun i => J i.succ))

def finiteTensorInclusion : (n : ℕ) → (J : Fin n → LineBundle X) →
    (∀ i, (J i).sheaf ⟶ O X) → ((finiteTensor n J).sheaf ⟶ O X)
  | 0, _, _ => 𝟙 _
  | n+1, J, a => tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) ≫
      finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ)

def finiteTensorFrame (U : X.Opens) : (n : ℕ) → (J : Fin n → LineBundle X) →
    (∀ i, (J i).sheaf.restrict U.ι ≅ O U.toScheme) →
    ((finiteTensor n J).sheaf.restrict U.ι ≅ O U.toScheme)
  | 0, _, _ => Scheme.Modules.restrictUnitIso U.ι
  | n+1, J, e => tensorFrame (J 0) (finiteTensor n (fun i => J i.succ)) U (e 0)
      (finiteTensorFrame U n (fun i => J i.succ) (fun i => e i.succ))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_QuarticSubsystem
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

def doublePointQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (j : QuarticIndex σ) : O X ⟶ modulePow X M 4 :=
  quarticSection (s (some j.1)) (s (some j.2.1)) (s j.2.2.1) (s j.2.2.2)

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceTwistEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

def mixedEuler (S : Surface) (L M : LineBundle S.scheme) : ℤ :=
  eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf -
    eulerCharacteristic S.structureMap 2 L.sheaf -
    eulerCharacteristic S.structureMap 2 M.sheaf +
    eulerCharacteristic S.structureMap 2 (O S.scheme)

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_CenteredJetChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

def affineSectionRatios (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (j : Option σ) : Γ(X, U.1) :=
  U.1.topIso.hom (coefficient (sectionFrameOn (s none) U.1 hU)
    (restrictSection U.1.ι (s j)))

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorPowerDistribution
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def lineTensorInterchange (A B C D : LineBundle X) :
    ((A.tensor B).tensor (C.tensor D)).sheaf ≅ ((A.tensor C).tensor (B.tensor D)).sheaf :=
  lineTensorAssoc A B (C.tensor D) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc B C D).symm ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (moduleTensorIso (moduleTensorComm B.sheaf C.sheaf) (Iso.refl D.sheaf)) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc C B D) ≪≫
  (lineTensorAssoc A C (B.tensor D)).symm

def lineTensorPower (L M : LineBundle X) : ∀ n : ℕ,
    ((L.tensor M).pow n).sheaf ≅ ((L.pow n).tensor (M.pow n)).sheaf
  | 0 => (moduleTensorUnit (O X)).symm
  | n+1 => moduleTensorIso (Iso.refl _) (lineTensorPower L M n) ≪≫
    lineTensorInterchange L M (L.pow n) (M.pow n)

def lineTwistPower (L M : LineBundle X) (d n : ℕ) :
    (((L.pow d).tensor M).pow n).sheaf ≅ ((L.pow (d*n)).tensor (M.pow n)).sheaf :=
  lineTensorPower (L.pow d) M n ≪≫ moduleTensorIso (linePowerMul L d n) (Iso.refl _)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_TwistedIdealPower
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def twistIdealPowerIso (L J : LineBundle X) (a b n : ℕ) :
    (((L.pow a).tensor (J.pow b)).pow n).sheaf ≅
      ((J.pow (b*n)).tensor (L.pow (a*n))).sheaf :=
  lineTwistPower L (J.pow b) a n ≪≫
    moduleTensorIso (Iso.refl _) (linePowerMul J b n) ≪≫
      moduleTensorComm _ _

def twistedIdealPowerInclusion (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) : (((L.pow a).tensor (J.pow b)).pow n).sheaf ⟶ (L.pow (a*n)).sheaf :=
  (twistIdealPowerIso L J a b n).hom ≫
    tensorInclusion (J.pow (b*n)) (L.pow (a*n)) (idealPowerInclusion J ι (b*n))

def twistedIdealPowerFrame (L J : LineBundle X) (a b n : ℕ) (U : X.Opens)
    (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : (L.pow (a*n)).sheaf.restrict U.ι ≅ O U.toScheme) :
    ((((L.pow a).tensor (J.pow b)).pow n).sheaf).restrict U.ι ≅ O U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (twistIdealPowerIso L J a b n) ≪≫
    tensorFrame (J.pow (b*n)) (L.pow (a*n)) U (idealPowerFrame J U e (b*n)) f

end
end MaximalSeshadri.Geometry

end


end OAI
end


