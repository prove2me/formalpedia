-- Prove2me | Definitions.Def_Q223SES009
-- name    : Q223SES009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:04:46.426901+00:00
-- url     : https://prove2.me/theorems/56deaf0c-237c-4667-84a1-a3690892f884
-- title:
--   Definitions bundle Q223SES009 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 9 definitions, 2 instances and 71 theorems. The definitions and types are `OAI.MaximalSeshadri.Projective.augmentedQuartics`, `OAI.MaximalSeshadri.Projective.centeredOpen`, `OAI.MaximalSeshadri.Projective.doublePointQuarticIdeal`, `OAI.MaximalSeshadri.Projective.sectionIdeal`, `OAI.MaximalSeshadri.Projective.sectionsMorphism`, `OAI.MaximalSeshadri.Projective.shiftedSections`, `OAI.MaximalSeshadri.PullbackTensor.iso`, `OAI.MaximalSeshadri.PullbackTensor.powIso`, `OAI.MaximalSeshadri.TensorPure.tensorSection`.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: [`Seshadri_Cohomology_MixedLocalExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedLocalExtension.lean), [`Seshadri_Divisors_CenteredSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CenteredSections.lean), [`Seshadri_Divisors_SectionIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionIdeal.lean), [`Seshadri_Projective_GlobalQuartic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/GlobalQuartic.lean), [`Seshadri_Projective_HyperplaneSection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/HyperplaneSection.lean), [`Seshadri_Projective_PullbackProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/PullbackProjective.lean), [`Seshadri_Projective_QuarticReindex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticReindex.lean), [`Seshadri_Projective_QuarticSubsystem`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticSubsystem.lean), [`Seshadri_Projective_SectionMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/SectionMaps.lean), [`Seshadri_Sheaves_LinePullbackTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/LinePullbackTensor.lean), [`Seshadri_Sheaves_TensorOpenSection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorOpenSection.lean).
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`; the bundles `Q223SES007` and `Q223SES008` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_integral_nodal_section_framed_etale`, `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_integral`, `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_smooth_integral_away`, `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_smooth_integral_away_s01`, `OAI_MaximalSeshadri_Geometry_Surface_coprime_embedding_option`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01`, `OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01`, `OAI_MaximalSeshadri_Geometry_Surface_exists_finite_projection`, `OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01`, `OAI_MaximalSeshadri_Geometry_finite_projection_H0_finite`, `OAI.MaximalSeshadri.Geometry.finite_projection_H0_finite_s01`, `OAI_MaximalSeshadri_Geometry_finite_projection_H1_finite`, `OAI.MaximalSeshadri.Geometry.finite_projection_H1_finite_s01`, `OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_eq_mixedEuler_s01`, `OAI_MaximalSeshadri_Geometry_generated_curveDegree_of_power_iso`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01`, `OAI_MaximalSeshadri_Geometry_generated_power_euler_difference`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI_MaximalSeshadri_Geometry_generated_section_H2_untwist`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01`, `OAI_MaximalSeshadri_Geometry_generated_twist_euler_difference`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01`, `OAI_MaximalSeshadri_Geometry_maximal_cartier_extraction_of_iso`, `OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_H1_le`, `OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite`, `OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_power_euler`, `OAI.MaximalSeshadri.Geometry.projective_curve_power_euler_s01`, `OAI_MaximalSeshadri_Geometry_projective_nodal_degree_bound`, `OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound_s01`, `OAI.MaximalSeshadri.Geometry.projective_section_euler_difference_s01`, `OAI_MaximalSeshadri_Geometry_projective_section_positive_degree`, `OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01`, `OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01`, `OAI_MaximalSeshadri_Projective_doublePointQuartics_bertini`, `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01`, `OAI_MaximalSeshadri_Projective_exists_centered_rational_jet_in_open`, `OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01`, `OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01`, `OAI.MaximalSeshadri.Projective.finite_plane_H1_s01`, `OAI.MaximalSeshadri.Projective.finite_plane_cokernel_s01`, `OAI.MaximalSeshadri.Projective.planeVertex_finite_generators_s01`, `OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one_s01` and `OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01`; the proofs of `OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_cohomology_zero_above_one`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.cohomology_zero_above_one_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_degree_nonneg_of_restriction`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.degree_nonneg_of_restriction_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01`, `OAI_MaximalSeshadri_Geometry_IsBlowup_ample_exceptional_twist`, `OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist_s01`, `OAI_MaximalSeshadri_Geometry_IsBlowup_eventual_ample_power_twist`, `OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01`, `OAI_MaximalSeshadri_Geometry_PointBlowup_effective_twist_bound`, `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01`, `OAI_MaximalSeshadri_Geometry_Surface_H0_finite`, `OAI.MaximalSeshadri.Geometry.Surface.H0_finite_s01`, `OAI_MaximalSeshadri_Geometry_Surface_H1_finite`, `OAI.MaximalSeshadri.Geometry.Surface.H1_finite_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_exceptional_square_squeeze`, `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_integral_nodal_section_framed_etale`, `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_integral`, `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral_s01`, `OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_smooth_integral_away`, `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_smooth_integral_away_s01`, `OAI_MaximalSeshadri_Geometry_Surface_blowup_intersections`, `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01`, `OAI_MaximalSeshadri_Geometry_Surface_cohomology_finite`, `OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01`, `OAI_MaximalSeshadri_Geometry_Surface_coprime_embedding_option`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01`, `OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01`, `OAI_MaximalSeshadri_Geometry_Surface_effective_mixed_nonneg`, `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventual_etale_affine_section_test`, `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_arbitrary_jet_frames`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_jets`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI_MaximalSeshadri_Geometry_Surface_exists_all_section_quadrilateral_etale`, `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01`, `OAI_MaximalSeshadri_Geometry_Surface_exists_finite_projection`, `OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01`, `OAI_MaximalSeshadri_Geometry_Surface_lineBundle_cohomology_zero_above_two`, `OAI.MaximalSeshadri.Geometry.Surface.lineBundle_cohomology_zero_above_two_s01`, `OAI_MaximalSeshadri_Geometry_Surface_pointBlowup_exists`, `OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01`, `OAI_MaximalSeshadri_Geometry_Surface_positive_square_eventually_effective`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI_MaximalSeshadri_Geometry_Surface_power_H0_quadratic_upper`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI_MaximalSeshadri_Geometry_Surface_power_H2_bounded`, `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01`, `OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_general`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01`, `OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_pow`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01`, `OAI_MaximalSeshadri_Geometry_Surface_seshadri_eq_of_curve_lower`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01`, `OAI_MaximalSeshadri_Geometry_Surface_square_squeeze_of_sections`, `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01`, `OAI_MaximalSeshadri_Geometry_curveDegree_pow`, `OAI.MaximalSeshadri.Geometry.curveDegree_pow_s01`, `OAI_MaximalSeshadri_Geometry_curveDegree_tensor`, `OAI.MaximalSeshadri.Geometry.curveDegree_tensor_s01`, `OAI_MaximalSeshadri_Geometry_curve_lower_of_homogeneous_section_test`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI_MaximalSeshadri_Geometry_finite_projection_H0_finite`, `OAI.MaximalSeshadri.Geometry.finite_projection_H0_finite_s01`, `OAI_MaximalSeshadri_Geometry_finite_projection_H1_finite`, `OAI.MaximalSeshadri.Geometry.finite_projection_H1_finite_s01`, `OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_eq_mixedEuler_s01`, `OAI_MaximalSeshadri_Geometry_generated_curveDegree_of_power_iso`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01`, `OAI_MaximalSeshadri_Geometry_generated_power_euler_difference`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI_MaximalSeshadri_Geometry_generated_section_H2_untwist`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01`, `OAI_MaximalSeshadri_Geometry_generated_twist_euler_difference`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, `OAI_MaximalSeshadri_Geometry_maximal_cartier_extraction_of_iso`, `OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right`, `OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general_s01`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01`, `OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_right_general`, `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_right_general_s01`, `OAI_MaximalSeshadri_Geometry_nodal_ideal_branch_sum_le_degree`, `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_H1_le`, `OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite`, `OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01`, `OAI_MaximalSeshadri_Geometry_projective_curve_power_euler`, `OAI.MaximalSeshadri.Geometry.projective_curve_power_euler_s01`, `OAI_MaximalSeshadri_Geometry_projective_nodal_degree_bound`, `OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound_s01`, `OAI.MaximalSeshadri.Geometry.projective_section_euler_difference_s01`, `OAI_MaximalSeshadri_Geometry_projective_section_positive_degree`, `OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01`, `OAI_MaximalSeshadri_Geometry_section_bound_of_curve_bound`, `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01`, `OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01`, `OAI_MaximalSeshadri_Projective_doublePointQuartics_bertini`, `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01`, `OAI_MaximalSeshadri_Projective_exists_centered_rational_jet_in_open`, `OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01`, `OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01`, `OAI.MaximalSeshadri.Projective.finite_plane_H1_s01`, `OAI.MaximalSeshadri.Projective.finite_plane_cokernel_s01`, `OAI.MaximalSeshadri.Projective.planeVertex_finite_generators_s01`, `OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one_s01` and `OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007
import Definitions.Def_Q223SES008

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

def sectionsMorphism {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s
    (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover)
    (fun i => sectionFrame (s i)) id (fun i => sectionFrame_normalized (s i))).morphism

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma sectionsMorphism_local {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (i : σ) :
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hcover =
      coordinatesMap (SectionOpens.isoOpen (s i)).toScheme
        ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) i
        (sectionFrame_normalized (s i)) := by
  exact CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s
      (X.openCoverOfIsOpenCover (fun a => SectionOpens.isoOpen (s a)) hcover)
      (fun a => sectionFrame (s a)) id (fun a => sectionFrame_normalized (s a))) i

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplaneSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K σ : Type u} [CommRing K] [Fintype σ] {X : Scheme.{u}}

theorem sectionsMorphism_hyperplane {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (t : σ → K) :
    sectionsMorphism k s hcover ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation t) =
      SectionOpens.isoOpen (sectionCombination k s t) := by
  classical
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (PolyGrade K σ) (linearEquation t)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (sectionCombination k s t) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_hyperplane, preimage_isoOpen (sectionCombination k s t) U.ι
        (sectionFrame (s i))]
    congr 1
    simp only [sectionCombination, restrictSection_sum, coefficient_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (coefficient_restrict_scalar_comp U.ι (sectionFrame (s i)) (k (t j)) (s j)).symm
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def sectionIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) : X.IdealSheafData :=
  (ambientHyperplane v).comap (sectionsMorphism k s hs)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_PullbackProjective
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

lemma pullback_isoOpen_le {M : X.Modules} (s : O X ⟶ M) (f : Y ⟶ X) :
    f ⁻¹ᵁ SectionOpens.isoOpen s ≤ SectionOpens.isoOpen (pullbackSection f s) := by
  let U := SectionOpens.isoOpen s
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame s)
  have hn : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  have hp : (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) = ⊤ := by
    rw [preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι e, hn]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  intro x hx
  have h : (⟨x,hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈
      (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) := by rw [hp]; trivial
  exact h

lemma pullback_sections_cover {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (f : Y ⟶ X) :
    (⨆ i, SectionOpens.isoOpen (pullbackSection f (s i))) = ⊤ := by
  apply top_le_iff.mp
  rw [← Scheme.Hom.preimage_top f, ← hs, Scheme.Hom.preimage_iSup]
  exact iSup_mono fun i => pullback_isoOpen_le (s i) f

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_MixedLocalExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

attribute [local instance] MaximalSeshadri.TensorPure.sectionModule

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def tensorSection {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) :
    O X ⟶ moduleTensor X M N :=
  (moduleTensorUnit (O X)).inv ≫ moduleTensorMap s t

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CenteredSections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

attribute [local instance] OAI.MaximalSeshadri.Projective.instDecidableEq_solutions
def shiftedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (c : σ → K) (i : Option σ) : O X ⟶ M :=
  sectionCombination k s (shiftCoefficients c i)

lemma shiftedSections_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (c : σ → K) (i : Option σ) :
    (sectionsMorphism k s hs ≫ (projectiveShift c).hom) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade K (Option σ)) (MvPolynomial.X i) =
        SectionOpens.isoOpen (shiftedSections k s c i) := by
  rw [Scheme.Hom.comp_preimage]
  change sectionsMorphism k s hs ⁻¹ᵁ
    (Proj.map (projectiveShiftHom c) (shift_irrelevant c) ⁻¹ᵁ _) = _
  rw [Proj.map_preimage_basicOpen, projectiveShiftHom_X,
    ← linearEquation_shiftCoefficients, sectionsMorphism_hyperplane]
  rfl

lemma shiftedSections_cover {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (c : σ → K) : (⨆ i, SectionOpens.isoOpen (shiftedSections k s c i)) = ⊤ := by
  simp_rw [← shiftedSections_preimage k s hs c]
  rw [← Scheme.Hom.preimage_iSup, projective_coordinate_cover, Scheme.Hom.preimage_top]

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_QuarticSubsystem
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma doublePointQuartics_pure {M : X.Modules} (s : Option σ → (O X ⟶ M)) (i : σ) :
    doublePointQuartics s (i,i,some i,some i) = powerSection (s (some i)) 4 :=
  quarticSection_pure _

def centeredOpen {M : X.Modules} (s : Option σ → (O X ⟶ M)) : X.Opens :=
  ⨆ i : σ, SectionOpens.isoOpen (s (some i))

lemma restricted_centered_cover {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    (⨆ i : σ, SectionOpens.isoOpen (restrictSection (centeredOpen s).ι (s (some i)))) = ⊤ := by
  simp_rw [isoOpen_restrictSection]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

lemma doublePointQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i : σ, SectionOpens.isoOpen (s (some i))) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (doublePointQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  calc
    SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) := sectionOpen_le_powerSection _ _
    _ = SectionOpens.isoOpen (doublePointQuartics s (i,i,some i,some i)) := by
      exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
    _ ≤ (⨆ j : QuarticIndex σ, SectionOpens.isoOpen (doublePointQuartics s j)) :=
      le_iSup (fun j : QuarticIndex σ => SectionOpens.isoOpen (doublePointQuartics s j)) (i,i,some i,some i)

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_GlobalQuartic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def augmentedQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    Option (QuarticIndex σ) → (O X ⟶ modulePow X M 4)
  | none => powerSection (s none) 4
  | some j => doublePointQuartics s j

omit [Fintype σ] in
lemma augmentedQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (augmentedQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  cases i with
  | none =>
    exact (sectionOpen_le_powerSection (s none) 4).trans
      (le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) none)
  | some i =>
    calc
      SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) :=
        sectionOpen_le_powerSection _ _
      _ = SectionOpens.isoOpen (augmentedQuartics s (some (i,i,some i,some i))) := by
        exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
      _ ≤ _ := le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) _

def doublePointQuarticIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → K) : X.IdealSheafData :=
  sectionIdeal k (augmentedQuartics s) (augmentedQuartics_cover s hs) (fun j => j.elim 0 v)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_QuarticReindex
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

variable {K σ τ : Type} [CommRing K] {X : Scheme}

lemma sections_cover_reindex {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (e : τ ≃ σ) :
    (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤ := by
  apply le_antisymm le_top
  rw [← hs]
  refine iSup_le (fun i => ?_)
  obtain ⟨j, rfl⟩ := e.surjective i
  exact le_iSup (fun j : τ => SectionOpens.isoOpen (s (e j))) j

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_LinePullbackTensor
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply ModuleLocal.isIso_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1,hx,?_⟩
  have := framed_isIso (f ∣_ U.1) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U.1).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).hom.app M.sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U.1).app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).app M.sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U.1 L.sheaf M.sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U.1).hom.app (moduleTensor Y L.sheaf M.sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U.1).hom.app
      (moduleTensor Y L.sheaf M.sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (L M : LineBundle Y) :
    (Scheme.Modules.pullback f).obj (L.tensor M).sheaf ≅
      ((L.pullback f).tensor (M.pullback f)).sheaf :=
  @asIso X.Modules _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => iso f L (L.pow n) ≪≫ moduleTensorIso (Iso.refl _) (powIso L n)

end
end MaximalSeshadri.PullbackTensor

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorOpenSection
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

instance tensorSection_isIso {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N)
    [IsIso s] [IsIso t] : IsIso (tensorSection s t) := by
  let unitIso : moduleTensor X (O X) (O X) ≅ O X := moduleTensorUnit (O X)
  let tensorMap : moduleTensor X (O X) (O X) ⟶ moduleTensor X M N :=
    moduleTensorMap s t
  have : IsIso tensorMap := moduleTensorMap_isIso (X := X) s t
  change IsIso (unitIso.inv ≫ tensorMap)
  infer_instance

end
end MaximalSeshadri.TensorPure

end

end OAI
end


