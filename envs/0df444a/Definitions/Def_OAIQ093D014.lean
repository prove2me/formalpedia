-- Prove2me | Definitions.Def_OAIQ093D014
-- name    : OAIQ093D014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:08:12.76217+00:00
-- url     : https://prove2.me/theorems/f33cfdfa-391a-431e-8a5e-419564736d73
-- title:
--   Definitions bundle OAIQ093D014 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 32 definitions, 1 inductive type or structure, 2 instances and 68 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths`, `OAI.PolycyclicRecognition.CartanWordModel.samplingPolytope`, `OAI.PolycyclicRecognition.ComplexCartan.instNormedAddCommGroup_solutions`, `OAI.PolycyclicRecognition.ComplexCartan.instNormedSpaceComplex_solutions`, `OAI.PolycyclicRecognition.ComplexCartan.instNormedSpaceReal_solutions`, `OAI.PolycyclicRecognition.ComplexCartan.semisimpleOperator`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.complexWeightCorrectedOperator`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.liftRotationCharacter`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightCorrectedOperator`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightRotationCharacter`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationCharacter`, `OAI.PolycyclicRecognition.DerivationLieSpace`, `OAI.PolycyclicRecognition.HasPolynomialSemidirectCoordinates`, `OAI.PolycyclicRecognition.abelianPolynomialCoordinates`, `OAI.PolycyclicRecognition.actionComplexNormedAddCommGroup`, `OAI.PolycyclicRecognition.actionComplexNormedSpace`, `OAI.PolycyclicRecognition.chosenIntegralPresentation`, `OAI.PolycyclicRecognition.complexNormedAddCommGroup`, `OAI.PolycyclicRecognition.complexNormedSpace`, `OAI.PolycyclicRecognition.complexRealNormedSpace`, `OAI.PolycyclicRecognition.coordinateMatrixDifferential`, `OAI.PolycyclicRecognition.inducedExhaustionDiagram`, `OAI.PolycyclicRecognition.instLieRingProdReal_solutions`, `OAI.PolycyclicRecognition.polynomialCoordinateLieModel`, `OAI.PolycyclicRecognition.polynomialModelLetters`, `OAI.PolycyclicRecognition.polynomialModelLieHom`, `OAI.PolycyclicRecognition.polynomialModelProduct`, `OAI.PolycyclicRecognition.realNormedSpace`, `OAI.PolycyclicRecognition.realPhaseHom`, `OAI.PolycyclicRecognition.realPhaseVector`, `OAI.PolycyclicRecognition.semidirectIdealInclusion`, `OAI.PolycyclicRecognition.semidirectIdealLieHom`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AbelianDynkinInput`, `PolycyclicRecognition_Algebra_AbelianPolynomialCoordinates`, `PolycyclicRecognition_Algebra_CommonDynkinFormula`, `PolycyclicRecognition_Algebra_CoordinateMatrixRepresentation`, `PolycyclicRecognition_Algebra_DynkinIntegration`, `PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm`, `PolycyclicRecognition_Algebra_HomogeneousWordCoefficients`, `PolycyclicRecognition_Algebra_NilpotentIntegrationConstruction`, `PolycyclicRecognition_Algebra_PolynomialCoordinateCurves`, `PolycyclicRecognition_Algebra_PolynomialCurveOperations`, `PolycyclicRecognition_Algebra_PolynomialModelHom`, `PolycyclicRecognition_Algebra_PolynomialModelRepresentation`, `PolycyclicRecognition_Algebra_RealTorusContinuity`, `PolycyclicRecognition_Algebra_UnconditionalNilpotentModel`, `PolycyclicRecognition_Algebra_UniversalDynkinTruncation`, `PolycyclicRecognition_Finiteness_FiniteProjectivePresentations`, `PolycyclicRecognition_Finiteness_InductionExhaustionVanishing`, `PolycyclicRecognition_Geometry_BoundedAssociativeBCH`, `PolycyclicRecognition_Geometry_CartanPolarProbeTemplates`, `PolycyclicRecognition_Geometry_CartanSamplingNonzero`, `PolycyclicRecognition_Geometry_CartanSamplingParameters`, `PolycyclicRecognition_Geometry_ComplexCartanJordan`, `PolycyclicRecognition_Geometry_ComplexPhaseDerivative`, `PolycyclicRecognition_Geometry_ComplexRotationDerivation`, `PolycyclicRecognition_Geometry_ComplexRotationTorus`, `PolycyclicRecognition_Geometry_ComplexWeightFactorModel`, `PolycyclicRecognition_Geometry_DerivationLieSpace`, `PolycyclicRecognition_Geometry_ExponentialSmoothHom`, `PolycyclicRecognition_Geometry_FactorRotationCharacter`, `PolycyclicRecognition_Geometry_FaithfulRepresentationBCH`, `PolycyclicRecognition_Geometry_FiniteAssociativeBCH`, `PolycyclicRecognition_Geometry_IntegratedCartanRotations`, `PolycyclicRecognition_Geometry_IntegratedNilradicalRotations`, `PolycyclicRecognition_Geometry_NilpotentDerivationFlowDerivative`, `PolycyclicRecognition_Geometry_NilpotentSemidirectTangent`, `PolycyclicRecognition_Geometry_NilradicalRotationAction`, `PolycyclicRecognition_Geometry_NormedLiePolynomial`, `PolycyclicRecognition_Geometry_RealCartanRotations`, `PolycyclicRecognition_Geometry_RealRotationTorus`, `PolycyclicRecognition_Geometry_RealShadowOperators`, `PolycyclicRecognition_Geometry_RealTorusAdjoint`, `PolycyclicRecognition_Geometry_SemidirectCoordinateOrbit`, `PolycyclicRecognition_Geometry_SemidirectIntegration`, `PolycyclicRecognition_Geometry_SemidirectPolynomialCurves`, `PolycyclicRecognition_Geometry_SemidirectPolynomialMaps`, `PolycyclicRecognition_Geometry_SmoothCoordinateAction`, `PolycyclicRecognition_Geometry_UnipotentCoordinateBCH`, `PolycyclicRecognition_Geometry_WeightRotationCharacter`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D006`, `OAIQ093D007`, `OAIQ093D008`, `OAIQ093D009` and `OAIQ093D010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D017` and `OAIQ093D018`; the statements `OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration` and `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration` and `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009
import Definitions.Def_OAIQ093D010

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianDynkinInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite BCH for commutative Lie groups -/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_abelian {c n : ℕ} (hc : 0 < c) (X : Fin n → L) :
    finiteDynkinPolynomial (abelianDynkinCoefficients c n) X = ∑ i, X i := by
  let z : Fin c := ⟨0, hc⟩
  unfold finiteDynkinPolynomial
  rw [Finset.sum_eq_single z]
  · change (∑ w : Fin 1 → Fin n, (1 : ℝ) • X (w 0)) = ∑ i, X i
    simp only [one_smul]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun _ => rfl)
  · intro d _ hdz
    have hd : d.val ≠ 0 := fun h => hdz (Fin.ext h)
    simp [abelianDynkinCoefficients, hd]
  · simp

/-- The published BCH input is fully proved for commutative Lie groups. -/
theorem nilpotentDynkinExpansionInput_of_comm [FiniteDimensional ℝ E] :
    NilpotentDynkinExpansionInput E G := by
  intro Exp hExp c hc n
  refine ⟨abelianDynkinCoefficients c n, abelianDynkinCoefficients_bound c n, ?_⟩
  intro X
  by_cases hz : c = 0
  · subst c
    have htop : (⊤ : LieSubmodule ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
        (GroupLieAlgebra (𝓘(ℝ, E)) G)) = ⊥ := by simpa using hc
    have hx (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : x = 0 := by
      have hm : x ∈ (⊥ : LieSubmodule ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
          (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by rw [← htop]; exact LieSubmodule.mem_top x
      exact hm
    have hX : X = 0 := funext fun i => hx (X i)
    rw [hX]
    simp [finiteDynkinPolynomial, hExp.map_zero]
  · rw [finiteDynkinPolynomial_abelian (Nat.pos_of_ne_zero hz)]
    exact hExp.prod_eq_exp_sum_of_comm X

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormedLiePolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth Lie polynomials in a compatible finite-dimensional norm -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V I : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_normed_evalBracketWord (X : V → I → L)
    (hX : ∀ i, ContDiff ℝ r (fun v => X v i)) (w : FreeMagma I) :
    ContDiff ℝ r (fun v => evalBracketWord (X v) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv =>
    exact ((normedLieBracket (L := L)).contDiff.comp hu).clm_apply hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialSmoothHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness and differential of exponential-compatible homomorphisms

Coordinates of the second kind reduce smoothness to the individual
one-parameter subgroups. This applies to arbitrary finite-dimensional Lie
group targets and does not assume a linear representation of the target.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

theorem contMDiffAt_one_of_exponential_compatibility [FiniteDimensional ℝ E]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : Continuous φ) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ 1 := by
  let b := Module.finBasis ℝ E
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct ExpG b) 0 d.toContinuousLinearMap := by
    apply (hG.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hp : ContMDiff (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, F)) ∞
      (φ ∘ exponentialProduct ExpG b) := by
    have heq : φ ∘ exponentialProduct ExpG b =
        exponentialProduct ExpH (fun i => j (b i)) := by
      funext x
      exact map_exponentialProduct φ j hcompat b x
    rw [heq]
    exact hH.contMDiff_exponentialProduct _
  have he : (φ ∘ exponentialProduct ExpG b) 0 = φ 1 := by
    simp only [Function.comp_apply, hG.exponentialProduct_zero]
  have hc : ContDiffAt ℝ ∞
      ((extChartAt (𝓘(ℝ, F)) (φ 1) ∘ φ) ∘ exponentialProduct ExpG b) 0 := by
    exact ((contMDiffAt_extChartAt (I := 𝓘(ℝ, F))).comp_of_eq hp.contMDiffAt he).contDiffAt
  have hh := contMDiffAt_of_local_parameterization
    (hG.contMDiff_exponentialProduct b).contMDiffAt hd hc
  apply contMDiffAt_iff_target.mpr
  refine ⟨hφ.continuousAt, ?_⟩
  simpa only [hG.exponentialProduct_zero] using hh

theorem contMDiff_of_exponential_compatibility [FiniteDimensional ℝ E]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : Continuous φ) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ := by
  have hbase := contMDiffAt_one_of_exponential_compatibility hG hH φ hφ j hcompat
  intro g
  have hl : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x)).contMDiffAt
  have hm := hbase.comp_of_eq hl (inv_mul_cancel g)
  have hh := (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
    ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ (fun y : H => φ g * y)).contMDiffAt.comp g hm
  have heq : (fun x => φ g * φ (g⁻¹ * x)) = φ := by
    funext x
    rw [← map_mul, mul_inv_cancel_left]
  change ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ (fun x => φ g * φ (g⁻¹ * x)) g at hh
  rwa [heq] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianPolynomialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit additive polynomial coordinates for an abelian Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [IsLieAbelian L]

@[instance_reducible]
def abelianPolynomialCoordinates : PolynomialExponentialCoordinates L := by
  let N := abelianLieModel (V := L)
  refine
    { group := inferInstanceAs (Group (Multiplicative L))
      lieGroup := N.lieGroup
      one_eq_zero := rfl
      inv_eq_neg := fun _ => rfl
      degree := 1
      coefficients := abelianDynkinCoefficients 1 2
      mul_eq := ?_
      tangentEquiv := N.equiv
      tangentEquiv_apply := fun _ => rfl }
  intro x y
  change x + y = finiteDynkinPolynomial (abelianDynkinCoefficients 1 2) ![x, y]
  rw [finiteDynkinPolynomial_abelian (by decide)]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonDynkinFormula
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common BCH formula for two nilpotent Lie groups

Apply the published finite Dynkin identity once to the product group, then
project to each factor. The projections preserve the actual tangent bracket.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

attribute [local instance] productSelfChartedSpace

variable {E G F H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] [T2Space H]

theorem exists_common_dynkin_formula
    (hG : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (hH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H))
    (dynkin : NilpotentDynkinExpansionInput (E × F) (G × H))
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hExpG : IsGroupExponential ExpG) (hExpH : IsGroupExponential ExpH) :
    ∃ c : ℕ, ∃ coeff : DynkinCoefficients c 2,
      (∀ x y, ExpG x * ExpG y = ExpG (finiteDynkinPolynomial coeff ![x, y])) ∧
      (∀ x y, ExpH x * ExpH y = ExpH (finiteDynkinPolynomial coeff ![x, y])) := by
  have hn := product_tangent_nilpotent hG hH
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hn
  let ExpP : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) → G × H := groupExponential
  have hExpP : IsGroupExponential ExpP := groupExponential_isGroupExponential
  have hfst (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
      (ExpP v).1 = ExpG (productFstLieHom (E := E) (F := F) (G := G) (H := H) v) :=
    hExpP.map_of_mdifferentiable hExpG (MonoidHom.fst G H)
      (contMDiff_product_fst.mdifferentiable (by simp)) v
  have hsnd (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
      (ExpP v).2 = ExpH (productSndLieHom (E := E) (F := F) (G := G) (H := H) v) :=
    hExpP.map_of_mdifferentiable hExpH (MonoidHom.snd G H)
      (contMDiff_product_snd.mdifferentiable (by simp)) v
  obtain ⟨coeff, _, hprod⟩ := dynkin ExpP hExpP c hc 2
  refine ⟨c, coeff, ?_, ?_⟩
  · intro x y
    let X : Fin 2 → GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) := ![(x, 0), (y, 0)]
    have hp := congrArg Prod.fst (hprod X)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Prod.fst_mul] at hp
    rw [hfst, hfst, hfst, finiteDynkinPolynomial_map] at hp
    have hX : (fun i => productFstLieHom (E := E) (F := F) (G := G) (H := H) (X i)) =
        ![x, y] := by
      funext i
      rw [productFstLieHom_apply]
      fin_cases i <;> rfl
    rw [hX] at hp
    simp only [productFstLieHom_apply] at hp
    rw [show (X 0).1 = x from rfl, show (X (Fin.succ 0)).1 = y from rfl] at hp
    exact hp
  · intro x y
    let X : Fin 2 → GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) := ![(0, x), (0, y)]
    have hp := congrArg Prod.snd (hprod X)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Prod.snd_mul] at hp
    rw [hsnd, hsnd, hsnd, finiteDynkinPolynomial_map] at hp
    have hX : (fun i => productSndLieHom (E := E) (F := F) (G := G) (H := H) (X i)) =
        ![x, y] := by
      funext i
      rw [productSndLieHom_apply]
      fin_cases i <;> rfl
    rw [hX] at hp
    simp only [productSndLieHom_apply] at hp
    rw [show (X 0).2 = x from rfl, show (X (Fin.succ 0)).2 = y from rfl] at hp
    exact hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothCoordinateAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth finite-dimensional actions from coordinate translates

This construction needs smooth coordinate functions, without assuming that
straight lines are exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {G I W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Group G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (q : I → G → ℝ) (B : W ≃ₗ[ℝ] coordinateOrbitSpan q)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_smoothCoordinateAction (γ : ℝ → G)
    (hγ : ∀ a b i, (fun t => q i ((a * γ t) * b)) ∈ polynomialFunctions)
    (v : W) (f : Module.Dual ℝ W) :
    (fun t => f (smoothCoordinateAction q B (γ t) v)) ∈ polynomialFunctions := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply polynomial_of_coordinateEvaluations e (Subtype.coe_injective.comp B.injective) _ ?_ f
  intro a
  change (fun t => (B (smoothCoordinateAction q B (γ t) v) : G → ℝ) a) ∈ polynomialFunctions
  simp only [smoothCoordinateAction_eval]
  have hfun (u : G → ℝ) (hu : u ∈ coordinateOrbitSpan q) :
      (fun t => u (a * γ t)) ∈ polynomialFunctions := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨⟨b, i⟩, rfl⟩ := hu
      exact hγ a b i
    | zero => exact polynomialFunctions.zero_mem
    | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
    | smul c f _ hf => exact polynomialFunctions.smul_mem c hf
  exact hfun _ (B v).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMatrixRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix representations from finite-dimensional coordinate orbits -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {G I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G] {m : ℕ}
  (q : I → G → ℝ) (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

def coordinateMatrixDifferential (hq : ∀ i, ContDiff ℝ ∞ (q i)) :
    GroupLieAlgebra (𝓘(ℝ, G)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ :=
  unitsHomLieDifferential (coordinateMatrixRepresentation q B)
    (contDiff_coordinateMatrixRepresentation q B hq).contMDiff

theorem coordinateMatrixDifferential_injective (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (hi : Function.Injective (fun g => fun i => q i g)) :
    Function.Injective (coordinateMatrixDifferential q B hq) :=
  injective_algebra_differential groupExponential_isGroupExponential
    (coordinateMatrixRepresentation q B) (coordinateMatrixRepresentation_injective q B hi)
    (coordinateMatrixDifferential q B hq).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (coordinateMatrixRepresentation q B)
      (contDiff_coordinateMatrixRepresentation q B hq).contMDiff)

theorem coordinateMatrixDifferential_exp (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (v : GroupLieAlgebra (𝓘(ℝ, G)) G) :
    coordinateMatrixRepresentation q B (groupExponential v) =
      algebraExpUnit (coordinateMatrixDifferential q B hq v) :=
  hom_exp_eq_algebraExpUnit groupExponential_isGroupExponential
    (coordinateMatrixRepresentation q B) (coordinateMatrixDifferential q B hq).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (coordinateMatrixRepresentation q B)
      (contDiff_coordinateMatrixRepresentation q B hq).contMDiff) v

theorem coordinateMatrixDifferential_nilpotent (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (v : GroupLieAlgebra (𝓘(ℝ, G)) G)
    (hγ : ∀ a b i, (fun t : ℝ => q i ((a * groupExponential (t • v)) * b)) ∈ polynomialFunctions) :
    IsNilpotent (coordinateMatrixDifferential q B hq v) := by
  let A := coordinateMatrixDifferential q B hq v
  let f : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => (coordinateMatrixRepresentation q B (groupExponential (t • v)) : Matrix (Fin m) (Fin m) ℝ)
  have hf0 : f 0 = 1 := by simp [f, groupExponential_isGroupExponential.map_zero]
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp [f]
    rw [groupExponential_isGroupExponential.map_add_smul, map_mul]
    rfl
  have heq : f = fun t => NormedSpace.exp (t • A) := by
    funext t
    have h := congrArg Units.val (coordinateMatrixDifferential_exp q B hq (t • v))
    simp only [coe_algebraExpUnit, map_smul] at h
    exact h
  have hzero : HasDerivAt f A 0 := by
    rw [heq]
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  apply isNilpotent_of_polynomial_oneParameter hf0 hadd hzero
  intro i j
  exact mem_polynomialFunctions_iff.mp
    (polynomial_smoothCoordinateAction q B _ hγ (Pi.single j 1) (LinearMap.proj i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration from a common finite BCH formula

A common two-factor BCH formula for the source and target makes
exponential conjugation of a Lie algebra homomorphism multiplicative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]
  (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
  (cH : GroupLieAlgebra (𝓘(ℝ, F)) H ≃ₜ H)
  (hG : IsGroupExponential cG) (hH : IsGroupExponential cH)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hprodG : ∀ x y, cG x * cG y = cG (finiteDynkinPolynomial coeff ![x, y]))
  (hprodH : ∀ x y, cH x * cH y = cH (finiteDynkinPolynomial coeff ![x, y]))
  (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, F)) H)

theorem continuous_exponentialHomOfDynkin :
    Continuous (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) :=
  cH.continuous.comp (j.toLinearMap.continuous_of_finiteDimensional.comp cG.symm.continuous)

theorem contMDiff_exponentialHomOfDynkin :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞
      (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) :=
  contMDiff_of_exponential_compatibility hG hH _
    (continuous_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j)
    j.toLinearMap (exponentialHomOfDynkin_apply_exp cG cH hG hH coeff hprodG hprodH j)

theorem mfderiv_exponentialHomOfDynkin [T2Space H]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F))
      (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) 1 x = j x :=
  mfderiv_eq_of_exponential_compatibility hG hH _
    ((contMDiff_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j).mdifferentiable
      (by simp)) j.toLinearMap
    (exponentialHomOfDynkin_apply_exp cG cH hG hH coeff hprodG hprodH j) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite right-nested coefficients of homogeneous primitive words -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n d : ℕ}

theorem wordLieProjection_homogeneous {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (p : RationalWords n) (hp : IsHomogeneousRationalWord p d) :
    wordLieProjection X p = ∑ w : Fin d → Fin n,
      p.coeff (wordOfFn w) • wordRightLie X (List.ofFn w) := by
  classical
  let s : Finset (FreeMonoid (Fin n)) := Finset.univ.image (wordOfFn (d := d))
  have hs : p.coeff ∈ Finsupp.supported ℚ ℚ (↑s : Set (FreeMonoid (Fin n))) := by
    rw [Finsupp.mem_supported]
    intro w hw
    obtain ⟨f, rfl⟩ := exists_wordOfFn_of_length w (hp w (Finsupp.mem_support_iff.mp hw))
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  change Finsupp.linearCombination ℚ (fun w => wordRightLie X w.toList) p.coeff = _
  rw [Finsupp.linearCombination_apply_of_mem_supported ℚ hs]
  dsimp [s]
  rw [Finset.sum_image]
  · rfl
  · intro f _ g _ h
    exact wordOfFn_injective h

attribute [local instance 100] LieRing.ofAssociativeRing

theorem primitive_word_finite_expansion {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (p : RationalWords n) (hp : IsPrimitiveRationalWord p)
    (hd : IsHomogeneousRationalWord p (d + 1)) :
    rationalWordEvaluation X p = ∑ w : Fin (d + 1) → Fin n,
      ((d + 1 : ℚ)⁻¹ * p.coeff (wordOfFn w)) •
        evalBracketWord X (rightNestedWord d w) := by
  have hc : (d + 1 : ℚ) ≠ 0 := by positivity
  calc
    rationalWordEvaluation X p = (d + 1 : ℚ)⁻¹ • wordLieProjection X p := by
      rw [primitive_homogeneous_word_projection X hp hd, smul_smul]
      simp [hc]
    _ = _ := by
      rw [wordLieProjection_homogeneous X p hd, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [smul_smul, wordRightLie_ofFn]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous Lie expansions of the universal logarithm coefficients -/

noncomputable section
namespace PolycyclicRecognition

variable {n d : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each positive-degree universal logarithm coefficient is a finite Lie polynomial. -/
theorem universalLogarithmCoefficient_lie_expansion {A : Type*} [Ring A] [Algebra ℚ A]
    (c n d : ℕ) (X : Fin n → A) :
    rationalWordEvaluation X (universalLogarithmCoefficient c n (d + 1)) =
      ∑ w : Fin (d + 1) → Fin n,
        ((d + 1 : ℚ)⁻¹ * (universalLogarithmCoefficient c n (d + 1)).coeff (wordOfFn w)) •
          evalBracketWord X (rightNestedWord d w) :=
  primitive_word_finite_expansion X _ (universalLogarithmCoefficient_primitive c n (d + 1))
    (universalLogarithmCoefficient_homogeneous c n (d + 1))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentIntegrationConstruction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration between the nilpotent models used by the application

Global exponential coordinates and one application of the finite Dynkin
identity to the product construct the homomorphism. Its smoothness and
actual differential are proved by exponential curves. The target is
explicitly nilpotent; integration into the ambient solvable group remains
a separate input.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

attribute [local instance] productSelfChartedSpace

variable {E G F H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]
  [T2Space H] [SimplyConnectedSpace H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] in
theorem nilpotentSmoothIntegration_of_coordinates
    (coordinatesG : NilpotentGlobalExponentialChartInput E G)
    (coordinatesH : NilpotentGlobalExponentialChartInput F H)
    (dynkin : ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
      (P : NilpotentLieModel L), NilpotentDynkinExpansionInput P.modelSpace P.carrier)
    (hnilH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H)) :
    NilpotentSmoothIntegrationInput (EN := E) (N := G) (EG := F) (G := H) := by
  intro _ hnilG j
  obtain ⟨cG, hcG⟩ := coordinatesG groupExponential groupExponential_isGroupExponential hnilG
  obtain ⟨cH, hcH⟩ := coordinatesH groupExponential groupExponential_isGroupExponential hnilH
  have hG : IsGroupExponential cG := by
    have heq : (cG : GroupLieAlgebra (𝓘(ℝ, E)) G → G) = groupExponential := funext hcG
    rw [heq]
    exact groupExponential_isGroupExponential
  have hH : IsGroupExponential cH := by
    have heq : (cH : GroupLieAlgebra (𝓘(ℝ, F)) H → H) = groupExponential := funext hcH
    rw [heq]
    exact groupExponential_isGroupExponential
  have hp : NilpotentDynkinExpansionInput (E × F) (G × H) :=
    dynkin _ (exponentialProductLieModel cG cH)
  obtain ⟨c, coeff, hprodG, hprodH⟩ := exists_common_dynkin_formula hnilG hnilH hp hG hH
  refine ⟨exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j,
    contMDiff_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j, ?_⟩
  exact mfderiv_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful finite-dimensional representation in polynomial coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

def polynomialModelLetters : Fin 2 → Fin n → MvPolynomial (Fin n) (L → ℝ) :=
  ![(fun j => MvPolynomial.X j), (fun j => MvPolynomial.C (fun g => b.repr g j))]

def polynomialModelProduct (i : Fin n) : MvPolynomial (Fin n) (L → ℝ) :=
  dynkinCoordinatePolynomial b P.coefficients (polynomialModelLetters b) i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateCurves
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial scalar curves in polynomial group coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L J : Type*} [RealNormedLieAlgebra L] [Fintype J]
  (b : Module.Basis J ℝ L)

theorem hasPolynomialLineCoordinates_dynkin {c n : ℕ} (coeff : DynkinCoefficients c n)
    (F : Fin n → ℝ → L) (hF : ∀ i, HasPolynomialLineCoordinates b (F i)) :
    HasPolynomialLineCoordinates b (fun t => finiteDynkinPolynomial coeff (fun i => F i t)) := by
  have h : ∀ i j, ∃ p : Polynomial ℝ, ∀ t, p.eval t = b.repr (F i t) j :=
    fun i j => mem_polynomialFunctions_iff.mp (hF i j)
  choose p hp using h
  let X : Fin n → J → MvPolynomial Unit ℝ :=
    fun i j => (MvPolynomial.uniqueAlgEquiv ℝ Unit).symm (p i j)
  intro j
  apply mem_polynomialFunctions_iff.mpr
  refine ⟨MvPolynomial.uniqueAlgEquiv ℝ Unit (dynkinCoordinatePolynomial b coeff X j), ?_⟩
  intro t
  rw [Polynomial.eval, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  apply eval_dynkinCoordinatePolynomial b coeff X (AlgHom.id ℝ ℝ)
  intro i k
  change ((MvPolynomial.uniqueAlgEquiv ℝ Unit).symm (p i k)).eval₂ (RingHom.id ℝ) (fun _ => t) = _
  rw [MvPolynomial.eval₂_const_uniqueAlgEquiv_symm, Polynomial.eval₂_id]
  exact hp i k t

section Group

variable [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem hasPolynomialLineCoordinates_mul (F H : ℝ → L)
    (hF : HasPolynomialLineCoordinates b F) (hH : HasPolynomialLineCoordinates b H) :
    HasPolynomialLineCoordinates b (fun t => F t * H t) := by
  have h := hasPolynomialLineCoordinates_dynkin b P.coefficients ![F, H] (by
    intro i
    fin_cases i
    · exact hF
    · exact hH)
  have heq : (fun t => finiteDynkinPolynomial P.coefficients (fun i => ![F, H] i t)) =
      (fun t => F t * H t) := by
    funext t
    rw [P.mul_eq]
    congr 1
    ext i
    fin_cases i <;> rfl
  rwa [heq] at h

end Group

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCurveOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial curves under linear maps and nilpotent derivation flows -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

theorem hasPolynomialLineCoordinates_linear (A : L →ₗ[ℝ] L) (F : ℝ → L)
    (hF : HasPolynomialLineCoordinates b F) :
    HasPolynomialLineCoordinates b (fun t => A (F t)) := by
  intro j
  exact polynomial_of_coordinateEvaluations b.equivFun.toLinearMap b.equivFun.injective F hF
    ((LinearMap.proj j).comp (b.equivFun.toLinearMap.comp A))

attribute [local instance] OAI.PolycyclicRecognition.polynomialCurveModuleRat
theorem hasPolynomialLineCoordinates_derivationFlow
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (f : ℝ → ℝ) (F : ℝ → L) (hf : f ∈ polynomialFunctions)
    (hF : HasPolynomialLineCoordinates b F) :
    HasPolynomialLineCoordinates b (fun t => nilpotentDerivationFlow D hD (f t) (F t)) := by
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  intro j
  have heq : (fun t => b.repr (nilpotentDerivationFlow D hD (f t) (F t)) j) =
      ∑ i ∈ Finset.range k, (fun t => f t ^ i *
        b.repr (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) (F t)) j) := by
    funext t
    rw [nilpotentDerivationFlow_eq_sum D hD hk]
    simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Finset.sum_apply]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact polynomialFunctions_mul (polynomialFunctions_pow hf i)
    (hasPolynomialLineCoordinates_linear b _ F hF j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth homomorphisms in polynomial exponential coordinates are linear -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L K : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates K]

def polynomialModelLieHom (f : L →* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) : L →ₗ⁅ℝ⁆ K :=
  Q.tangentEquiv.symm.toLieHom.comp ((homLieDifferential f hf).comp P.tangentEquiv.toLieHom)

theorem polynomialModelLieHom_apply (f : L →* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) (x : L) :
    polynomialModelLieHom f hf x = f x := by
  have h := PolynomialExponentialCoordinates.isGroupExponential_identity.map_of_mdifferentiable
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := K))
    f (hf.mdifferentiable (by simp)) x
  change f x = mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, K)) f 1 x at h
  have hd : homLieDifferential f hf (P.tangentEquiv x) = Q.tangentEquiv (f x) := by
    rw [P.tangentEquiv_apply, Q.tangentEquiv_apply]
    exact (homLieDifferential_apply f hf x).trans h.symm
  change Q.tangentEquiv.symm
    (homLieDifferential f hf (P.tangentEquiv x)) = f x
  rw [hd, Q.tangentEquiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationTorus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact group containing the Cartan rotations

Diagonal unit scalars are invertible on the generalized weight decomposition.
The equations for preserving the bracket and fixing the Cartan algebra cut out
an actual closed subgroup of a finite torus, giving a compact action.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module Set

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

section Topology

attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.rotationNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.rotationNormedSpace
theorem continuous_torusOperator (x : L) :
    Continuous (fun z : Weight ℂ H L → Circle => torusOperator H z x) := by
  have hc : Continuous (fun z : Weight ℂ H L → Circle => fun χ => (z χ : ℂ)) :=
    continuous_pi (fun χ => continuous_subtype_val.comp (continuous_apply χ))
  exact ((coefficientOperator H).continuous_of_finiteDimensional.comp hc).clm_apply continuous_const

theorem rotationTorus_isClosed : IsClosed (rotationTorus H : Set (Weight ℂ H L → Circle)) := by
  apply IsClosed.inter
  · change IsClosed {z : Weight ℂ H L → Circle | ∀ x y : L,
        torusOperator H z ⁅x, y⁆ = ⁅torusOperator H z x, torusOperator H z y⁆}
    simp_rw [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (continuous_torusOperator H ⁅x, y⁆)
        ((bracketOperator.continuous.comp (continuous_torusOperator H x)).clm_apply
          (continuous_torusOperator H y))))
  · change IsClosed {z : Weight ℂ H L → Circle | ∀ h : H, torusOperator H z h = h}
    simp_rw [ofPred_forall]
    exact isClosed_iInter (fun h => isClosed_eq (continuous_torusOperator H h) continuous_const)

instance rotationTorus_compactSpace : CompactSpace (rotationTorus H) :=
  isCompact_iff_compactSpace.mp (rotationTorus_isClosed H).isCompact

end Topology
end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealCartanRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realImaginaryOperator_complexify _root_.OAI.PolycyclicRecognition.realTorusOperator_complexify _root_.OAI.PolycyclicRecognition.realTorusOperator_mul _root_.OAI.PolycyclicRecognition.realTorusOperator_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan rotations preserve the actual real form -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
theorem phase_conjugate_real (h : H) (χ : complexifiedSubalgebra L H → ℂ) :
    ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (conjugateCartanWeight L H χ) =
      star (ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h) χ) := by
  unfold ComplexCartan.phase conjugateCartanWeight
  rw [cartanConjugation_real]
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp [ComplexCartan.imaginaryPart]

set_option maxHeartbeats 1000000 in
/-- Conjugation commutes with rotations by real Cartan parameters. -/
theorem complex_rotation_conjugation (h : H) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x) := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    rw [ComplexCartan.rotationLinear_apply _ _ χ hv, complexificationConjugation_smul,
      ComplexCartan.rotationLinear_apply_genWeight _ _ (conjugateCartanWeight L H χ)
        (conjugation_mem_genWeightSpace L H χ hv), phase_conjugate_real]
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealRotationTorus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact torus of automorphisms preserving the real form

Commuting with the canonical conjugation is a closed subgroup condition.
The resulting compact subgroup contains every real Cartan rotation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module Set
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

section Topology

local instance complexNormedAddCommGroup : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance complexNormedSpace : NormedSpace ℂ (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedSpace
local instance realNormedSpace : NormedSpace ℝ (ℂ ⊗[ℝ] L) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

/-- Conjugation commutation cuts out a closed subgroup of the compact torus. -/
theorem realRotationTorus_isClosed : IsClosed (realRotationTorus L H : Set (complexCartanTorus L H)) := by
  change IsClosed {z : complexCartanTorus L H | ∀ x : ℂ ⊗[ℝ] L,
    complexificationConjugation L
      (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val x) =
    ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val
      (complexificationConjugation L x)}
  rw [ofPred_forall]
  apply isClosed_iInter
  intro x
  have hc : Continuous (complexificationConjugation L) :=
    (complexificationConjugation L).toLinearMap.continuous_of_finiteDimensional
  exact isClosed_eq
    (hc.comp ((ComplexCartan.continuous_torusOperator (complexifiedSubalgebra L H) x).comp
      continuous_subtype_val))
    ((ComplexCartan.continuous_torusOperator (complexifiedSubalgebra L H)
      (complexificationConjugation L x)).comp continuous_subtype_val)

instance realRotationTorus_compactSpace : CompactSpace (realRotationTorus L H) :=
  isCompact_iff_compactSpace.mp (realRotationTorus_isClosed L H).isCompact

end Topology

/-- The genuine rotations by real Cartan parameters lie in the compact
subgroup preserving the real form. -/
def realPhaseVector (h : H) : realRotationTorus L H := by
  refine ⟨ComplexCartan.phaseVector (complexifiedSubalgebra L H) (realCartanInComplex L H h), ?_⟩
  intro x
  change complexificationConjugation L
    (ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x)
  exact complex_rotation_conjugation L H h x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealTorusContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the real compact rotation action -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Additive Cartan parameters act through the compact rotation group. -/
def realPhaseHom : Multiplicative H →* realRotationTorus L H where
  toFun h := realPhaseVector L H h.toAdd
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext χ
    apply Subtype.ext
    change ComplexCartan.phase (complexifiedSubalgebra L H)
      (realCartanInComplex L H 0) χ = 1
    rw [realCartanInComplex_zero, ComplexCartan.phase_zero]
  map_mul' h k := by
    apply Subtype.ext
    apply Subtype.ext
    funext χ
    apply Subtype.ext
    change ComplexCartan.phase (complexifiedSubalgebra L H)
      (realCartanInComplex L H (h.toAdd + k.toAdd)) χ =
        ComplexCartan.phase (complexifiedSubalgebra L H)
          (realCartanInComplex L H h.toAdd) χ *
        ComplexCartan.phase (complexifiedSubalgebra L H)
          (realCartanInComplex L H k.toAdd) χ
    rw [realCartanInComplex_add, ComplexCartan.phase_add]

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance actionComplexNormedAddCommGroup : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance actionComplexNormedSpace : NormedSpace ℂ (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedSpace
local instance complexRealNormedSpace : NormedSpace ℝ (ℂ ⊗[ℝ] L) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

/-- The compact real torus acts jointly continuously on the real algebra. -/
theorem continuous_realTorusOperator :
    Continuous (fun p : realRotationTorus L H × L => realTorusOperator L H p.1 p.2) := by
  have hc : Continuous (fun z : realRotationTorus L H =>
      fun χ : Weight ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) =>
        (z.val.val χ : ℂ)) :=
    continuous_pi (fun χ => continuous_subtype_val.comp
      ((continuous_apply χ).comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hj : Continuous (complexificationLieHom L) :=
    (complexificationLieHom L).toLinearMap.continuous_of_finiteDimensional
  have hr : Continuous (complexificationRealPart L) :=
    (complexificationRealPart L).continuous_of_finiteDimensional
  exact hr.comp
    ((((ComplexCartan.coefficientOperator (complexifiedSubalgebra L H)).continuous_of_finiteDimensional.comp
      hc).comp continuous_fst).clm_apply (hj.comp continuous_snd))

attribute [local instance] OAI.PolycyclicRecognition.cartanTopologicalAddGroup
/-- Cartan rotations depend continuously on the real Cartan parameter. -/
theorem continuous_realPhaseVector : Continuous (realPhaseVector L H) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro χ
  let j : H →ₗ[ℝ] complexifiedSubalgebra L H :=
    { toFun := realCartanInComplex L H
      map_add' := realCartanInComplex_add L H
      map_smul' := by
        intro r h
        apply Subtype.ext
        exact (complexificationLieHom L).map_smul r (h : L) }
  let f : H →ₗ[ℝ] ℂ :=
    ((χ : complexifiedSubalgebra L H →ₗ[ℂ] ℂ).restrictScalars ℝ).comp j
  exact Circle.exp.continuous.comp (Complex.continuous_im.comp f.continuous_of_finiteDimensional)

end Topology
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentDerivationFlowDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial velocity of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

attribute [local instance] OAI.PolycyclicRecognition.instModuleRat_solutions_2
omit [FiniteDimensional ℝ L] in
theorem hasDerivAt_nilpotentDerivationFlow_zero (x : L) :
    HasDerivAt (fun t : ℝ => nilpotentDerivationFlow D hD t x) (D x) 0 := by
  have hnil := hD
  obtain ⟨k, hk⟩ := hnil
  have hk' : D.toLinearMap ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  have hterm (i : ℕ) :
      HasDerivAt (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x))
        (if i = 1 then D x else 0) 0 := by
    have hh : HasDerivAt
        (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x))
        (((i : ℝ) * 0 ^ (i - 1)) • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow i).smul_const
        (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    by_cases hi : i = 1
    · subst i
      simp
    · by_cases hz : i = 0
      · subst i
        simp
      · have hsub : i - 1 ≠ 0 := by omega
        simp [hi, zero_pow hsub]
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (k + 2)) => hterm i)
  have heq : (fun t : ℝ => nilpotentDerivationFlow D hD t x) =
      (fun t => ∑ i ∈ Finset.range (k + 2),
        t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)) := by
    funext t
    exact nilpotentDerivationFlow_eq_sum D hD hk' t x
  rw [heq]
  simpa using hsum

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentSemidirectTangent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The tangent bracket of the codimension-one extension -/

noncomputable section
namespace PolycyclicRecognition

open VectorField
open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

section TangentComputation

variable [Group (L × ℝ)]

variable [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)]
  (hone : (inferInstance : Group (L × ℝ)).one = 0)
  (hmul : ∀ x y : L × ℝ,
    (inferInstance : Group (L × ℝ)).mul x y =
      (x.1 * nilpotentDerivationFlow D hD x.2 y.1, x.2 + y.2))

local instance instLieRingProdReal_solutions : LieRing (L × ℝ) :=
  inferInstanceAs (LieRing (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)))

include D hD hone hmul

local notation "ST" => GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)

local instance instLieAlgebraRealProd_solutions_rfe7c26_1 : LieAlgebra ℝ (L × ℝ) :=
  inferInstanceAs (LieAlgebra ℝ (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)))
def semidirectIdealInclusion :
    @MonoidHom L (L × ℝ) P.group.toMulOne
      (inferInstance : Group (L × ℝ)).toMulOne := by
  letI : MulOneClass (L × ℝ) := (inferInstance : Group (L × ℝ)).toMulOneClass
  exact {
  toFun x := (x, 0)
  map_one' := by
    change ((1 : L), (0 : ℝ)) = (inferInstance : Group (L × ℝ)).one
    rw [hone, P.one_eq_zero]
    rfl
  map_mul' x y := by
    change (x * y, (0 : ℝ)) = (inferInstance : Group (L × ℝ)).mul (x, 0) (y, 0)
    rw [hmul]
    simp only [nilpotentDerivationFlow_zero, zero_add] }

omit [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)] in
theorem contMDiff_semidirectIdealInclusion :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ)) ∞ (semidirectIdealInclusion D hD hone hmul) :=
  (contDiff_id.prodMk contDiff_const).contMDiff

def semidirectIdealLieHom : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) :=
  (homLieDifferential (semidirectIdealInclusion D hD hone hmul)
    (contMDiff_semidirectIdealInclusion D hD hone hmul)).comp P.tangentEquiv.toLieHom

theorem semidirectIdealLieHom_apply (v : L) :
    semidirectIdealLieHom D hD hone hmul v = (v, 0) := by
  change mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ))
    (fun x : L => (x, (0 : ℝ))) 1 (P.tangentEquiv v) = _
  rw [P.one_eq_zero]
  have hd := (ContinuousLinearMap.inl ℝ L ℝ).hasFDerivAt (x := (0 : L))
  change (mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ))
    (ContinuousLinearMap.inl ℝ L ℝ) 0) (show L from P.tangentEquiv v) = _
  have he : (show L from P.tangentEquiv v) = v := P.tangentEquiv_apply v
  rw [he]
  exact congrArg (fun A : L →L[ℝ] (L × ℝ) => A v) hd.hasMFDerivAt.mfderiv

theorem semidirect_ideal_bracket (v w : L) :
    ⁅((v, 0) : ST), ((w, 0) : ST)⁆ = (⁅v, w⁆, 0) := by
  have h := (semidirectIdealLieHom D hD hone hmul).map_lie v w
  rw [semidirectIdealLieHom_apply, semidirectIdealLieHom_apply,
    semidirectIdealLieHom_apply] at h
  exact h.symm

omit [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)] in
theorem semidirect_invariant_axis (v : L × ℝ) (t : ℝ) :
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) v (0, t) =
      (nilpotentDerivationFlow D hD t v.1, v.2) := by
  let A := (nilpotentDerivationFlow D hD t).toLinearEquiv.toContinuousLinearEquiv
  let B : (L × ℝ) →L[ℝ] (L × ℝ) :=
    (A.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ L ℝ)).prod
      (ContinuousLinearMap.snd ℝ L ℝ)
  have heq : (fun p : L × ℝ => (inferInstance : Group (L × ℝ)).mul (0, t) p) =
      (fun p => (A p.1, t + p.2)) := by
    funext p
    rw [hmul]
    rw [← P.one_eq_zero, one_mul]
    rfl
  have hd : HasFDerivAt (fun p : L × ℝ => (A p.1, t + p.2)) B 0 :=
    ((A.toContinuousLinearMap.hasFDerivAt.comp 0
      (ContinuousLinearMap.fst ℝ L ℝ).hasFDerivAt).prodMk
      ((ContinuousLinearMap.snd ℝ L ℝ).hasFDerivAt.const_add t))
  change mfderiv (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ))
    (fun p : L × ℝ => (inferInstance : Group (L × ℝ)).mul (0, t) p)
      (inferInstance : Group (L × ℝ)).one v = _
  rw [hone, heq, hd.hasMFDerivAt.mfderiv]
  rfl

theorem semidirect_invariant_time (g : L × ℝ) :
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) (0, 1) g = (0, 1) := by
  let f : (L × ℝ) → (L × ℝ) := fun p => (inferInstance : Group (L × ℝ)).mul g p
  let : Monoid (L × ℝ) := (inferInstance : Group (L × ℝ)).toMonoid
  let : Mul (L × ℝ) := (inferInstance : Group (L × ℝ)).toMul
  have hs : ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ)) ∞ f :=
    contMDiff_mul_left (I := 𝓘(ℝ, L × ℝ)) (a := g)
  have hf : DifferentiableAt ℝ f 0 :=
    (hs.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => ((0 : L), t)) (0, 1) 0 :=
    (hasDerivAt_const 0 (0 : L)).prodMk (hasDerivAt_id 0)
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => f (0, t)) = fun t => (g.1, g.2 + t) := by
    funext t
    dsimp only [f]
    rw [hmul, map_zero, ← P.one_eq_zero, mul_one]
  have hd : HasDerivAt (fun t : ℝ => f (0, t)) (0, 1) 0 := by
    rw [heq]
    exact (hasDerivAt_const 0 g.1).prodMk ((hasDerivAt_id 0).const_add g.2)
  have hval := hcomp.unique hd
  change mfderiv (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ)) f
    (inferInstance : Group (L × ℝ)).one (0, 1) = _
  rw [hone, mfderiv_eq_fderiv]
  exact hval

theorem semidirect_time_bracket (v : L) :
    ⁅((0, 1) : ST), ((v, 0) : ST)⁆ = (D v, 0) := by
  let u : ST := (0, 1)
  let w : ST := (v, 0)
  let V : (L × ℝ) → (L × ℝ) := fun g =>
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) w g
  have hV : ContDiff ℝ ∞ V := contMDiff_vectorSpace_iff_contDiff.mp
    (contMDiff_invariantVectorField_infty (E := L × ℝ) (G := L × ℝ) w)
  have hline : HasDerivAt (fun t : ℝ => ((0 : L), t)) (0, 1) 0 :=
    (hasDerivAt_const 0 (0 : L)).prodMk (hasDerivAt_id 0)
  have hc := (hV.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => V (0, t)) =
      (fun t => (nilpotentDerivationFlow D hD t v, (0 : ℝ))) := by
    funext t
    exact semidirect_invariant_axis D hD hone hmul (v, 0) t
  have hd : HasDerivAt (fun t : ℝ => V (0, t)) (D v, 0) 0 := by
    rw [heq]
    exact (hasDerivAt_nilpotentDerivationFlow_zero D hD v).prodMk (hasDerivAt_const 0 0)
  have hder := hc.unique hd
  change ⁅u, w⁆ = _
  rw [GroupLieAlgebra.bracket_def]
  change @Eq (L × ℝ) (mlieBracket (𝓘(ℝ, L × ℝ))
    (fun g : L × ℝ => (mulInvariantVectorField u g : L × ℝ)) V
    (inferInstance : Group (L × ℝ)).one) (D v, 0)
  rw [hone]
  apply (congrFun (mlieBracketWithin_eq_lieBracketWithin
    (V := fun g : L × ℝ => (mulInvariantVectorField u g : L × ℝ))
    (W := V) (s := Set.univ)) (0 : L × ℝ)).trans
  have htime : mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) u =
      (fun _ : L × ℝ => (0, 1)) := funext (semidirect_invariant_time D hD hone hmul)
  rw [htime]
  rw [lieBracketWithin_univ]
  change fderiv ℝ V 0 (0, 1) - fderiv ℝ (fun _ : L × ℝ => (0, 1)) 0 (V 0) = _
  have hz : fderiv ℝ (fun _ : L × ℝ => ((0 : L), (1 : ℝ))) (0 : L × ℝ) = 0 :=
    (hasFDerivAt_const ((0 : L), (1 : ℝ)) (0 : L × ℝ)).fderiv
  rw [hz, zero_apply]
  exact (sub_zero ((fderiv ℝ V (0 : L × ℝ)) (0, 1))).trans hder

theorem semidirect_tangent_bracket (v w : L) (s t : ℝ) :
    ⁅((v, s) : ST), ((w, t) : ST)⁆ =
      (⁅v, w⁆ + s • D w - t • D v, 0) := by
  let u : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) := (0, 1)
  let a : ST := (v, 0)
  let b : ST := (w, 0)
  let vs : ST := (v, s)
  let wt : ST := (w, t)
  have hv : vs = a + s • u := by
    change (v, s) = ((v, 0) : L × ℝ) + s • ((0, 1) : L × ℝ)
    ext <;> simp
  have hw : wt = b + t • u := by
    change (w, t) = ((w, 0) : L × ℝ) + t • ((0, 1) : L × ℝ)
    ext <;> simp
  have hcross : ⁅a, u⁆ = -((D v, 0) : ST) := by
    exact (lie_skew a u).symm.trans
      (congrArg (fun z : ST => -z) (semidirect_time_bracket D hD hone hmul v))
  have hideal : ⁅a, b⁆ = ((⁅v, w⁆, 0) : ST) :=
    semidirect_ideal_bracket D hD hone hmul v w
  have htime : ⁅u, b⁆ = ((D w, 0) : ST) :=
    semidirect_time_bracket D hD hone hmul w
  change @Eq ST ⁅vs, wt⁆ ((⁅v, w⁆ + s • D w - t • D v, 0) : ST)
  rw [hv, hw, add_lie, lie_add, lie_add, lie_smul, smul_lie, smul_lie, lie_smul,
    hideal, hcross, htime, lie_self]
  change @Eq (L × ℝ) _ _
  apply Prod.ext
  · change (⁅v, w⁆ + t • -D v) + (s • D w + s • t • (0 : L)) =
      ⁅v, w⁆ + s • D w - t • D v
    simp only [smul_neg, smul_zero, add_zero, sub_eq_add_neg]
    abel
  · change ((0 : ℝ) + t * -0) + (s * 0 + s * (t * 0)) = 0
    simp

end TangentComputation
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteAssociativeBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite BCH in an associative algebra with vanishing long products

The universal logarithm constructs the finite Baker--Campbell--Hausdorff
coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

variable (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
include hX

theorem rationalUniversalLogarithm_eval_lie :
    rationalWordEvaluation X (rationalUniversalLogarithm c n) =
      finiteUniversalLiePolynomial (c := c) X := by
  rw [rationalWord_evaluation_by_degrees X hX]
  simp_rw [rationalWordWeight_universalLogarithm]
  change (∑ d : Fin (c + 1), rationalWordEvaluation X (universalLogarithmCoefficient c n d.val)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, universalLogarithmCoefficient_zero, map_zero, zero_add]
  apply Finset.sum_congr rfl
  intro d _
  exact universalLogarithmCoefficient_lie_expansion c n d.val X

/-- A finite, universal right-nested Lie polynomial gives the exponential product. -/
theorem finite_associative_bch :
    (List.ofFn (fun i => IsNilpotent.exp (X i))).prod =
      IsNilpotent.exp (finiteUniversalLiePolynomial (c := c) X) := by
  have hnil := nilpotent_word_exp_product_pow X hX
  have he := exp_finiteNilpotentLog _ c hnil
  rw [add_sub_cancel] at he
  calc
    _ = IsNilpotent.exp (finiteNilpotentLog (c + 1)
        ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1)) := he.symm
    _ = IsNilpotent.exp (rationalWordEvaluation X (rationalUniversalLogarithm c n)) := by
      rw [rationalUniversalLogarithm_eval X hX]
    _ = _ := by rw [rationalUniversalLogarithm_eval_lie X hX]

theorem finiteUniversalLiePolynomial_pow :
    finiteUniversalLiePolynomial (c := c) X ^ (c + 1) = 0 := by
  rw [← rationalUniversalLogarithm_eval_lie X hX, rationalUniversalLogarithm_eval X hX]
  exact finiteNilpotentLog_pow _ c (nilpotent_word_exp_product_pow X hX)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundedAssociativeBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real coefficients and the bounded associative BCH identity -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A] [Algebra ℚ A]
variable {c n : ℕ} (X : Fin n → A)

theorem universalDynkinPolynomial_eq :
    finiteDynkinPolynomial (universalDynkinCoefficients c n) X =
      finiteUniversalLiePolynomial (c := c) X := by
  unfold finiteDynkinPolynomial finiteUniversalLiePolynomial universalDynkinCoefficients
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  exact Rat.cast_smul_eq_qsmul ℝ _ _

theorem bounded_associative_bch
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0) :
    (List.ofFn (fun i => IsNilpotent.exp (X i))).prod =
      IsNilpotent.exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) := by
  rw [universalDynkinPolynomial_eq]
  exact finite_associative_bch X hX

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FaithfulRepresentationBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting finite BCH through an actual faithful group representation

The derivative is the Lie homomorphism used in the polynomial. The only
algebraic assumption is a concrete common bound on products of its values.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem finite_bch_of_faithful_nilpotent_representation
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      j.toLinearMap.toContinuousLinearMap)
    (c : ℕ)
    (hc : ∀ l : List (GroupLieAlgebra (𝓘(ℝ, E)) G), c < l.length → (l.map j).prod = 0)
    {n : ℕ} (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) := by
  have hw (w : FreeMonoid (Fin n)) (h : c < w.length) :
      FreeMonoid.lift (fun i => j (X i)) w = 0 := by
    have hh := hc (w.toList.map X) (by simpa only [List.length_map, FreeMonoid.length] using h)
    simpa only [List.map_map, FreeMonoid.lift_apply, Function.comp_def] using hh
  have hn (i : Fin n) : IsNilpotent (j (X i)) :=
    ⟨c + 1, nilpotent_word_letter_pow (fun i => j (X i)) hw i⟩
  have hnp : IsNilpotent
      (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) := by
    rw [universalDynkinPolynomial_eq]
    exact ⟨c + 1, finiteUniversalLiePolynomial_pow (fun i => j (X i)) hw⟩
  apply hρ
  apply Units.ext
  calc
    (ρ (List.ofFn (fun i => Exp (X i))).prod : A) =
        (List.ofFn (fun i => (ρ (Exp (X i)) : A))).prod := by
      exact (map_list_prod ((Units.coeHom A).comp ρ) _).trans
        (congrArg List.prod (List.map_ofFn ..))
    _ = (List.ofFn (fun i => IsNilpotent.exp (j (X i)))).prod := by
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd,
        coe_algebraExpUnit]
      exact analytic_exp_eq_nilpotent_exp (hn i)
    _ = IsNilpotent.exp
        (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) :=
      bounded_associative_bch _ hw
    _ = (ρ (Exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X)) : A) := by
      rw [hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd,
        coe_algebraExpUnit]
      change _ = NormedSpace.exp (j (finiteDynkinPolynomial _ X))
      rw [finiteDynkinPolynomial_map, analytic_exp_eq_nilpotent_exp hnp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectCoordinateOrbit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinate orbits in the nilpotent semidirect construction -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

attribute [local instance] OAI.PolycyclicRecognition.semidirectCoordinateModuleRat
omit [FiniteDimensional ℝ L] P in
theorem semidirectCoordinate_injective :
    Function.Injective (fun g => fun i => semidirectCoordinate b i g) := by
  intro x y h
  apply Prod.ext
  · apply b.repr.injective
    ext i
    exact congrFun h (.inl i)
  · exact congrFun h (.inr ())

theorem semidirectProductCoordinatePolynomial_eval {k : ℕ} (hk : D.toLinearMap ^ k = 0) :
    ∀ (g : L × ℝ) (i : Fin n ⊕ Unit) (x : L × ℝ),
      semidirectCoordinate b i ((derivationSemidirectGroup D hD).mul x g) =
        coordinatePolynomialEvaluation (semidirectCoordinate b)
          (semidirectProductCoordinatePolynomial b D k i) g x  := by
  intro g i x
  rw [derivationSemidirect_mul]
  cases i with
  | inl j =>
    change b.repr (x.1 * nilpotentDerivationFlow D hD x.2 g.1) j = _
    rw [P.mul_eq]
    symm
    apply eval_dynkinCoordinatePolynomial b P.coefficients _
      (Pi.evalAlgHom ℝ (fun _ : L × ℝ => ℝ) g) _ ![x.1, nilpotentDerivationFlow D hD x.2 g.1]
    intro i j
    fin_cases i
    · simp [semidirectCoordinate]
    · exact semidirectFlowCoordinatePolynomial_eval b D hD hk x g j
  | inr j => simp [semidirectCoordinate, coordinatePolynomialEvaluation, semidirectProductCoordinatePolynomial]

include hD in
theorem finiteDimensional_semidirectCoordinateOrbit :
    letI := derivationSemidirectGroup D hD
    FiniteDimensional ℝ (coordinateOrbitSpan (semidirectCoordinate b))  := by
  let := derivationSemidirectGroup D hD
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  exact finiteDimensional_coordinateOrbitSpan_of_polynomial (semidirectCoordinate b)
    (semidirectProductCoordinatePolynomial b D k)
    (fun g i x => semidirectProductCoordinatePolynomial_eval b D hD hk g i x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialCurves
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial scalar curves in semidirect coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem hasSemidirectPolynomialCoordinates_mul (F H : ℝ → L × ℝ)
    (hF : HasSemidirectPolynomialCoordinates b F)
    (hH : HasSemidirectPolynomialCoordinates b H) :
    HasSemidirectPolynomialCoordinates b
      (fun t => (derivationSemidirectGroup D hD).mul (F t) (H t)) := by
  intro i
  cases i with
  | inl j =>
    have hf : HasPolynomialLineCoordinates b (fun t => (F t).1) := fun i => hF (.inl i)
    have hh : HasPolynomialLineCoordinates b (fun t => (H t).1) := fun i => hH (.inl i)
    have hflow := hasPolynomialLineCoordinates_derivationFlow b D hD
      (fun t => (F t).2) (fun t => (H t).1) (hF (.inr ())) hh
    have hp := hasPolynomialLineCoordinates_dynkin b P.coefficients
      ![(fun t => (F t).1), (fun t => nilpotentDerivationFlow D hD (F t).2 (H t).1)]
      (by intro i; fin_cases i; exact hf; exact hflow) j
    change (fun t => b.repr ((F t).1 * nilpotentDerivationFlow D hD (F t).2 (H t).1) j) ∈ _
    have heq (t : ℝ) :
        (fun i : Fin 2 => ![(fun t => (F t).1),
          (fun t => nilpotentDerivationFlow D hD (F t).2 (H t).1)] i t) =
        ![(F t).1, nilpotentDerivationFlow D hD (F t).2 (H t).1] := by
      funext i
      fin_cases i <;> rfl
    simpa only [P.mul_eq, heq] using hp
  | inr j => exact polynomialFunctions.add_mem (hF (.inr ())) (hH (.inr ()))

theorem semidirect_translated_line_polynomial (a v z : L × ℝ) :
    ∀ i, (fun t : ℝ => semidirectCoordinate b i
      ((derivationSemidirectGroup D hD).mul ((derivationSemidirectGroup D hD).mul a (t • v)) z)) ∈ polynomialFunctions := by
  exact hasSemidirectPolynomialCoordinates_mul b D hD _ _
    (hasSemidirectPolynomialCoordinates_mul b D hD _ _
      (hasSemidirectPolynomialCoordinates_const b a)
      (hasSemidirectPolynomialCoordinates_line b v))
    (hasSemidirectPolynomialCoordinates_const b z)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnconditionalNilpotentModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simply connected nilpotent model existence without published inputs -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

def polynomialCoordinateLieModel (L : Type*) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] [P : PolynomialExponentialCoordinates L] : NilpotentLieModel L := by
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  exact { modelSpace := L, carrier := L, equiv := P.tangentEquiv }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalDynkinTruncation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the universal BCH polynomial to the nilpotency class -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem universalDynkinPolynomial_truncate {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {c d n : ℕ} (h : c ≤ d)
    (hc : LieModule.lowerCentralSeries ℝ L L c = ⊥) (X : Fin n → L) :
    finiteDynkinPolynomial (universalDynkinCoefficients d n) X =
      finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold finiteDynkinPolynomial
  rw [Fin.sum_univ_add]
  trans (∑ e : Fin c, ∑ w : Fin (e.val + 1) → Fin n,
    universalDynkinCoefficients c n e w • evalBracketWord X (rightNestedWord e.val w)) + 0
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro w _
      have he := universalDynkinCoefficients_stable (n := n) (Nat.le_add_right c k) e w
      change universalDynkinCoefficients (c + k) n (e.castLE (Nat.le_add_right c k)) w •
        evalBracketWord X (rightNestedWord e.val w) = _
      rw [← he]
    · apply Finset.sum_eq_zero
      intro e _
      apply Finset.sum_eq_zero
      intro w _
      rw [evalBracketWord_eq_zero_of_depth X hc (rightNestedWord _ w) (by
        rw [rightNestedWord_depth]
        exact Nat.le_add_right c e.val), smul_zero]
  · exact add_zero _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteProjectivePresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective covers of finitely generated representations -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

theorem finiteIntegralProjectivePresentation_exists (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    Nonempty (FiniteIntegralProjectivePresentation A) := by
  obtain ⟨ι, hι, f, hf⟩ := finiteIntegralFreeCover_exists A hA
  let := hι
  exact ⟨{
    p := Rep.free ℤ G ι
    f := f
    epi := hf
    finite := integralRepresentationFinite_free G ι }⟩

/-- A projective presentation chosen with finite source whenever the target
is finitely generated. The finiteness proof stays inside the chosen object. -/
def chosenIntegralPresentation (A : Rep.{0} ℤ G) : ProjectivePresentation A := by
  classical
  exact if h : IntegralRepresentationFinite G A then
    (finiteIntegralProjectivePresentation_exists A h).some.toProjectivePresentation
  else (EnoughProjectives.presentation A).some

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InductionExhaustionVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing for induction along a subgroup exhaustion

The finite stages may have arbitrarily large projective dimensions. The
ambient group's FP-infinity hypothesis supplies continuity of its completed
cohomology for the actual induced-coefficient colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

variable (A : Rep.{0} ℤ G) (H : ℕ → Subgroup G) (K : Subgroup G)
variable (hmono : Monotone H) (hHK : ∀ n, H n ≤ K)
variable (hcover : ∀ g ∈ K, ∃ n, g ∈ H n)

def inducedExhaustionDiagram : SequentialRepresentationDiagram G :=
  ascendingQuotientDiagram (inductionAmbient A)
    (fun n => subgroupCoinvariantRelations (inductionDiagonalAction A) (H n))
    (fun n => inductionRelations_invariant A (H n))
    (fun _ _ h => subgroupCoinvariantRelations_mono _ (hmono h))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarProbeTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual polar-template widths for the three probe boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
def polarProbeWidths (K : ProperCone ℝ (StrongDual ℝ W)) : Fin M.letterCount → ℝ :=
  fun i => conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The actual normalized halfspaces used to sample the root ideal. -/
def samplingPolytope : Set W :=
  weightSamplingPolytope (fun i => ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)

set_option maxHeartbeats 1000000 in
theorem sampling_weight_ne_zero (i : Fin M.letterCount) :
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ≠ 0 := by
  intro hz
  apply M.weight_nonzero i
  funext h
  have he := congrArg (fun f : W →L[ℝ] ℝ =>
    f (eW (heightProjection T.character (h : L)))) hz
  simpa [supportIn, SupportDatum.transport, supportDatum_weight,
    cartanHeightWeight_projection] using he

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingNonzero
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonvanishing of the actual linear sampling weights -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The linear form underlying each actual sampling weight is nonzero. -/
theorem sampling_linear_weight_ne_zero (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weight i ≠ 0 := by
  intro h
  exact M.sampling_weight_ne_zero T hunimod eW i (congrArg LinearMap.toContinuousLinearMap h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realImaginaryOperator_complexify _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The infinitesimal imaginary Cartan action

The infinitesimal compact action is a genuine Lie derivation. Subtracting
it from the original adjoint action removes exactly the imaginary weights.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- The zero-weight Cartan algebra is fixed infinitesimally. -/
theorem imaginaryOperator_cartan (h k : H) : imaginaryOperator H h k = 0 := by
  have hk : (k : L) ∈ genWeightSpace L (0 : H → ℂ) := by
    change (k : L) ∈ rootSpace H 0
    rw [rootSpace_zero_eq]
    exact k.property
  rw [imaginaryOperator_apply_genWeight H h 0 hk]
  simp

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanJordan
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The semisimple Cartan operator preserves the original triangular flag -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The full semisimple part, before its imaginary part is removed. -/
def semisimpleOperator (h : H) : Module.End ℂ L := weightOperator H (fun χ => χ h)

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexPhaseDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative of a Cartan phase along a real line -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

local instance instNormedAddCommGroup_solutions : NormedAddCommGroup L := rotationNormedAddCommGroup
local instance instNormedSpaceComplex_solutions : NormedSpace ℂ L := rotationNormedSpace
local instance instNormedSpaceReal_solutions : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentCoordinateBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal product formula in faithful unipotent coordinates

This algebraic transport uses only the exponential compatibility of the given
representation. Its bound may be enlarged, so two coordinate models can use
exactly the same coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type*} [LieRing L] [LieAlgebra ℝ L] [Group L]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem finite_product_of_unipotent_coordinates
    (ρ : L →* Aˣ) (hρ : Function.Injective ρ) (j : L →ₗ⁅ℝ⁆ A)
    (hexp : ∀ x, ρ x = algebraExpUnit (j x)) (c : ℕ)
    (hc : ∀ l : List L, c < l.length → (l.map j).prod = 0)
    {n : ℕ} (X : Fin n → L) :
    (List.ofFn X).prod = finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  have hw (w : FreeMonoid (Fin n)) (h : c < w.length) :
      FreeMonoid.lift (fun i => j (X i)) w = 0 := by
    have hh := hc (w.toList.map X) (by simpa only [List.length_map, FreeMonoid.length] using h)
    simpa only [List.map_map, FreeMonoid.lift_apply, Function.comp_def] using hh
  have hn (i : Fin n) : IsNilpotent (j (X i)) :=
    ⟨c + 1, nilpotent_word_letter_pow (fun i => j (X i)) hw i⟩
  have hnp : IsNilpotent
      (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) := by
    rw [universalDynkinPolynomial_eq]
    exact ⟨c + 1, finiteUniversalLiePolynomial_pow (fun i => j (X i)) hw⟩
  apply hρ
  apply Units.ext
  calc
    (ρ (List.ofFn X).prod : A) = (List.ofFn (fun i => (ρ (X i) : A))).prod := by
      exact (map_list_prod ((Units.coeHom A).comp ρ) _).trans
        (congrArg List.prod (List.map_ofFn ..))
    _ = (List.ofFn (fun i => IsNilpotent.exp (j (X i)))).prod := by
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [hexp, coe_algebraExpUnit]
      exact analytic_exp_eq_nilpotent_exp (hn i)
    _ = IsNilpotent.exp
        (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) :=
      bounded_associative_bch _ hw
    _ = (ρ (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) : A) := by
      rw [hexp, coe_algebraExpUnit]
      rw [finiteDynkinPolynomial_map, analytic_exp_eq_nilpotent_exp hnp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a codimension-one semidirect product

An equivariant homomorphism on the ideal and the complementary exponential
curve give the required homomorphism, with its actual manifold derivative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (k : L →* G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
  (hact : ∀ t x, k (nilpotentDerivationFlow D hD t x) =
    Exp (t • u) * k x * (Exp (t • u))⁻¹)

theorem hasMFDerivAt_derivationSemidirectHom
    (j : L →L[ℝ] E)
    (hk : HasMFDerivAt (𝓘(ℝ, L)) (𝓘(ℝ, E)) k (1 : L) j) :
    let d : (L × ℝ) →L[ℝ] E := j.comp (ContinuousLinearMap.fst ℝ L ℝ) +
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (M₂ := E) (u : E)).comp
        (ContinuousLinearMap.snd ℝ L ℝ)
    HasMFDerivAt (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, E))
      (derivationSemidirectHom D hD Exp hExp k u hact) (0 : L × ℝ) d := by
  have hk0 : HasMFDerivAt (𝓘(ℝ, L)) (𝓘(ℝ, E)) k (0 : L) j := by
    rw [← P.one_eq_zero]
    exact hk
  exact HasMFDerivAt.mul_at_one
    (hk0.comp (f := fun p : L × ℝ => p.1) (0 : L × ℝ)
      (ContinuousLinearMap.fst ℝ L ℝ).hasFDerivAt.hasMFDerivAt)
    ((hExp.hasMFDerivAt_zero u).comp (f := fun p : L × ℝ => p.2) (0 : L × ℝ)
      (ContinuousLinearMap.snd ℝ L ℝ).hasFDerivAt.hasMFDerivAt)
    (by change k 0 = 1; rw [← P.one_eq_zero, map_one])
    (by change Exp (0 • u) = 1; rw [zero_smul, hExp.map_zero])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightFactorModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent and Cartan factors for a solvable group with complex weights -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold ContDiff Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)

/-- The concrete group part of the complex-weight Cartan model. The ambient
overlap is retained, and all lifting conclusions refer to the actual map. -/
structure ComplexWeightFactorModel where
  N : NilpotentLieModel T.kernelIdeal
  D : NilpotentLieModel H
  weightCharacter : G →* Multiplicative T.weightMap.range
  continuousWeightCharacter : Continuous weightCharacter
  weightCharacter_exp : ∀ x, (weightCharacter (ExpG x)).toAdd = T.weightMap.rangeRestrict x
  ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier
  ExpD : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier → D.carrier
  isExpN : IsGroupExponential ExpN
  isExpD : IsGroupExponential ExpD
  inclusionN : N.carrier →* G
  inclusionD : D.carrier →* G
  action : D.carrier →* MulAut N.carrier
  closedN : Topology.IsClosedEmbedding inclusionN
  closedD : Topology.IsClosedEmbedding inclusionD
  compatibleN : ∀ x : T.kernelIdeal, inclusionN (ExpN (N.equiv x)) = ExpG x
  compatibleD : ∀ x : H, inclusionD (ExpD (D.equiv x)) = ExpG x
  normalN : inclusionN.range.Normal
  conjugation : ∀ d n, inclusionN (action d n) =
    inclusionD d * inclusionN n * (inclusionD d)⁻¹
  surjective : Function.Surjective (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  openProduct : IsOpenMap (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  compactLifts : ∀ K : Set G, IsCompact K → ∃ C : Set (N.carrier × D.carrier),
    IsCompact C ∧ K ⊆ (fun p => inclusionN p.1 * inclusionD p.2) '' C
  overlap : Set.range inclusionN ∩ Set.range inclusionD = ExpG ''
    ((T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩
      (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)))


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivationLieSpace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tangent algebra of the derivation extension

The type synonym keeps exponential group coordinates distinct from the raw
semidirect group on the product vector space.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def DerivationLieSpace (D : LieDerivation ℝ L L) (_hD : IsNilpotent D.toLinearMap) : Type _ :=
  L × ℝ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilradicalRotationAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotation action on the actual nilpotent kernel -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem continuous_nilradicalRotation :
    Continuous (fun p : realRotationTorus L H × T.kernelIdeal =>
      T.nilradicalRotation H p.1 p.2) :=
  ((continuous_realTorusOperator L H).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end Topology
end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntegratedNilradicalRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotations on the closed nilpotent factor -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (N : NilpotentLieModel T.kernelIdeal)

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance modelKernelTopologicalAddGroup : IsTopologicalAddGroup T.kernelIdeal :=
  Submodule.topologicalAddGroup T.kernelIdeal.toSubmodule

theorem continuous_modelNilradicalRotation :
    Continuous (fun p : realRotationTorus L H ×
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
        modelNilradicalRotation T H N p.1 p.2) := by
  have he : Continuous (N.equiv : T.kernelIdeal →
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.equiv.toLinearMap.continuous_of_finiteDimensional
  have hi : Continuous (N.equiv.symm :
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → T.kernelIdeal) :=
    N.equiv.symm.toLinearMap.continuous_of_finiteDimensional
  have hr := (T.continuous_nilradicalRotation H).comp
    (continuous_fst.prodMk (hi.comp continuous_snd))
  simpa only [modelNilradicalRotation_apply, Function.comp_def] using he.comp hr

end Topology
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealTorusAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Cartan rotations commute with the Cartan adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) [H.IsCartanSubalgebra]

/-- A rotation fixing the Cartan algebra commutes with every Cartan bracket. -/
theorem realTorusOperator_cartan_bracket
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    realTorusOperator _ H z ⁅(h : GroupLieAlgebra (𝓘(ℝ, E)) G), x⁆ =
      ⁅(h : GroupLieAlgebra (𝓘(ℝ, E)) G), realTorusOperator _ H z x⁆ := by
  rw [realTorusOperator_lie, realTorusOperator_fixes_cartan]

/-- The same commutation holds for the exponential of the adjoint operator. -/
theorem realTorusOperator_commutes_adjoint_exponential
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H) (x : E) :
    realTorusOperator _ H z (NormedSpace.exp (groupAdjointOperator (E := E) (G := G) h) x) =
      NormedSpace.exp (groupAdjointOperator (E := E) (G := G) h)
        (realTorusOperator _ H z x) := by
  let A : E →L[ℝ] E := (realTorusOperator (GroupLieAlgebra (𝓘(ℝ, E)) G) H z).toContinuousLinearMap
  have hc : Commute A (groupAdjointOperator (E := E) (G := G) h) := by
    ext v
    exact realTorusOperator_cartan_bracket H z h v
  exact congrArg (fun f : E →L[ℝ] E => f x) (hc.exp_right.eq)

/-- In the original Lie group the compact rotations commute with conjugation
by exponentials of Cartan elements, at the tangent level. -/
theorem realTorusOperator_commutes_cartan_conjugation
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H) (x : E) :
    realTorusOperator _ H z (adjointLinearMap (E := E) (G := G) (Exp h) x) =
      adjointLinearMap (E := E) (G := G) (Exp h) (realTorusOperator _ H z x) := by
  have he := adjointLinearMap_exponential hExp (h : GroupLieAlgebra (𝓘(ℝ, E)) G) 1
  simp only [one_smul] at he
  rw [he]
  exact realTorusOperator_commutes_adjoint_exponential H z h x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntegratedCartanRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Cartan rotations on the original simply connected group -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

include hExp in
omit [H.IsCartanSubalgebra] in
/- The actual tangent conjugation preserves the nilpotent ideal. -/
set_option maxHeartbeats 1000000 in
theorem cartan_conjugation_mem (h : H) (x : T.kernelIdeal) :
    adjointLinearMap (E := E) (G := G) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G) ∈ T.kernelIdeal := by
  have he := adjointLinearMap_exponential hExp (h : GroupLieAlgebra (𝓘(ℝ, E)) G) 1
  simp only [one_smul] at he
  rw [he]
  let U : Submodule ℝ E := T.kernelIdeal.toSubmodule
  exact exp_apply_mem_of_stable U U.closed_of_finiteDimensional
    (groupAdjointOperator (E := E) (G := G) h)
    (fun w hw => T.kernelIdeal.lie_mem hw) x.property

/- Conjugation in the factorization agrees with the actual adjoint map
on nilpotent exponential coordinates. -/
set_option maxHeartbeats 1000000 in
omit [H.IsCartanSubalgebra] in
theorem action_cartan_exponential (h : H) (x : T.kernelIdeal) :
    F.action (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv ⟨adjointLinearMap (E := E) (G := G) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
        cartan_conjugation_mem hExp h x⟩) := by
  apply F.closedN.injective
  rw [F.conjugation, F.compatibleD, F.compatibleN, F.compatibleN]
  exact conjugation_exponential hExp (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G)

set_option maxHeartbeats 1000000 in
theorem rotation_fixes_overlap
    (α : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut F.N.carrier)
    (hα : ∀ z x, α z (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) :
    ∀ z n d, F.inclusionN n = F.inclusionD d → α z n = n := by
  intro z n d hnd
  have ho : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n,rfl⟩,⟨d,hnd.symm⟩⟩
  rw [F.overlap] at ho
  obtain ⟨x,hx,hex⟩ := ho
  have hn : F.ExpN (F.N.equiv ⟨x,hx.1⟩) = n :=
    F.closedN.injective ((F.compatibleN ⟨x,hx.1⟩).trans hex)
  rw [← hn,hα]
  congr 2
  apply Subtype.ext
  exact realTorusOperator_fixes_cartan _ H z ⟨x,hx.2⟩

/- The compact rotations descend to a jointly continuous action on the
original group, fixing its Cartan factor and acting as prescribed on its
closed nilpotent factor. No group integration premise is used. -/

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact rotation character on the actual adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- The rotational character on the image of the full complex adjoint
weight map, viewed as a real additive vector group. -/
def weightRotationCharacter : Multiplicative T.weightMap.range →* realRotationTorus L H :=
  (realPhaseHom L H).comp (T.cartanWeightSection H).toAddMonoidHom.toMultiplicative

/-- Compose the rotation character with a group-valued weight map. -/
def liftRotationCharacter {G : Type*} [Group G]
    (q : G →* Multiplicative T.weightMap.range) : G →* realRotationTorus L H :=
  (T.weightRotationCharacter H).comp q

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

attribute [local instance] OAI.PolycyclicRecognition.ComplexTriangularAdjoint.characterCartanTopologicalAddGroup
/-- The character is continuous for the actual finite-dimensional quotient
topology; no discrete replacement of the compact torus is used. -/
theorem continuous_weightRotationCharacter : Continuous (T.weightRotationCharacter H) :=
  (continuous_realPhaseVector L H).comp
    ((T.cartanWeightSection H).continuous_of_finiteDimensional.comp continuous_toAdd)

theorem continuous_liftRotationCharacter {G : Type*} [Group G] [TopologicalSpace G]
    (q : G →* Multiplicative T.weightMap.range) (hq : Continuous q) :
    Continuous (T.liftRotationCharacter H q) :=
  (T.continuous_weightRotationCharacter H).comp hq

end Topology
end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FactorRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant compact character for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/- The actual quotient character followed by its compact rotational part. -/
def rotationCharacter : G →* realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H :=
  T.liftRotationCharacter H F.weightCharacter

omit [H.IsCartanSubalgebra] in
theorem weightCharacter_nilradical (x : T.kernelIdeal) :
    F.weightCharacter (F.inclusionN (F.ExpN (F.N.equiv x))) = 1 := by
  apply Multiplicative.ext
  exact (congrArg (fun g => (F.weightCharacter g).toAdd) (F.compatibleN x)).trans
    ((F.weightCharacter_exp x).trans (Subtype.ext x.property))

theorem rotationCharacter_nilradical (x : T.kernelIdeal) :
    F.rotationCharacter (F.inclusionN (F.ExpN (F.N.equiv x))) = 1 :=
  (congrArg (T.weightRotationCharacter H) (F.weightCharacter_nilradical x)).trans
    (T.weightRotationCharacter H).map_one

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowOperators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The triangular operator underlying the real shadow adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

def weightCorrectedOperator (x : L) : Module.End ℝ L :=
  ad ℝ L x - (T.weightImaginaryAction H x).toLinearMap

def complexWeightCorrectedOperator (x : L) : Module.End ℂ (ℂ ⊗[ℝ] L) :=
  ad ℂ (ℂ ⊗[ℝ] L) (complexificationLieHom L x) -
    ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H (T.cartanWeightSection H (T.weightMap.rangeRestrict x)))

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multivariate polynomial multiplication in the derivation extension -/

noncomputable section
namespace PolycyclicRecognition
variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

def HasPolynomialSemidirectCoordinates (F : (I → ℝ) → L × ℝ) : Prop :=
  IsCoordinatePolynomial (fun x i => semidirectCoordinate b i (F x))

end PolycyclicRecognition

end

end OAI
end


