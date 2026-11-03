-- Prove2me | Definitions.Def_OAIQ093D011
-- name    : OAIQ093D011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T17:59:56.777067+00:00
-- url     : https://prove2.me/theorems/7269ae80-bf7f-42b0-b596-51dcedca96da
-- title:
--   Definitions bundle OAIQ093D011 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 46 definitions, 5 instances and 14 theorems. The definitions and types are `OAI.PolycyclicRecognition.normalInductionTensorHom`, `OAI.PolycyclicRecognition.normalInductionTensorLinear`, `OAI.PolycyclicRecognition.normalTensorQuotientTerm`, `OAI.PolycyclicRecognition.pairDomainTranslation`, `OAI.PolycyclicRecognition.pairInverseTargetTranslation`, `OAI.PolycyclicRecognition.polarSamplingTemplates`, `OAI.PolycyclicRecognition.polynomialCoordinateHeightHom`, `OAI.PolycyclicRecognition.polynomialEndpointScheme`, `OAI.PolycyclicRecognition.polynomialSliceDifferential`, `OAI.PolycyclicRecognition.productOccupationLaw`, `OAI.PolycyclicRecognition.rationalCoefficientColimit`, `OAI.PolycyclicRecognition.rationalCoefficientDiagram`, `OAI.PolycyclicRecognition.rationalCoefficientInclusion`, `OAI.PolycyclicRecognition.rationalConjugation`, `OAI.PolycyclicRecognition.rationalConjugationLinear`, `OAI.PolycyclicRecognition.rationalPreimageSubgroup`, `OAI.PolycyclicRecognition.rationalSubgroupFiltration`, `OAI.PolycyclicRecognition.rationalTrivialRetract`, `OAI.PolycyclicRecognition.realIntegerSemidirectMap`, `OAI.PolycyclicRecognition.relativeTraceRepresentation`, `OAI.PolycyclicRecognition.relativeTraceTerm`, `OAI.PolycyclicRecognition.rescaledLieData`, `OAI.PolycyclicRecognition.rescaledTupleBases`, `OAI.PolycyclicRecognition.rescaledTwoImageData`, `OAI.PolycyclicRecognition.rootIntervalLaw`, `OAI.PolycyclicRecognition.rootIntervalSupport`, `OAI.PolycyclicRecognition.semidirectProductMeasurableSpace`, `OAI.PolycyclicRecognition.semidirectProductMeasure`, `OAI.PolycyclicRecognition.smallCoefficientConstant`, `OAI.PolycyclicRecognition.smallCoefficientEvaluation`, `OAI.PolycyclicRecognition.sourceBundleBoundary`, `OAI.PolycyclicRecognition.spectralEigenvalue`, `OAI.PolycyclicRecognition.spectralLieDerivation`, `OAI.PolycyclicRecognition.subgroupBarResolutionHomotopy`, `OAI.PolycyclicRecognition.subgroupResolution`, `OAI.PolycyclicRecognition.subgroupShapiroIso`, `OAI.PolycyclicRecognition.submoduleAdjointStabilizer`, `OAI.PolycyclicRecognition.switchEndpoint`, `OAI.PolycyclicRecognition.switchParameterLaw`, `OAI.PolycyclicRecognition.truncatedEnvelopingGenerator` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `MatrixSubsum_Subsums`, `PolycyclicRecognition_Algebra_FiniteIndexTraceRetract`, `PolycyclicRecognition_Algebra_GeneratorOrbit`, `PolycyclicRecognition_Algebra_IndependentSwitchParameters`, `PolycyclicRecognition_Algebra_NilpotentClassBound`, `PolycyclicRecognition_Algebra_NormalInductionTensor`, `PolycyclicRecognition_Algebra_PairCoupling`, `PolycyclicRecognition_Algebra_RationalCoefficientSequence`, `PolycyclicRecognition_Algebra_RationalConjugation`, `PolycyclicRecognition_Algebra_RationalGroupDimension`, `PolycyclicRecognition_Algebra_RationalSubgroupFiltration`, `PolycyclicRecognition_Algebra_RescaledTwoImageLimit`, `PolycyclicRecognition_Algebra_SmallCoefficientConstants`, `PolycyclicRecognition_Algebra_SpectralLogValue`, `PolycyclicRecognition_Algebra_SubgroupShapiro`, `PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra`, `PolycyclicRecognition_Analysis_MeanSubgroup`, `PolycyclicRecognition_Analysis_OccupationSampling`, `PolycyclicRecognition_Analysis_PolynomialEndpointSchemes`, `PolycyclicRecognition_Analysis_RescaledTupleVolume`, `PolycyclicRecognition_Analysis_SourceBundleBlockPaths`, `PolycyclicRecognition_Analysis_SwitchEndpoints`, `PolycyclicRecognition_Analysis_WordChartPivot`, `PolycyclicRecognition_Finiteness_CompletedCohomology`, `PolycyclicRecognition_Finiteness_NormalHomologyAction`, `PolycyclicRecognition_Finiteness_SubgroupBarResolution`, `PolycyclicRecognition_Finiteness_SubgroupResolution`, `PolycyclicRecognition_Geometry_CartanSamplingParameters`, `PolycyclicRecognition_Geometry_GradedHeight`, `PolycyclicRecognition_Geometry_PolynomialMinorDifferential`, `PolycyclicRecognition_Geometry_PositiveWeightCones`, `PolycyclicRecognition_Geometry_RescaledLieFamily`, `PolycyclicRecognition_Geometry_RootIntervalSampling`, `PolycyclicRecognition_Geometry_RootIntervalSupports`, `PolycyclicRecognition_Geometry_SemidirectProductHaar`, `PolycyclicRecognition_Geometry_SpectralLieDerivation`, `PolycyclicRecognition_Geometry_UnipotentLieFlow`, `PolycyclicRecognition_Geometry_WeightedWordBound`, `PolycyclicRecognition_Geometry_WeightedWordNorm`, `PolycyclicRecognition_Lattices_IntegerSemidirectLattice`, `Thompson_MeanApproximation`, `Unitary_Packing`.
--
--   **Imports.** It imports the bundles `OAIQ093D000`, `OAIQ093D001`, `OAIQ093D002`, `OAIQ093D003`, `OAIQ093D004` and `OAIQ093D005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D015`; the statements `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero`, `OAI_PolycyclicRecognition_CartanWordModel_exists_interval_recurrence_cells_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_supported_switch_profiles_agree_on`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence`, `OAI.PolycyclicRecognition.cartan_cover_controlled_pairs` and `OAI.PolycyclicRecognition.supported_profile_increment_of_flow`; the proofs of `GeneratesNS.exists_theorem_3_1_input`, `OAI_PolycyclicRecognition_CartanWordModel_supported_switch_profiles_agree_on`, `OAI.PolycyclicRecognition.supported_profile_increment_of_flow` and `int_matrix_poly_growth_eigenvalue`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D002
import Definitions.Def_OAIQ093D003
import Definitions.Def_OAIQ093D004
import Definitions.Def_OAIQ093D005

section
-- module Solutions.OAIQ093_PR.MatrixSubsum_Subsums
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subset sums of matrix powers

The `DerivedSets` machinery and the estimate `subsums_unique`: distinct subsets of `[a,b)` give
distinct sums of `Aᵏ • v` when `A` has an eigenvalue of norm `≥ 3`.
-/


open scoped Finset
open scoped Pointwise


@[expose]
def poly_cancel  {R: Type*} [NormedCommRing R] {n: ℕ} (A: Matrix (Fin n) (Fin n) R) (v: (Fin n) → R) (p q : Finset ℕ) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)) : DerivedSets A v p q := ({
  h_prime := by
    have p_inter_subset : p ∩ q ⊆ q := by
      simp
    rw [← Finset.sdiff_union_inter (s := p) (t := q)] at hpq
    rw [Finset.sum_union (by apply Finset.disjoint_sdiff_inter)] at hpq
    rw [←  Finset.sum_sdiff p_inter_subset] at hpq
    simpa using hpq
  supp_disj := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    grind
} : DerivedSets A v p q)
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTraceRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative trace-one coefficients are retracts of induced restrictions

The averaging is over a finite coset space, so the subgroup itself may be
infinite. The trace element is invariant under that subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G R : Type} [Group G] [Ring R] [MulSemiringAction G R]
variable (N : Subgroup G)

variable (e : R) (he : ∀ n : N, (n : G) • e = e)

abbrev relativeTraceRepresentation : Rep ℤ G := ringActionRepresentation (H := G) (R := R)

def relativeTraceTerm (g : G) : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  (IndV.mk N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))).ρ g).comp
    ((LinearMap.mulLeft ℤ e).comp ((relativeTraceRepresentation (G := G) (R := R)).ρ g))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorOrbit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spanning by conjugated generator directions

Products of adjoint exponentials applied to a Lie-generating family span the
whole algebra. This proves the linear nondegeneracy needed to construct a
submersive generator product scheme; it does not assume controllability or a
volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedSpace
/-- The elements whose adjoints preserve a fixed linear subspace form a Lie
subalgebra, by the Jacobi identity. -/
def submoduleAdjointStabilizer (U : Submodule ℝ L) : LieSubalgebra ℝ L where
  carrier := {x | ∀ v ∈ U, ⁅x, v⁆ ∈ U}
  zero_mem' := by intro v _; simpa only [zero_lie] using U.zero_mem
  add_mem' := by
    intro x y hx hy v hv
    simpa only [add_lie] using U.add_mem (hx v hv) (hy v hv)
  smul_mem' := by
    intro c x hx v hv
    simpa only [smul_lie] using U.smul_mem c (hx v hv)
  lie_mem' := by
    intro x y hx hy v hv
    rw [lie_lie]
    exact U.sub_mem (hx _ (hy v hv)) (hy _ (hx v hv))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IndependentSwitchParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable event of successful independent switch parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

universe u

instance switchParametersMeasurableSpace {G : Type*} [MeasurableSpace G] :
    (k : ℕ) → MeasurableSpace (SwitchParameters G k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k + 1 =>
    letI := switchParametersMeasurableSpace (G := G) k
    inferInstanceAs (MeasurableSpace (G × G × SwitchParameters G k))

variable {G : Type*} [Group G] [MeasurableSpace G]

def switchParameterLaw (σ : ℕ → Measure G) :
    (n k : ℕ) → Measure (SwitchParameters G k)
  | _, 0 => Measure.dirac PUnit.unit
  | n, k + 1 => (σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))

instance switchParameterLaw_isProbability (σ : ℕ → Measure G)
    [∀ j, IsProbabilityMeasure (σ j)] (n k : ℕ) :
    IsProbabilityMeasure (switchParameterLaw σ n k) := by
  induction k generalizing n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ k ih =>
    let := ih (n + 1)
    exact inferInstanceAs (IsProbabilityMeasure
      ((σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting integral resolutions to subgroups

Restriction is exact and preserves projectives. Truncating at a projective
syzygy before restriction gives the cohomological-dimension bound for every
subgroup, without a finite-generation hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G] (H : Subgroup G)

/-- Restrict an actual integral resolution, retaining its augmentation. -/
def subgroupResolution (P : ProjectiveResolution (trivialIntegral G)) :
    ProjectiveResolution (trivialIntegral H) :=
  (Rep.resFunctor H.subtype).mapProjectiveResolution P

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanSubgroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting invariant means to subgroups

The finite-index height kernel in the recognition argument inherits amenability
from the ambient group. The construction below works for an arbitrary subgroup:
choose representatives for right cosets, construct an equivariant map to the subgroup,
and extend each bounded function by composition with this map.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u

variable {G : Type u} [Group G]

/-- The subgroup coordinate intertwines the left action of the subgroup. -/
theorem subgroupCoordinate_mul (K : Subgroup G) (k : K) (g : G) :
    subgroupCoordinate K ((k : G) * g) = k * subgroupCoordinate K g := by
  have hq : (Quotient.mk'' ((k : G) * g) : Quotient (QuotientGroup.rightRel K)) =
      Quotient.mk'' g := by
    apply Quotient.sound'
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using K.inv_mem k.property
  apply Subtype.ext
  change (k : G) * g * (rightCosetRepresentative K ((k : G) * g))⁻¹ =
    (k : G) * (g * (rightCosetRepresentative K g)⁻¹)
  unfold rightCosetRepresentative
  rw [hq, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rational conjugation on an abelian normal subgroup

Conjugation extends to the rationalization. When the subgroup is torsion free,
the extended action has exactly the same kernel, namely its centralizer.
Together with the rank bound this is a finite-dimensional representation of
the centralizer quotient, without a finite-generation assumption on the
abelian subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def rationalConjugation : G →*
    (RationalAbelianSpace H ≃ₗ[ℚ] RationalAbelianSpace H) :=
  rationalAbelianAut.comp (MulAut.conjNormal (H := H))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalSubgroupFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Pulling the rational action filtration back to the group

The rational filtration on an abelian normal subgroup gives actual ambient
subgroups. Commuting with the ambient group advances the filtration. Its last
term is trivial when the abelian subgroup is torsion free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def rationalPreimageSubgroup (W : Submodule ℚ (RationalAbelianSpace H)) : Subgroup H where
  carrier := {a | rationalAbelianMap (Additive.ofMul a) ∈ W}
  one_mem' := by
    change rationalAbelianMap 0 ∈ W
    rw [map_zero]
    exact W.zero_mem
  mul_mem' ha hb := by
    change rationalAbelianMap (Additive.ofMul _ + Additive.ofMul _) ∈ W
    rw [map_add]
    exact W.add_mem ha hb
  inv_mem' ha := by
    change rationalAbelianMap (-Additive.ofMul _) ∈ W
    rw [map_neg]
    exact W.neg_mem ha

def rationalSubgroupFiltration (n : ℕ) : Subgroup G :=
  (rationalPreimageSubgroup H (linearActionFiltration
    (fun g => (rationalConjugation H g).toLinearMap - 1) n)).map H.subtype

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentClassBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A uniform nilpotency-class bound from integral dimension

A maximal abelian normal subgroup of a nilpotent group is self-centralizing.
The faithful rational conjugation action bounds the lower central series
modulo that subgroup. Its pulled-back rational filtration bounds the remaining
series inside it. Each part has length at most the rational rank.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type} [Group G]

def rationalConjugationLinear (H : Subgroup G) [H.Normal] [IsMulCommutative H] :
    G →* Module.End ℚ (RationalAbelianSpace H) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (rationalConjugation H)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalInductionTensor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Induced restriction as the quotient regular representation tensored with a coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory Representation MonoidalCategory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

theorem normalInductionTensorRaw_invariant (n : N) :
    (normalInductionTensorRaw N A).comp
      ((Representation.tprod ((Representation.leftRegular ℤ G).comp N.subtype)
        (A.ρ.comp N.subtype)) n) = normalInductionTensorRaw N A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  ext a
  simp [normalInductionTensorRaw, mul_inv_rev, map_mul, Module.End.mul_apply]
  have hn : (QuotientGroup.mk' N) (n : G) = 1 := normalQuotient_mk_subgroup N n
  change MonoidAlgebra.single ((QuotientGroup.mk' N g)⁻¹ *
    (QuotientGroup.mk' N (n : G))⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a = _
  rw [hn, inv_one, mul_one]
  rfl

def normalInductionTensorLinear :
    Rep.ind N.subtype (Rep.res N.subtype A) →ₗ[ℤ] quotientRegularTensor N A :=
  Coinvariants.lift _ (normalInductionTensorRaw N A) (normalInductionTensorRaw_invariant N A)

@[simp]
theorem normalInductionTensorLinear_mk (g : G) (a : A) :
    normalInductionTensorLinear N A (IndV.mk _ _ g a) =
      MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a :=
  normalInductionTensorRaw_single N A g a

def normalInductionTensorHom :
    Rep.ind N.subtype (Rep.res N.subtype A) ⟶ quotientRegularTensor N A :=
  Rep.ofHom ⟨normalInductionTensorLinear N A, fun g => by
    apply IndV.hom_ext
    intro h
    ext a
    change normalInductionTensorLinear N A ((Representation.ind _ _) g (IndV.mk _ _ h a)) =
      (quotientRegularTensor N A).ρ g (normalInductionTensorLinear N A (IndV.mk _ _ h a))
    rw [ind_mk, normalInductionTensorLinear_mk, normalInductionTensorLinear_mk]
    simp [quotientRegularTensor, mul_inv_rev, map_mul, Module.End.mul_apply]⟩

def normalTensorQuotientTerm (c : G ⧸ N) :
    A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  normalTensorTerm N A (normalQuotientRepresentative N c)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCoupling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance of the pair coupling

The two commuting translations are written in both product charts. Haar
measure times the stationary probability gives the actual invariant coupling.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- Domain translation, expressed in the target-normalized chart. -/
def pairDomainTranslation (x : G) (q : G × NormalizedPair G Λ) :
    G × NormalizedPair G Λ :=
  (q.1 * q.2.val.1 x, normalizedTranslate x q.2)

/-- Target translation by `y⁻¹`, expressed in the source-normalized chart. -/
def pairInverseTargetTranslation (y : G) (q : NormalizedPair G Λ × G) :
    NormalizedPair G Λ × G :=
  (normalizedTranslate y q.1, (q.1.val.1 y)⁻¹ * q.2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCoefficientSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_succ _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorial coefficient system with colimit the rational numbers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear

def rationalCoefficientDiagram (G : Type) [Group G] : SequentialRepresentationDiagram G where
  obj _ := trivialIntegral G
  map i j _ := factorialMultiplier i j • 𝟙 _
  map_id i := by rw [factorialMultiplier_self, one_smul]
  map_comp i j k hij hjk := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul,
      factorialMultiplier_comp i j k hij hjk]

def rationalCoefficientInclusion (G : Type) [Group G] (i : ℕ) :
    trivialIntegral G ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨{ toFun := fun z => (z : ℚ) / (i.factorial : ℚ)
               map_add' := fun x y => by simp [add_div]
               map_smul' := fun r z => by simp [mul_div_assoc] },
    fun g => by rfl⟩

@[simp]
theorem rationalCoefficientInclusion_apply (G : Type) [Group G] (i : ℕ) (z : ℤ) :
    (rationalCoefficientInclusion G i).hom z = (z : ℚ) / (i.factorial : ℚ) := rfl

def rationalCoefficientColimit (G : Type) [Group G] :
    (rationalCoefficientDiagram G).ColimitCocone (Rep.trivial ℤ G ℚ) where
  ι := rationalCoefficientInclusion G
  comm i j hij := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change ℤ at z
    change ((factorialMultiplier i j * (z : ℤ) : ℤ) : ℚ) / (j.factorial : ℚ) =
      ((z : ℤ) : ℚ) / (i.factorial : ℚ)
    have he : (i.factorial : ℚ) * (factorialMultiplier i j : ℚ) = (j.factorial : ℚ) := by
      exact_mod_cast factorialMultiplier_factorial i j hij
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    push_cast
    field_simp
    calc
      (factorialMultiplier i j : ℚ) * (z : ℚ) * (i.factorial : ℚ) =
          (z : ℚ) * ((i.factorial : ℚ) * (factorialMultiplier i j : ℚ)) := by ring
      _ = (z : ℚ) * (j.factorial : ℚ) := congrArg (fun t : ℚ => (z : ℚ) * t) he
  surj q := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Rat.den_pos q) (le_refl q.den)
    refine ⟨q.den, q.num * (k : ℤ), ?_⟩
    change ((q.num * (k : ℤ) : ℤ) : ℚ) / (q.den.factorial : ℚ) = q
    rw [hk]
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos q).ne'
    have hk0 : (k : ℚ) ≠ 0 := by
      have hkn : k ≠ 0 := by intro h; simp only [h, mul_zero] at hk; exact Nat.factorial_ne_zero q.den hk
      exact_mod_cast hkn
    push_cast
    rw [mul_div_mul_right _ _ hk0]
    exact Rat.num_div_den q
  zero_exact i z hz := by
    change ℤ at z
    refine ⟨i, le_rfl, ?_⟩
    have hz' : ((z : ℤ) : ℚ) / (i.factorial : ℚ) = 0 := hz
    have hfac : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h0 : z = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz').resolve_right hfac
    subst z
    simp [rationalCoefficientDiagram]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalGroupDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational group dimension supplied by the integral rational coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

def rationalTrivialRetract :
    Retract (Rep.trivial ℚ G ℚ) (rationalizeRepresentation (Rep.trivial ℤ G ℚ)) := by
  let i : Rep.trivial ℚ G ℚ ⟶ rationalizeRepresentation (Rep.trivial ℤ G ℚ) :=
    Rep.ofHom ⟨(LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)),
      fun g => by
        apply LinearMap.ext
        intro q
        change q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)) =
          ((rationalizeRepresentation (Rep.trivial ℤ G ℚ)).ρ g)
            (q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)))
        erw [map_smul]
        rfl⟩
  let r : rationalizeRepresentation (Rep.trivial ℤ G ℚ) ⟶ Rep.trivial ℚ G ℚ :=
    Rep.ofHom ⟨rationalLinearExtension (LinearMap.id : ℚ →ₗ[ℤ] ℚ), fun g => by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q x
      rfl⟩
  refine ⟨i, r, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro q
  change rationalLinearExtension (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ))) = q
  rw [map_smul, rationalLinearExtension_tmul]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RescaledLieFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual rescalings lie in a compact family of normalized Lie laws

Both the law and the generator vectors are transported by the same rescaled
word basis. Basis-word identities hold exactly, independently of the scale.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I]

/-- The coordinate law and coordinate generators belonging to one rescaling. -/
def rescaledLieData (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (s : I → ℝ) (r : ℝ) :=
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The expanded conjugate scheme, evaluated as a polynomial in every
parameter, whether or not that parameter defines a group law. -/
def polynomialEndpointScheme {c n : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (p : (V →L[ℝ] V →L[ℝ] V) × (I → V)) (t : Fin n → ℝ) : V :=
  polynomialListProduct (dynkinProduct a p.1) (List.ofFn (fun k =>
    dynkinProduct a p.1
      (dynkinProduct a p.1 (polynomialWord (dynkinProduct a p.1) p.2 (w k))
        (t k • p.2 (i k)))
      (polynomialWord (dynkinProduct a p.1) p.2 (inverseGeneratorWord (w k)))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledTwoImageLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The alternating submersion for actual pairs of rescaled boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L]

def rescaledTwoImageData (X : I → L) (S : Finset (FreeMagma I))
    (β β₁ β₂ : WordBasisSelections X S) (s₁ s₂ : I → ℝ) (r : ℝ) :
    TwoImageData I (finrank ℝ L) :=
  let s := fun i => max (s₁ i) (s₂ i)
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  let b₁ := exponentialRescaleBasis (WordBasisSelections.basis X S β₁)
    (fun j => bracketWordExponent s₁ (β₁.val j)) r
  let b₂ := exponentialRescaleBasis (WordBasisSelections.basis X S β₂)
    (fun j => bracketWordExponent s₂ (β₂.val j)) r
  ((rescaledLieData X S β s r, (boxCoordinateChange b b₁, boxCoordinateChange b b₂)),
    ((rescaledLieData X S β₁ s₁ r).2, (rescaledLieData X S β₂ s₂ r).2))

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientConstants
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_apply _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the constant functions from the small coefficient ring

The constant copy of the integers is a subrepresentation. Its quotient is
again projective over the integers: evaluation at the identity splits the
underlying sequence. The splitting is not asserted to be equivariant.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientConstant : ℤ →ₗ[ℤ] SmallCoefficientRing G where
  toFun z := ⟨fun _ => z, ∅, fun _ _ _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientEvaluation : SmallCoefficientRing G →ₗ[ℤ] ℤ where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientEvaluation_constant (z : ℤ) :
    smallCoefficientEvaluation G (smallCoefficientConstant G z) = z := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralLogValue
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar values of a compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def spectralEigenvalue (S : Module.End ℂ V) (hS : IsUnit S)
    (μ : ℂ) (hμ : S.HasEigenvalue μ) : spectralUnitGroup S :=
  ⟨Units.mk0 μ (eigenvalue_ne_zero_of_isUnit S hS hμ),
    Subgroup.subset_closure (Or.inl hμ)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupBarResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroup inclusions on the free bar resolution -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

theorem subgroupBarResolutionMap_π :
    subgroupBarResolutionMap H ≫
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).π =
        (Rep.barResolution ℤ H).π := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution ℤ G).π.f 0).hom
      ((subgroupFreeInclusion H 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
        ((Rep.barResolution ℤ H).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
    rw [subgroupFreeInclusion_single, barResolution_pi_single, barResolution_pi_single]
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (Rep.trivial ℤ H ℤ) (n + 1) (by omega)).eq_of_tgt _ _

def subgroupBarResolutionHomotopy : Homotopy (subgroupBarResolutionMap H)
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).hom := by
  have hid : (Rep.barResolution ℤ H).π ≫
      (ChainComplex.single₀ (Rep ℤ H)).map (𝟙 (Rep.trivial ℤ H ℤ)) =
      (Rep.barResolution ℤ H).π := by
    exact (congrArg (fun f => (Rep.barResolution ℤ H).π ≫ f)
      ((ChainComplex.single₀ (Rep ℤ H)).map_id (Rep.trivial ℤ H ℤ))).trans
        (Category.comp_id _)
  apply ProjectiveResolution.liftHomotopy (P := Rep.barResolution ℤ H)
    (Q := (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))
    (𝟙 (Rep.trivial ℤ H ℤ)) (subgroupBarResolutionMap H)
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).hom
  · exact (subgroupBarResolutionMap_π H).trans hid.symm
  · exact (ProjectiveResolution.homotopyEquiv_hom_π (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).trans
        hid.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupShapiro
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Shapiro comparison associated to subgroup inclusion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G)

def subgroupShapiroIso (A : Rep ℤ H) (n : ℕ) :
    groupHomology A n ≅ groupHomology (Rep.ind H.subtype A) n := by
  classical
  exact coefficientNaturalHomologyIso
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)) A n ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso H A (Rep.barResolution ℤ G)) ≪≫
    ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype A))).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite truncated enveloping algebra and its faithful generators

A given nilpotent representation bounds the truncation degree and certifies
injectivity. No PBW theorem or additional representation input is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

def truncatedEnvelopingProjection (c : ℕ) : U →ₐ[R] TruncatedEnvelopingAlgebra R L c :=
  RingCon.mkₐ R (envelopingTruncationIdeal (R := R) (L := L) c).ringCon

def truncatedEnvelopingGenerator (c : ℕ) : L →ₗ⁅R⁆ TruncatedEnvelopingAlgebra R L c :=
  ((truncatedEnvelopingProjection (R := R) (L := L) c).toLieHom).comp η

theorem truncatedEnvelopingProjection_surjective (c : ℕ) :
    Function.Surjective (truncatedEnvelopingProjection (R := R) (L := L) c) :=
  RingCon.mkₐ_surjective _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

open Classical in
def productOccupationLaw {A D X : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D) (p : A × D → X) :
    ProbabilityMeasure X :=
  -- OpenAI's Mathlib maps by any function (a Dirac mass when it is not measurable); ours needs the
  -- measurability, so the non-measurable case is that Dirac mass explicitly
  if hp : AEMeasurable p ((μ : Measure A).prod (ν : Measure D)) then
    ProbabilityMeasure.map
      (⟨(μ : Measure A).prod (ν : Measure D), inferInstance⟩ : ProbabilityMeasure (A × D)) hp
  else
    ⟨Measure.dirac (p ((μ : Measure A).nonempty_of_isProbabilityMeasure_compat.some,
      (ν : Measure D).nonempty_of_isProbabilityMeasure_compat.some)), inferInstance⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledTupleVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of correlated tuple volume

The domain is an arbitrary tuple set. Its coordinates need not be
independent after the successful parameters have been retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold ENNReal Topology BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def rescaledTupleBases {h : ℕ} (X : I → L) (words : Finset (FreeMagma I))
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ) (r : ℝ) :=
  fun i => exponentialRescaleBasis (WordBasisSelections.basis X words (β i))
    (fun j => cost i ((β i).val j)) r

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMinorDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

def polynomialSliceDifferential {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.pi (fun i => polynomialDifferential (p i) (Fin.append v z))).comp
    (appendParameterLinear n k)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SwitchEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial difference word is the endpoint of the successful switches -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

/-- The last state after the specified sequence of switches. -/
def switchEndpoint : (m : ℕ) → G → SwitchParameters G m → G
  | 0, x, _ => x
  | m + 1, x, p => switchEndpoint m (x * p.1 * p.2.1⁻¹) p.2.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceBundleBlockPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact source-bundle boundaries and their individual paths -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N]

/-- The prefix-defined boundary uses the same conjugated bundle increments
as the Haar-preserving state-coordinate map. -/
def sourceBundleBoundary {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (v : Fin h → N) (j : ℕ) : N :=
  n * wordPrefix (fun k => if hk : k < h then φ ⟨k, hk⟩ (v ⟨k, hk⟩) else 1) j

omit [TopologicalSpace N] in
@[simp] theorem sourceBundleBoundary_zero {h : ℕ} (n : N)
    (φ : Fin h → N ≃* N) (v : Fin h → N) : sourceBundleBoundary n φ v 0 = n := by
  simp only [sourceBundleBoundary, wordPrefix_zero, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartPivot
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial size and exact height of a scaled word-chart pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

def wordChartPivot {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I] (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (r : ℝ) (z : Fin (finrank ℝ L) → ℝ) : L :=
  (exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
    (max (Real.log r) 0)).equivFun.symm z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree-zero complete cohomology from normalized syzygies

The transition maps are the actual connecting homomorphisms of the natural
short exact free-cover sequences. No vanishing theorem is assumed here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

instance normalizedCohomologyForward_directed (A : Rep.{0} ℤ G) :
    DirectedSystem (normalizedCohomologyStage A)
      (fun i j h => normalizedCohomologyForward A i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalHomologyAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on normal-subgroup homology with ambient coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k G)

theorem normalHomologyMap_one (i : ℕ) : normalHomologyMap k N A i 1 = 𝟙 _ := by
  rw [normalHomologyMap, ← groupHomology.map_id]
  apply groupHomology.map_congr
  · ext n
    exact congrArg (fun e : MulAut N => ((e n : N) : G)) (map_one (MulAut.conjNormal (H := N)))
  · apply LinearMap.ext
    intro x
    change A.ρ 1 x = x
    simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section

namespace PolycyclicRecognition

open Set

set_option maxHeartbeats 1000000 in
/-- The exact translated templates used by the three probe chains. -/
def polarSamplingTemplates {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (W →L[ℝ] ℝ)) (ε : ℝ) (w : W) (k : Fin 3) : Set W :=
  (fun x => x + w) '' ((fun z => threePolarRadii ε k • z) '' conePolarTemplate K)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original height is a homomorphism on the graded group -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {L G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I]

/-- Regard an additive coordinate height as a homomorphism on the
polynomial group. Its additivity is supplied by the preceding limit proof. -/
def polynomialCoordinateHeightHom
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : V → V → V) (hg : PolynomialGroupLaws m) (p : V →L[ℝ] W)
    (hp : ∀ x y, p (m x y) = p x + p y) :
    PolynomialCoordinateGroup m hg →* Multiplicative W where
  toFun x := Multiplicative.ofAdd (p x)
  map_one' := by change Multiplicative.ofAdd (p 0) = 1; rw [map_zero]; rfl
  map_mul' x y := congrArg Multiplicative.ofAdd (hp x y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem positiveWeightRay_add (α : V) :
    ∀ x ∈ positiveWeightRay α, ∀ y ∈ positiveWeightRay α, x + y ∈ positiveWeightRay α := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩
  exact ⟨c + d, add_pos hc hd, (add_smul c d α).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent interval laws for the root increments -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]

variable [MeasurableSpace N]

def rootIntervalLaw (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) : Measure N :=
  Measure.map (rootIntervalSample Exp letters X s r j) (uniformIntervalLaw R)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSupports
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact supports of the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

/-- The closed interval image carries the complete sampling law. -/
def rootIntervalSupport (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) : Set N :=
  rootIntervalSample Exp letters X s r j '' closedBall 0 R

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure in genuine semidirect product coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure

variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D] [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

@[instance_reducible]
def semidirectProductMeasurableSpace : MeasurableSpace (N ⋊[φ] D) :=
  borel (N ⋊[φ] D)

omit [IsTopologicalGroup N] [IsTopologicalGroup D] [MeasurableSpace N]
  [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D] in
theorem semidirectProduct_borelSpace :
    let := semidirectProductMeasurableSpace φ
    BorelSpace (N ⋊[φ] D) := by
  let := semidirectProductMeasurableSpace φ
  exact ⟨rfl⟩

variable [MeasurableSpace (N ⋊[φ] D)] [BorelSpace (N ⋊[φ] D)]
  (μN : Measure N) (μD : Measure D)

def semidirectProductMeasure : Measure (N ⋊[φ] D) :=
  Measure.map (semidirectProductHomeomorph φ).symm (μN.prod μD)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SpectralLieDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compatible spectral logarithm is a Lie derivation

The multiplicative relations among eigenvalues are essential: brackets of
eigenvectors have the product eigenvalue, so their logarithmic weights add.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable {L : Type} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

def spectralLieDerivation (S : L ≃ₗ⁅ℂ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap)
    (l : spectralUnitGroup S.toLinearMap →* Multiplicative ℂ) : LieDerivation ℂ L L := by
  let D := semisimpleSpectralOperator S.toLinearMap hS (spectralLogValue S.toLinearMap l)
  let B := (LieAlgebra.ad ℂ L).toLinearMap
  let F : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => D.comp (B x)
      map_add' := by intros; simp [LinearMap.comp_add]
      map_smul' := by intros; simp [LinearMap.comp_smul] }
  let G : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => B (D x) + (B x).comp D
      map_add' := by intros; simp [LinearMap.add_comp]; abel
      map_smul' := by intros; simp [smul_add, LinearMap.smul_comp] }
  have he : F = G := by
    apply semisimple_bilinear_ext S.toLinearMap hS
    intro μ ν x y hx hy
    change D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hμ : Module.End.HasEigenvalue S.toLinearMap μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩
    have hν : Module.End.HasEigenvalue S.toLinearMap ν :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
    have hu : IsUnit S.toLinearMap := (Module.End.isUnit_iff _).mpr S.bijective
    let z := spectralEigenvalue S.toLinearMap hu μ hμ
    let w := spectralEigenvalue S.toLinearMap hu ν hν
    have hm : spectralLogValue S.toLinearMap l (μ * ν) =
        spectralLogValue S.toLinearMap l μ + spectralLogValue S.toLinearMap l ν :=
      spectralLogValue_mul S.toLinearMap l z w
    have hb : ⁅x, y⁆ ∈ Module.End.eigenspace S.toLinearMap (μ * ν) := by
      rw [Module.End.mem_eigenspace_iff]
      change S ⁅x, y⁆ = (μ * ν) • ⁅x, y⁆
      have hx' : S x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      have hy' : S y = ν • y := Module.End.mem_eigenspace_iff.mp hy
      rw [S.map_lie, hx', hy', smul_lie, lie_smul, smul_smul]
    rw [show D ⁅x, y⁆ = _ from semisimpleSpectralOperator_apply _ _ _ hb,
      show D x = _ from semisimpleSpectralOperator_apply _ _ _ hx,
      show D y = _ from semisimpleSpectralOperator_apply _ _ _ hy,
      hm, smul_lie, lie_smul, add_smul]
  refine { D with leibniz' := ?_ }
  intro x y
  have h := congrArg (fun T : L →ₗ[ℂ] L →ₗ[ℂ] L => T x y) he
  change D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆ at h
  rw [h, sub_eq_add_neg, lie_skew (D x) y, add_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentLieFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real Lie-automorphism flow through a given unipotent automorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance unipotentFlowRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norms obtained by assigning costs to group elements

The infimum of the costs of finite product expressions is subadditive.
A pre-existing group norm below the costs guarantees separation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

open Set
variable {G : Type*} (c : G → ℝ≥0)

variable [Group G]

theorem weightedWordNorm_le (g : G) : weightedWordNorm c g ≤ c g := by
  simpa using weightedWordNorm_le_cost c [g]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-length control by a weighted norm

Short-cost factors are accumulated until they leave a small identity ball.
Each completed block has bounded word length and pays for that length.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type*} [Group G]

/-- The residual factor stays in the small ball; every flushed block is
charged against the accumulated cost. -/
theorem seminorm_product_cost_bound
    (p w : GroupSeminorm G) (c : G → ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpc : ∀ g, p g ≤ c g)
    (hlocal : ∀ g, p g ≤ δ → w g ≤ 1)
    (hwc : ∀ g, w g ≤ max 1 (c g : ℝ))
    (l : List G) :
    w l.prod ≤ (4 / δ) * (productCost c l : ℝ) + 1 := by
  let C : ℝ := 4 / δ
  have hC : 0 < C := div_pos (by norm_num) hδ
  have hCδ : C * δ = 4 := by dsimp [C]; field_simp
  have hC2 : 2 ≤ C := by nlinarith
  have hmain : ∀ (l : List G) (a : G) (r : ℝ),
      p a ≤ r → 0 ≤ r → r < δ / 2 →
      w (a * l.prod) ≤ C * (r + (productCost c l : ℝ)) + 1 := by
    intro l
    induction l with
    | nil =>
      intro a r ha hr hrδ
      simpa only [List.prod_nil, mul_one, productCost_nil, NNReal.coe_zero, add_zero] using
        (hlocal a (ha.trans (by linarith))).trans
          (by have := mul_nonneg hC.le hr; linarith)
    | cons b l ih =>
      intro a r ha hr hrδ
      have hb0 : (0 : ℝ) ≤ c b := (c b).coe_nonneg
      by_cases hsmall : r + (c b : ℝ) < δ / 2
      · have hab : p (a * b) ≤ r + (c b : ℝ) :=
          (p.mul_le' a b).trans (add_le_add ha (hpc b))
        have h := ih (a * b) (r + c b) hab (by linarith) hsmall
        simpa only [List.prod_cons, productCost_cons, NNReal.coe_add, add_assoc,
          mul_assoc] using h
      · have hpaid : w (a * b) ≤ C * (r + (c b : ℝ)) := by
          have hsum : δ / 2 ≤ r + (c b : ℝ) := le_of_not_gt hsmall
          by_cases hb : (c b : ℝ) < δ / 2
          · have hab : p (a * b) ≤ δ := by
              have hp := (p.mul_le' a b).trans (add_le_add ha (hpc b))
              change p (a * b) ≤ r + (c b : ℝ) at hp
              linarith
            have hpay : 1 ≤ C * (r + (c b : ℝ)) := by nlinarith
            exact (hlocal (a * b) hab).trans hpay
          · have hbδ : δ / 2 ≤ (c b : ℝ) := le_of_not_gt hb
            have haW : w a ≤ 1 := hlocal a (ha.trans (by linarith))
            have hbW := hwc b
            have hpay : 1 + max 1 (c b : ℝ) ≤ C * (c b : ℝ) := by
              rcases le_total (c b : ℝ) 1 with h | h
              · rw [max_eq_left h]
                nlinarith
              · rw [max_eq_right h]
                nlinarith
            exact ((w.mul_le' a b).trans (add_le_add haW hbW)).trans
              (hpay.trans (mul_le_mul_of_nonneg_left (by linarith) hC.le))
        have hrest := ih 1 0 (by simp) le_rfl (half_pos hδ)
        simp only [one_mul, zero_add] at hrest
        have hbound := (w.mul_le' (a * b) l.prod).trans (add_le_add hpaid hrest)
        change w (a * (b * l.prod)) ≤ C * (r + ((c b : ℝ) + (productCost c l : ℝ))) + 1
        rw [← mul_assoc]
        calc
          _ ≤ C * (r + (c b : ℝ)) + (C * (productCost c l : ℝ) + 1) := hbound
          _ = _ := by ring
  simpa only [one_mul, zero_add] using hmain l 1 0 (by simp) le_rfl (half_pos hδ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerSemidirectLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral semidirect product is the lattice in its real extension -/

noncomputable section
namespace PolycyclicRecognition
variable {H N : Type*} [Group H] [Group N]

def realIntegerSemidirectMap (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (e : H →* N) (he : ∀ x, e (a x) = φ (Multiplicative.ofAdd 1) (e x)) :
    (H ⋊[integerPowerAction a] Multiplicative ℤ) →* (N ⋊[φ] Multiplicative ℝ) :=
  SemidirectProduct.map e integerTimeHom (by
    intro n
    ext x
    change e ((a ^ n.toAdd) x) = φ (Multiplicative.ofAdd (n.toAdd : ℝ)) (e x)
    rw [realAction_int]
    exact mulAut_zpow_semiconj a _ e he n.toAdd x)

attribute [local instance] semidirectProductTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

attribute [local instance] OAI.ThompsonNonamenability.instFactLeENNRealOfNat_solutions
/-- A separator gives one bounded real function for each translation. -/
def separatorCoordinate {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (h : {h : G // h ∈ S}) : BoundedReal G :=
  ⟨fun g => ell (lp.single 1 (h, g) 1), memℓp_infty ⟨‖ell‖, by
    rintro y ⟨g, rfl⟩
    have hb := ell.le_opNorm (lp.single 1 (h, g) 1)
    simpa only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)),
      norm_one, mul_one] using hb⟩⟩

omit [Group G] in
@[simp]
theorem separatorCoordinate_apply [Group G] {S : Finset G}
    (ell : DefectSpace S →L[ℝ] ℝ) (h : {h : G // h ∈ S}) (g : G) :
    separatorCoordinate ell h g = ell (lp.single 1 (h, g) 1) := rfl

/-- The finite sum whose mean vanishes by left invariance. -/
def separatorDefect {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : BoundedReal G :=
  ∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Unitary_Packing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Volume packing in the unitary group

`volume_packing`, bounding how many almost-orthogonal translates fit in a ball, together with
the auxiliary inner product `FreshInnerProduct`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


instance instAddCommGroupFreshInnerProduct (V : Type*) [base_comm : AddCommGroup V]: AddCommGroup (FreshInnerProduct V) := base_comm
instance instModuleComplexFreshInnerProduct (V : Type*) [AddCommGroup V] [base_module : Module ℂ V]: Module ℂ (FreshInnerProduct V) := base_module


attribute [-simp] MeasureTheory.Measure.inv_eq_self

attribute [local implicit_reducible] FreshInnerProduct
end


