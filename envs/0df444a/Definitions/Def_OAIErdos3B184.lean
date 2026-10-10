-- Prove2me | Definitions.Def_OAIErdos3B184
-- name    : OAIErdos3B184
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T07:26:43.742976+00:00
-- url     : https://prove2.me/theorems/3294f2aa-a95c-49ab-ae93-e0c04d8d97c2
-- title:
--   OpenAI Erdős-3 split, definitions bundle 185 of 196
-- statement:
--   Definitions bundle 185 of 196 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B183`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 185 available.
--
--   Modules: `OAI.Erdos3.NativeRankInterval.SunflowerWitness`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.exists_bounded_coefficient_corrections`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.exists_projected_corrections`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.horizontalImage_eq`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.mono`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.mono_projectedDenominator`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedDenominator`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedDenominator_bound`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedDenominator_pos`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient_coe`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient_horizontal`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient_native_component`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient_native_coordinates`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedOrbitCoefficient_native_log_mod_kernel`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentative`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentativeLayer`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentative_grid`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentative_horizontal`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentative_mem`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedRepresentative_slow`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projectedSymbol_native_component`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projection`, `OAI.Erdos3.NativeRankInterval.SunflowerWitness.projection_mem_candidates`, `OAI.Erdos3.NativeRankRelation.CommonData`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientAlphabet`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.combined_free_sunflower`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.commonFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.commonFreeLift_range`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.correlation_four_frequency`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.correlation_refined_four_identity`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.dependentFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.dependentFreeLift_range`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_free_tree_linearization`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.finite_combined_free_sunflower`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_coefficientFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_commonFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_commonFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_dependentFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_dependentFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeEvaluation_generator`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.freeFrequency`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.free_refined_four_identity`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.generator`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.generator_height`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.generator_mem_common`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.generator_mem_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.mono`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realCommonFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realCommonFreeLift_baseChange`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realCommonFreeLift_mem`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realDependentFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realDependentFreeLift_baseChange`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realDependentFreeLift_mem`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realEvaluation_commonFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.realEvaluation_dependentFreeLift`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientFreeLieAlgebra`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_anchor_polynomial_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_anchor_representative_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_bounded_native_dependent_approximations`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_native_dependent_approximations`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_native_sparse_approximations`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.exists_uniform_native_degree_approximations`, `OAI.Erdos3.NativeRankRelation.CommonData.SparseAnchors.shifts_subset`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientAlphabetFintype`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientAlphabet_card`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientDegree`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFourSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeFiltration`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeGenerator`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeGenerator_mem_combined`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeGenerator_mem_dependent`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeGenerator_mem_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeSpan_le_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientIsDependent`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientLayerIndex`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientWeight`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientWeight_eq_layerIndex`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientWeight_pos`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficient_four_frequency`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficient_sunflower`, `OAI.Erdos3.NativeRankRelation.CommonData.commonCoefficientSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.commonCoefficientSpace_le`, `OAI.Erdos3.NativeRankRelation.CommonData.commonFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.commonFreeSpan_le_coefficientFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.commonFreeSpan_le_dependentWordLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.commonFreeSpan_le_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.coordinateSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.coordinateSpace_dependent`, `OAI.Erdos3.NativeRankRelation.CommonData.coordinateSpace_eq_map`, `OAI.Erdos3.NativeRankRelation.CommonData.coordinateSpace_first`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentCoefficientSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentCoefficientSpace_le_common`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentFreeSpan_le_coefficientFreeSpan`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentFreeSpan_le_dependentWordLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentFreeSpan_le_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentWordIdeal`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentWordLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentWordLayer_antitone`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_bounded_coefficient_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_bounded_coordinate_generators`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficientFreeSpan_basis`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficient_space_bases`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_common_projected_denominator`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coordinate_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coordinate_generators`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_dependentFreeSpan_basis`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_dependent_remainder`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_real_dependent_remainder`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_sparse_anchors`, `OAI.Erdos3.NativeRankRelation.CommonData.horizontal`, `OAI.Erdos3.NativeRankRelation.CommonData.horizontalImage_eq`, `OAI.Erdos3.NativeRankRelation.CommonData.horizontal_frequency`, `OAI.Erdos3.NativeRankRelation.CommonData.mem_coefficientFourSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.mem_real_coefficientFourSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.mono`, `OAI.Erdos3.NativeRankRelation.CommonData.native_coefficient_mem_common`, `OAI.Erdos3.NativeRankRelation.CommonData.native_coefficient_mem_dependent`, `OAI.Erdos3.NativeRankRelation.CommonData.native_scaled_correction`, `OAI.Erdos3.NativeRankRelation.CommonData.paired_affine_orbit_coefficient_mem_comparison`, `OAI.Erdos3.NativeRankRelation.CommonData.realCoefficientFourSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.realCoordinateSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.realCoordinateSpace_eq_image`, `OAI.Erdos3.NativeRankRelation.CommonData.realCoordinateSpace_mem`, `OAI.Erdos3.NativeRankRelation.CommonData.real_dependent_coordinateSpace_eq`, `OAI.Erdos3.NativeRankRelation.CommonData.spaces_le_fourHorizontalLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.spaces_mem_candidates`, `OAI.Erdos3.NativeRankRelation.CommonData.sunflower_bracket`, `OAI.Erdos3.NativeRankRelation.CommonData.sunflower_representatives`, `OAI.Erdos3.NativeRankRelation.CommonData.variable_coefficient_graph_energy`, `OAI.Erdos3.NativeRankRelation.CommonData.variable_graph_small_difference`, `OAI.Erdos3.exists_common_rank_interval_data`, `OAI.Erdos3.exists_common_rank_projection_family`, `OAI.Erdos3.exists_common_rank_relation`, `OAI.Erdos3.exists_native_common_dependent_factorization`, `OAI.Erdos3.exists_native_common_rank_relation`, `OAI.Erdos3.exists_native_degree_approximation_bound`, `OAI.Erdos3.exists_native_dependent_coordinate_family`, `OAI.Erdos3.exists_native_dependent_polynomial_corrections`, `OAI.Erdos3.exists_native_dependent_representative_family`, `OAI.Erdos3.exists_native_frozen_common_factorization`, `OAI.Erdos3.exists_native_periodic_common_factorization`, `OAI.Erdos3.exists_rank_sunflower_witness`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B154
import Definitions.Def_OAIErdos3B185

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

end NativeDegreeRankFamily

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

structure SunflowerWitness (I : NativeRankInterval W out H t branch p q) (P : ℝ) where
  index : Fin I.expansion.count
  lowerRank : ((I.expansion.model index).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r
  lower_complexity : lowerRank.ComplexityLE P
  lower_top : lowerRank.realSubgroup s r = ⊥
  adapted : (piRank (I.productModels index) (I.productRanks index lowerRank)).AdaptedData
  adapted_complexity : adapted.rank.ComplexityLE P
  forward : ∀ j k, rationalLogHeight ((pi (I.productModels index)).basis.repr (adapted.basis j) k) ≤ P
  backward : ∀ k j, rationalLogHeight (adapted.basis.repr ((pi (I.productModels index)).basis k) j) ≤ P
  denominator : ℕ
  subalgebra : LieSubalgebra ℚ (pi (I.productModels index)).filtration.AssociatedGraded
  spanning : Fin (finrank ℚ (∀ k : Option (Fin 4),
    optionLieSpace (I.expansion.L index) (fun _ : Fin 4 => W.L) k)) →
    (pi (I.productModels index)).filtration.AssociatedGraded
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp P
  span : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers)
    adapted.weight subalgebra.toSubmodule
  height : ∀ j k, rationalLogHeight
    (((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers).repr
      (spanning j) k) ≤ P
  bracket : I.BracketKernel index subalgebra
  sunflower : I.SunflowerKernel index subalgebra
  factorization : (pi (I.productModels index)).filtration.SymbolFactorizationIn
    adapted.basis adapted.weight adapted.layers (fun _ : Unit => (I.length : ℝ))
    (I.productSymbol index adapted.basis adapted.weight adapted.layers) P denominator subalgebra

namespace SunflowerWitness

variable {I : NativeRankInterval W out H t branch p q} {P : ℝ} (D : I.SunflowerWitness P)

noncomputable def projection (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  I.refilteredProjectionImage D.index D.subalgebra d

theorem projection_mem_candidates (hP : 0 ≤ P) (d : ℕ) :
    D.projection d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ :=
  I.refilteredProjectionImage_mem_candidates D.index D.lowerRank D.adapted D.subalgebra
    D.spanning D.span hP D.adapted_complexity D.forward D.height d

theorem horizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage D.index D.subalgebra d =
      W.rank.filtration.horizontalImageOfSubmodule (D.projection d) d :=
  I.refilteredHorizontalImage_eq D.index D.subalgebra d

end SunflowerWitness

end NativeRankInterval

theorem exists_rank_sunflower_witness (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      Nonempty (I.SunflowerWitness ((p + C) ^ C)) := by
  obtain ⟨C, hC, hexists⟩ := exists_rank_interval_sunflower s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, hsunflower, hinside⟩ := hexists hp hbp I hlarge
  exact ⟨{
    index := i
    lowerRank := R₀
    lower_complexity := hR₀
    lower_top := hzero
    adapted := F
    adapted_complexity := hF
    forward := hforward
    backward := hback
    denominator := l
    subalgebra := U
    spanning := v
    denominator_pos := hl
    denominator_bound := hlp
    span := hv
    graded := hU
    height := hheight
    bracket := hker
    sunflower := hsunflower
    factorization := hinside
  }⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_projection_family
    {α : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : ∀ a, NativeRankInterval W out H (t a) branch p q)
    (S : Finset α) (hS : S.Nonempty) (hP : 0 ≤ P)
    (D : ∀ a ∈ S, (I a).SunflowerWitness P) :
    ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-(3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
        Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2)) * (s + 1)) *
        S.card ≤ (T.card : ℝ) ∧
      (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊) ∧
      ∀ a ∈ T, ∃ E : (I a).SunflowerWitness P,
        (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
        ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
          W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  classical
  let code (a : α) : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L) :=
    if ha : a ∈ S then fun d => (D a ha).projection d.val else 0
  have hcode (a : α) (ha : a ∈ S) : code a = fun d => (D a ha).projection d.val := by
    simp only [code, dif_pos ha]
  have hmem : ∀ a ∈ S, ∀ d, code a d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
    intro a ha d
    rw [hcode a ha]
    exact (D a ha).projection_mem_candidates hP d.val
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hsize⟩ := exists_common_height_bounded_subspace_family
    W.fourRankBasis S hS code (Fintype.card (Σ _ : Fin 4, Fin W.dim))
    (refiltrationCoordinateBudget_nonneg hP) hmem
  refine ⟨code a₀, T, hTS, ⟨a₀, haT⟩, ?_, hmem a₀ ha₀, ?_⟩
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hsize
  · intro a ha
    let E := D a (hTS ha)
    have heq (d : Fin (s + 1)) : E.projection d.val = code a₀ d := by
      have h := congrFun (hcommon a ha) d
      rwa [hcode a (hTS ha)] at h
    exact ⟨E, heq, fun d => (E.horizontalImage_eq d.val).trans (congrArg
      (fun B => W.rank.filtration.horizontalImageOfSubmodule B d.val) (heq d))⟩

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

namespace SunflowerWitness

variable {I} {P : ℝ} (D : I.SunflowerWitness P)

theorem exists_projected_corrections (hs : 1 ≤ s) :
    ∃ E R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (pi (I.productModels D.index)).filtration.SymbolSlowBound
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
        (fun _ => (I.length : ℝ)) (Real.exp P) E ∧
      (pi (I.productModels D.index)).filtration.SymbolRationalGrid
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R ∧
      ∀ α : Unit →₀ ℕ,
        (I.projectedCoefficient D.index α).baseChange ℝ
            (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord -
          (I.projectedCoefficient D.index α).baseChange ℝ E.coord -
          (I.projectedCoefficient D.index α).baseChange ℝ R.coord ∈
        (I.refilteredHorizontalImage D.index D.subalgebra (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  exact W.rank.filtration.projectedHorizontal_factorization (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index) hs
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => (I.length : ℝ))
    (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers)
    P D.denominator D.subalgebra D.factorization

end SunflowerWitness

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

noncomputable def mono (D : I.SunflowerWitness P) (hPQ : P ≤ Q) : I.SunflowerWitness Q :=
  { D with
    lower_complexity := D.lower_complexity.mono D.lowerRank hPQ
    adapted_complexity := D.adapted_complexity.mono D.adapted.rank hPQ
    forward := fun j k => (D.forward j k).trans hPQ
    backward := fun k j => (D.backward k j).trans hPQ
    denominator_bound := D.denominator_bound.trans (Real.exp_le_exp.mpr hPQ)
    height := fun j k => (D.height j k).trans hPQ
    factorization := NilpotentLieFiltration.SymbolFactorizationIn.mono
      (pi (I.productModels D.index)).filtration D.adapted.basis D.adapted.weight D.adapted.layers
      D.factorization hPQ (fun _ => by exact_mod_cast I.length_pos) }

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

noncomputable def projectedRepresentative
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : ℝ ⊗[ℚ] (Fin 4 → W.L) :=
  (I.rankProjection D.index).toLinearMap.baseChange ℝ
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord) α)

noncomputable def projectedDenominator : ℕ :=
  matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
    D.denominator

theorem projectedDenominator_pos : 0 < D.projectedDenominator :=
  Nat.mul_pos (matrixDenominator_pos _) D.denominator_pos

theorem projectedDenominator_bound (hP : 0 ≤ P) :
    (D.projectedDenominator : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) := by
  have hdim := D.adapted_complexity.1.1
  apply NilpotentLieFiltration.original_coordinate_denominator_bound D.adapted.basis
    (pi (I.productModels D.index)).basis hP
  · simpa only [Fintype.card_fin] using hdim
  · simpa only [← finrank_eq_card_basis (pi (I.productModels D.index)).basis] using hdim
  · exact D.forward
  · exact D.denominator_bound

theorem projectedRepresentative_slow (hP : 0 ≤ P)
    (E : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hE : (pi (I.productModels D.index)).filtration.SymbolSlowBound
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
      (fun _ => (I.length : ℝ)) (Real.exp P) E) (α : Unit →₀ ℕ) (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative E α) j| ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  apply I.real_rankProjection_abs_bound D.index
  intro k
  apply (pi (I.productModels D.index)).filtration.realSymbolRepresentative_slow_original_coordinates
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) (fun _ => (I.length : ℝ)) (fun _ => by exact_mod_cast I.length_pos) hP
  · simpa only [Fintype.card_fin] using D.adapted_complexity.1.1
  · exact D.forward
  · exact hE

theorem projectedRepresentative_grid
    (R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hR : (pi (I.productModels D.index)).filtration.SymbolRationalGrid
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R)
    (α : Unit →₀ ℕ) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative R α) j) ∈
      realDenominatorGrid D.projectedDenominator := by
  unfold projectedDenominator projectedRepresentative
  have hgrid := (pi (I.productModels D.index)).filtration.realSymbolRepresentative_original_grid
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) D.denominator R hR α
  have hp := I.real_rankProjection_grid D.index
    (matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
      D.denominator)
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) R.coord) α) hgrid
  convert hp using 2

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedRepresentative_mem
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : D.projectedRepresentative X α ∈
      (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  have h := W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
    ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
  convert h using 2
  dsimp only [projectedRepresentative, NilpotentLieFiltration.realAdaptedSymbolRepresentative]

noncomputable def projectedRepresentativeLayer
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨D.projectedRepresentative X α, D.projectedRepresentative_mem X α⟩

theorem projectedRepresentative_horizontal
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedRepresentativeLayer X α) =
      (I.projectedCoefficient D.index α).baseChange ℝ X.coord := by
  have h := W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
    (D.projectedRepresentativeLayer X α) (by
      dsimp only [projectedRepresentativeLayer, projectedRepresentative,
        NilpotentLieFiltration.realAdaptedSymbolRepresentative])
  rwa [NilpotentLieFiltration.realPolynomialSymbolMap_representative] at h

noncomputable def projectedOrbitCoefficient (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨(I.rankProjection D.index).toLinearMap.baseChange ℝ (coefficients (I.productOrbit D.index).log α),
    W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
      (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
      ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩⟩

@[simp] theorem projectedOrbitCoefficient_coe (α : Unit →₀ ℕ) :
    (D.projectedOrbitCoefficient α : ℝ ⊗[ℚ] (Fin 4 → W.L)) =
      (I.rankProjection D.index).toLinearMap.baseChange ℝ
        (coefficients (I.productOrbit D.index).log α) := rfl

theorem projectedOrbitCoefficient_horizontal (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedOrbitCoefficient α) =
      (I.projectedCoefficient D.index α).baseChange ℝ
        (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord := by
  exact W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (D.projectedOrbitCoefficient α) rfl

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

theorem projectedSymbol_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.projectedCoefficient D.index α).baseChange ℝ
          (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  have h := W.rank.filtration.projectedHorizontalSymbolCoefficient_native
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) hs D.adapted.basis D.adapted.weight D.adapted.layers
    c τ hG (fun _ : Unit => 1) α
    ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (W.rank.orbitEquiv (fun _ => 1)
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit) k (by
      exact (I.rankProjection_component_log D.index k).trans
        (W.rank.orbitEquiv_log (fun _ : Unit => 1)
          (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
            ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).symm)
  exact h.trans (W.fourPoint_horizontalCoefficient hs c τ hG out
    (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) α
    ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem projectedOrbitCoefficient_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α)) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  exact (congrArg ((LinearMap.proj k).baseChange ℝ) (D.projectedOrbitCoefficient_horizontal α)).trans
    (D.projectedSymbol_native_component hs c τ hG α k)

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

variable {A κ : Type*} {s r : ℕ} {b : ℝ} (W : NativeDegreeRankFamily s r A b)

end NativeDegreeRankFamily

namespace NativeRankInterval.SunflowerWitness

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedOrbitCoefficient_native_log_mod_kernel
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (k : Fin 4) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (D.projectedOrbitCoefficient α).val k -
      coefficients (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α ∈
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).baseChange ℝ := by
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let v := W.rank.filtration.realFourLayerComponent (Finsupp.weight (fun _ : Unit => 1) α) k
    (D.projectedOrbitCoefficient α)
  let z : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ :=
    ⟨coefficients (W.orbit a).log α, W.logCoefficient_mem_rank_one α a⟩
  have heq : W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) z :=
    (W.rank.filtration.realFourLayerComponent_horizontal _ k (D.projectedOrbitCoefficient α)).symm.trans
      ((D.projectedOrbitCoefficient_native_component hs c τ hG α k).trans
        (W.horizontalCoefficient_real_log hs c τ hG α a z rfl))
  have h := (W.rank.filtration.realHorizontalMap_eq _ v z).mp heq
  simpa only [v, z, a, W.rank.filtration.realFourLayerComponent_coe, real_four_projection] using h

end NativeRankInterval.SunflowerWitness
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankOrbitCoefficientCorrections
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem exists_bounded_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P) :
    ∃ E R : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (R α).val j) ∈
        realDenominatorGrid D.projectedDenominator) ∧
      ∀ α, W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α - E α - R α) ∈
        (I.refilteredHorizontalImage D.index D.subalgebra
          (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  obtain ⟨E, R, hE, hR, hres⟩ := D.exists_projected_corrections hs
  refine ⟨D.projectedRepresentativeLayer E, D.projectedRepresentativeLayer R, ?_, ?_, ?_⟩
  · intro α j
    exact D.projectedRepresentative_slow hP E hE α j
  · intro α
    exact D.projectedRepresentative_grid R hR α
  · intro α
    let f := W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
    have hinner := (map_sub f (D.projectedOrbitCoefficient α) (D.projectedRepresentativeLayer E α)).trans
      (congrArg₂ (fun x y => x - y) (D.projectedOrbitCoefficient_horizontal α)
        (D.projectedRepresentative_horizontal E α))
    have heq := (map_sub f (D.projectedOrbitCoefficient α - D.projectedRepresentativeLayer E α)
      (D.projectedRepresentativeLayer R α)).trans
        (congrArg₂ (fun x y => x - y) hinner (D.projectedRepresentative_horizontal R α))
    exact (congrArg (fun v => v ∈ (I.refilteredHorizontalImage D.index D.subalgebra
      (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ) heq).mpr (hres α)

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_interval_data (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : ∀ a, NativeRankInterval W out H (t a) branch p p) →
      (S : Finset α) → S.Nonempty →
      (∀ a ∈ S, Real.exp ((p + C) ^ C) ≤ ((I a).length : ℝ)) →
      ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
        T ⊆ S ∧ T.Nonempty ∧ Real.exp (-((p + C) ^ C)) * S.card ≤ (T.card : ℝ) ∧
        (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
          ⌈Real.exp (refiltrationCoordinateBudget ((p + C) ^ C))⌉₊) ∧
        ∀ a ∈ T, ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
          (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
          ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
            W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  obtain ⟨c, _, hwitness⟩ := exists_rank_sunflower_witness s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_common_data_budget s c
  refine ⟨C, hC, ?_⟩
  intro α r N _ b p W out H t branch hp hbp I S hS hlarge
  let P := (p + c) ^ c
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hPC, hcostC⟩ := hbudget p hp
  have hQ : 0 ≤ (p + C) ^ C := hP.trans hPC
  have hex (a : α) (ha : a ∈ S) : Nonempty ((I a).SunflowerWitness P) :=
    hwitness hp hbp (I a) ((Real.exp_le_exp.mpr hPC).trans (hlarge a ha))
  let D (a : α) (ha : a ∈ S) := Classical.choice (hex a ha)
  obtain ⟨K, T, hTS, hT, hsize, _, hdata⟩ := exists_common_rank_projection_family I S hS hP D
  have hdim : (W.dim : ℝ) ≤ p := W.complexity.1.1.trans hbp
  have hcard : Fintype.card (Σ _ : Fin 4, Fin W.dim) = 4 * W.dim := by simp
  have hn : (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) ≤ 4 * p := by
    rw [hcard, Nat.cast_mul]
    norm_num
    linarith
  have hA := refiltrationCoordinateBudget_nonneg hP
  have hcost : 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      (p + C) ^ C := by
    apply le_trans _ hcostC
    change 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget P + 2) * (s + 1)
    gcongr
  have hnew (a : α) (ha : a ∈ T) : ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
      (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
      ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
    obtain ⟨E, hproj, hhor⟩ := hdata a ha
    exact ⟨E.mono hPC, hproj, hhor⟩
  refine ⟨K, T, hTS, hT, ?_, ?_, hnew⟩
  · apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · obtain ⟨a, ha⟩ := hT
    obtain ⟨E, hproj, _⟩ := hnew a ha
    intro d
    rw [← hproj d]
    exact E.projection_mem_candidates hQ d.val

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

structure CommonData (R : NativeRankRelation W out H p q) (P : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  subset : quadruples ⊆ R.quadruples
  nonempty : quadruples.Nonempty
  density : Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  spaces : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)
  witness : ∀ t, (ht : t ∈ quadruples) → (R.interval ⟨t, subset ht⟩).SunflowerWitness P
  projection : ∀ t (ht : t ∈ quadruples) (d : Fin (s + 1)),
    (witness t ht).projection d.val = spaces d

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} (D : R.CommonData P)

theorem spaces_mem_candidates (hP : 0 ≤ P) (d : Fin (s + 1)) :
    D.spaces d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  exact (D.witness t ht).projection_mem_candidates hP d.val

theorem horizontalImage_eq (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (d : Fin (s + 1)) :
    (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage
      (D.witness t ht).index (D.witness t ht).subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val := by
  rw [(D.witness t ht).horizontalImage_eq, D.projection t ht d]

noncomputable def mono (hPQ : P ≤ Q) : R.CommonData Q :=
  { D with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
      (by positivity)).trans D.density
    witness := fun t ht => (D.witness t ht).mono hPQ
    projection := fun t ht d => D.projection t ht d }

end CommonData

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def horizontal (d : Fin (s + 1)) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d.val) :=
  W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val

theorem horizontal_frequency (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ D.horizontal (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 3)) = 0 := by
  obtain ⟨t, ht⟩ := D.nonempty
  apply (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage_frequency
    (D.witness t ht).index (D.witness t ht).subalgebra (fun j => (d j).val) a hd hr
    ((D.witness t ht).bracket n (fun j => (d j).val) a hd hr) v
  intro j
  rw [D.horizontalImage_eq t ht (d j)]
  exact hv j

theorem sunflower_bracket (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (D.horizontal (d j)))
    (hvk : v k ∈ fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a)
    (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf
      (fun j => (d j).val) a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => D.horizontal (d j))
    (D.horizontal_frequency n d a hd hr) v hv j k hjk hj hk hvj hvk

theorem sunflower_representatives (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.layer (d j).val 1)
    (hv : ∀ j, W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourDependentProjection (D.horizontal (d j)))
    (hvk : W.rank.filtration.higherHorizontalMk (d k).val (v k) ∈
      fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (lieTreeEval (fun j => (v j).val) a) = 0 := by
  have h := D.sunflower_bracket n d a hd hr
    (fun j => W.rank.filtration.higherHorizontalMk (d j).val (v j)) hv j k hjk hj hk hvj hvk
  rwa [W.rank.filtration.horizontalTreeValue_mk (fun j => (d j).val) a hd hr v] at h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)}, 0 ≤ p → b ≤ p →
      (R : NativeRankRelation W out H p p) →
      Real.exp ((p + C) ^ C) ≤ N → Nonempty (R.CommonData ((p + C) ^ C)) := by
  classical
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_interval_data s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_rank_relation_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H hp hbp R hN
  let A := (p + c) ^ c
  have hsum : p + A ≤ (p + C) ^ C := hbudget p hp
  have hAQ : A ≤ (p + C) ^ C := by linarith
  obtain ⟨t₀, ht₀⟩ := R.quadruples_nonempty
  let : Nonempty R.quadruples := ⟨⟨t₀, ht₀⟩⟩
  have hlong (t : R.quadruples) (_ht : t ∈ (Finset.univ : Finset R.quadruples)) :
      Real.exp ((p + c) ^ c) ≤ ((R.interval t).length : ℝ) :=
    (R.interval t).length_exp_lower_bound ((Real.exp_le_exp.mpr hsum).trans hN)
  obtain ⟨K, T, _, hT, hsize, _, hdata⟩ :=
    hcommon hp hbp R.interval Finset.univ Finset.univ_nonempty hlong
  let e : R.quadruples ↪ (ZMod N × ZMod N × ZMod N) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Q := T.map e
  have hQR : Q ⊆ R.quadruples := by
    intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    exact u.property
  have hQ : Q.Nonempty := by
    obtain ⟨u, hu⟩ := hT
    exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
  have hsize' : Real.exp (-A) * (R.quadruples.card : ℝ) ≤ (T.card : ℝ) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hsize
  have hdensity : Real.exp (-(p + A)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Q.card := by
    calc
      _ = Real.exp (-A) * (Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [show -(p + A) = -A + -p by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-A) * R.quadruples.card :=
        mul_le_mul_of_nonneg_left R.density (Real.exp_pos _).le
      _ ≤ T.card := hsize'
      _ = Q.card := by simp only [Q, Finset.card_map]
  have hwitness (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ Q) :
      ∃ E : (R.interval ⟨t, hQR ht⟩).SunflowerWitness ((p + C) ^ C),
        ∀ d : Fin (s + 1), E.projection d.val = K d := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨E, hproj, _⟩ := hdata u hu
    exact ⟨E.mono hAQ, hproj⟩
  refine ⟨{
    quadruples := Q
    subset := hQR
    nonempty := hQ
    density := ?_
    spaces := K
    witness := fun t ht => Classical.choose (hwitness t ht)
    projection := fun t ht => Classical.choose_spec (hwitness t ht) }⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
    (by positivity)).trans hdensity

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        p ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ R : NativeRankRelation W.family out H q q,
          Nonempty (R.CommonData ((p + C) ^ C)) := by
  obtain ⟨a, _, hrelation⟩ := exists_native_rank_relation s
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_relation s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_common_rank_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hbase : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  obtain ⟨hqC, hcommonC⟩ := hbudget p hp
  obtain ⟨out, H, hHW, hH, hshort, hHsize, ⟨R⟩⟩ := hrelation W hf
  let R' : NativeRankRelation W.family out H q q := R.mono hbase hbase
  obtain ⟨D⟩ := hcommon hq hpq R' ((Real.exp_le_exp.mpr hcommonC).trans hN)
  refine ⟨out, H, q, hHW, hH, hshort, ?_, hpq, hqC, R', ⟨D.mono hcommonC⟩⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (hbase.trans hqC))) (Nat.cast_nonneg _)).trans hHsize

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coefficient_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (Q α).val j) ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
            (V.projectedOrbitCoefficient α - E α - Q α) ∈
          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩).baseChange ℝ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := V.exists_bounded_coefficient_corrections hs hP
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  exact (congrArg (fun U => _ ∈ U.baseChange ℝ)
    (D.horizontalImage_eq t ht ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).mp
    (hres α)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonUniformCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval.SunflowerWitness

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem mono_projectedDenominator (D : I.SunflowerWitness P) (hPQ : P ≤ Q) :
    (D.mono hPQ).projectedDenominator = D.projectedDenominator := rfl

end NativeRankInterval.SunflowerWitness

namespace NativeRankRelation.CommonData

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_common_projected_denominator (D : R.CommonData P) (hP : 0 ≤ P) :
    ∃ (E : R.CommonData ((P + 2) ^ 3 + 2 * P)) (l : ℕ),
      E.quadruples ⊆ D.quadruples ∧ E.spaces = D.spaces ∧ 0 < l ∧
      (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ t (ht : t ∈ E.quadruples), (E.witness t ht).projectedDenominator = l := by
  classical
  let B := (P + 2) ^ 3 + P
  let code (t : ZMod N × ZMod N × ZMod N) :=
    if ht : t ∈ D.quadruples then (D.witness t ht).projectedDenominator else 1
  let A := (Finset.Icc 1 ⌊Real.exp B⌋₊ : Finset ℕ)
  have hcode (t) (ht : t ∈ D.quadruples) : code t ∈ (A : Set ℕ) := by
    simp only [code, dif_pos ht, Finset.mem_coe, A, Finset.mem_Icc]
    exact ⟨(D.witness t ht).projectedDenominator_pos,
      Nat.le_floor ((D.witness t ht).projectedDenominator_bound hP)⟩
  have hcount : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp B := by
    simpa only [Set.ncard_coe_finset, A, Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.floor_le (Real.exp_pos B).le
  obtain ⟨l, hl, T, hTD, hT, hconst, hsize⟩ := exists_exponential_constant_fiber
    D.quadruples D.nonempty code A A.finite_toSet hcode hcount
  have hPP : P ≤ (P + 2) ^ 3 + 2 * P := by
    have hcube : 0 ≤ (P + 2) ^ 3 := by positivity
    linarith
  let E : R.CommonData ((P + 2) ^ 3 + 2 * P) := {
    quadruples := T
    subset := hTD.trans D.subset
    nonempty := hT
    density := by
      calc
        Real.exp (-((P + 2) ^ 3 + 2 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
            Real.exp (-B) * (Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          dsimp only [B]
          ring
        _ ≤ Real.exp (-B) * D.quadruples.card :=
          mul_le_mul_of_nonneg_left D.density (Real.exp_pos _).le
        _ ≤ T.card := hsize
    spaces := D.spaces
    witness := fun t ht => (D.witness t (hTD ht)).mono hPP
    projection := fun t ht d => D.projection t (hTD ht) d }
  have hl' : 1 ≤ l ∧ l ≤ ⌊Real.exp B⌋₊ := Finset.mem_Icc.mp hl
  refine ⟨E, l, hTD, rfl, hl'.1,
    (Nat.cast_le.mpr hl'.2).trans (Nat.floor_le (Real.exp_pos B).le), ?_⟩
  intro t ht
  change ((D.witness t (hTD ht)).mono hPP).projectedDenominator = l
  rw [NativeRankInterval.SunflowerWitness.mono_projectedDenominator]
  simpa only [code, dif_pos (hTD ht)] using hconst t ht

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankNativeCoordinates
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem projectedOrbitCoefficient_native_coordinates (D : I.SunflowerWitness P)
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (k : Fin 4) (i : ι) :
    W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (D.projectedOrbitCoefficient α).val ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
          (W.horizontalCoefficient hs c τ hG α
            (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))) i := by
  have hmap := congrFun (W.rank.filtration.realFourHorizontalCoordinates_map
    (Finsupp.weight (fun _ : Unit => 1) α) f (D.projectedOrbitCoefficient α)).symm ⟨k, i⟩
  have hcomponent := W.rank.filtration.realFourHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f
    (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
      (D.projectedOrbitCoefficient α)) k i
  exact hmap.trans (hcomponent.trans (congrArg
    (fun x => (f.baseChange ℝ).repr
      ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ x) i)
    (D.projectedOrbitCoefficient_native_component hs c τ hG α k)))

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem spaces_le_fourHorizontalLayer (d : Fin (s + 1)) :
    D.spaces d ≤ W.rank.filtration.fourHorizontalLayer d.val := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  change I.refilteredProjectionImage V.index V.subalgebra d.val ≤ _
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (W.rank.filtration.mem_fourHorizontalLayer d.val _).mpr
    (I.rankProjection_mem_refiltered V.index V.subalgebra d.val y hy)

noncomputable def coordinateSpace (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    Submodule ℚ (Fin 4 → κ → ℚ) :=
  (D.horizontal d).map (W.rank.filtration.fourHorizontalCoordinates d.val f)

theorem coordinateSpace_eq_map (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    D.coordinateSpace d f = (D.spaces d).map (W.rank.filtration.fourAmbientCoordinates d.val f) :=
  W.rank.filtration.horizontalImage_coordinates d.val f (D.spaces d) (D.spaces_le_fourHorizontalLayer d)

theorem exists_coordinate_generators (hP : 0 ≤ P) (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) {K : ℕ}
    (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) K) :
    ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → κ → ℚ),
      Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
      ∀ a k i, RationalHeightLE (v a k i)
        ((W.dim + 1) * (⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ * K) ^ W.dim) := by
  obtain ⟨v, hspan, hv⟩ := (mem_heightBoundedSubspaces W.fourRankBasis _ _ _).mp
    (D.spaces_mem_candidates hP d)
  let φ := W.rank.filtration.fourAmbientCoordinates d.val f
  refine ⟨fun a => φ (v a), ?_, ?_⟩
  · rw [D.coordinateSpace_eq_map, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a k i
    have hv' (j : Fin 4) (l : Fin W.dim) :
        RationalHeightLE (W.model.basis.repr (v a j) l)
          ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
      simpa only [NativeDegreeRankFamily.fourRankBasis, Pi.basis_repr] using hv a ⟨j, l⟩
    simpa only [Fintype.card_fin] using W.rank.filtration.fourAmbientCoordinates_height
      d.val f W.model.basis hf (v a) hv' k i

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coordinate_generators (D : R.CommonData P) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ m : ℕ, m ≤ W.dim ∧ ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer d.val 2),
      (∀ i j, rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) ≤
        (P + 3) ^ 7) ∧
      ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → Fin m → ℚ),
        Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
        ∀ a k i, rationalLogHeight (v a k i) ≤ horizontalCoordinateBudget P := by
  obtain ⟨K, hK, hKp, m, hm, f, hf⟩ :=
    W.rank.exists_horizontal_ambient_basis d hd hP (W.complexity.mono W.rank hbP)
  obtain ⟨v, hv, hheight⟩ := D.exists_coordinate_generators hP d f hf
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hbound := horizontalCoordinateHeight_bound hP W.dim
    ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ K hdim
    (ceil_exp_le_exp_add_one (refiltrationCoordinateBudget_nonneg hP)) hKp
  refine ⟨m, hm, f, (fun i j => rationalLogHeight_le_of_height (hf i j) hKp), v, hv, ?_⟩
  intro a k i
  exact rationalLogHeight_le_of_height (hheight a k i) hbound

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

noncomputable def realCoordinateSpace : Submodule ℝ ((Σ _ : Fin 4, κ) → ℝ) :=
  ((D.coordinateSpace d f).baseChange ℝ).map
    (DegreeRankLieFiltration.realFourCoordinateEquiv (ι := κ)).toLinearMap

theorem realCoordinateSpace_eq_image :
    D.realCoordinateSpace d f =
      ((D.horizontal d).baseChange ℝ).map (W.rank.filtration.realFourHorizontalCoordinates d.val f) :=
  (W.rank.filtration.realFourHorizontalCoordinates_image d.val f (D.horizontal d)).symm

theorem realCoordinateSpace_mem
    (x : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ)
    (hx : W.rank.filtration.realFourHorizontalMap d.val x ∈ (D.horizontal d).baseChange ℝ) :
    W.rank.filtration.realFourAmbientCoordinates d.val f x.val ∈ D.realCoordinateSpace d f := by
  rw [D.realCoordinateSpace_eq_image, ← W.rank.filtration.realFourHorizontalCoordinates_map d.val f x]
  exact ⟨_, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_coordinate_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : (Σ _ : Fin 4, κ) → ℝ,
      (∀ j, |E j| ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α)) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * V.projectedDenominator) ∧
      W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
          (V.projectedOrbitCoefficient α).val - E - Q ∈
        D.realCoordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  let φ := W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
  refine ⟨φ (E α).val, φ (Q α).val, ?_, ?_, ?_⟩
  · intro j
    have hscale := monomialScale_pos (fun _ : Unit => (I.length : ℝ))
      (fun _ => by exact_mod_cast I.length_pos) α
    have hbound := W.rank.filtration.realFourAmbientCoordinates_bound
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis hf (E α).val
      (div_nonneg (Real.exp_pos _).le hscale.le) (hE α) j.1 j.2
    simpa only [Fintype.card_fin] using hbound
  · exact W.rank.filtration.realFourAmbientCoordinates_grid
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis V.projectedDenominator (Q α).val (hQ α)
  · have h := D.realCoordinateSpace_mem
      ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
      (V.projectedOrbitCoefficient α - E α - Q α) (hres α hα)
    change φ ((V.projectedOrbitCoefficient α).val - (E α).val - (Q α).val) ∈ _ at h
    simpa only [map_sub] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

structure SparseAnchors (D : R.CommonData P) where
  anchors12 : ZMod N × ZMod N
  anchors13 : ZMod N × ZMod N
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-(2 * P)) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  relations : ∀ h ∈ shifts,
    (anchors12.2 - h, anchors12.2, anchors12.1) ∈ D.quadruples ∧
      (anchors13.1 - anchors13.2, h + (anchors13.1 - anchors13.2), anchors13.1) ∈ D.quadruples

theorem exists_sparse_anchors (D : R.CommonData P) : Nonempty D.SparseAnchors := by
  obtain ⟨a, b, c, d, S, hS, hsize, hmem⟩ :=
    exists_simultaneous_four_point_anchors D.quadruples (Real.exp_pos _) D.density
  refine ⟨{
    anchors12 := (a, b)
    anchors13 := (c, d)
    shifts := S
    nonempty := hS
    density := ?_
    relations := hmem }⟩
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_neg] using hsize

namespace SparseAnchors

variable {D : R.CommonData P} (A : D.SparseAnchors)

theorem shifts_subset : A.shifts ⊆ H := by
  intro h hh
  have hmem := (A.relations h hh).1
  have hsecond := (R.interval ⟨_, D.subset hmem⟩).second_mem
  simpa using hsecond

end SparseAnchors

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_representative_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ,
      (∀ α, Finsupp.weight (fun _ : Unit => 1) α ≤ s →
        ‖(W.model.basis.baseChange ℝ).equivFun (E α).val‖ ≤
          Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      (∀ α, (W.model.basis.baseChange ℝ).equivFun (Q α).val ∈ realDenominatorGrid n) ∧
      ∀ α (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.horizontalCoefficient hs c τ hG α h₀ -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (E α) -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (Q α) ∈
          (fourFirstProjection (D.horizontal
            ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  let t := (A.anchors12.2 - h₀, A.anchors12.2, A.anchors12.1)
  have ht : t ∈ D.quadruples := (A.relations h₀ hh₀).1
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨fun α => W.rank.filtration.realFourLayerComponent _ 0 (E α),
    fun α => W.rank.filtration.realFourLayerComponent _ 0 (Q α), ?_, ?_, ?_⟩
  · intro α hα
    have he := W.rank.filtration.realFourLayerComponent_norm_bound
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (E α)
      (div_nonneg (Real.exp_nonneg _) (monomialScale_pos _
        (fun _ => by exact_mod_cast I.length_pos) α).le) (hE α)
    have hb := I.norm_bound_on_modulus hp α hα (Real.exp_nonneg ((P + 3) ^ 2))
      ((W.model.basis.baseChange ℝ).equivFun
        (W.rank.filtration.realFourLayerComponent _ 0 (E α)).val) he
    rwa [← Real.exp_add] at hb
  · intro α
    have hg := W.rank.filtration.realFourLayerComponent_grid
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (Q α)
      V.projectedDenominator (hQ α)
    simpa only [Basis.equivFun_apply] using
      realDenominatorGrid_subset_of_dvd V.projectedDenominator_pos (hdenom t ht) hg
  · intro α hα
    have hm := real_firstProjection_mem
      (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩) (hres α hα)
    have hfirst : rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) 0) = h₀ := by
      simp [t, rankQuadrupleParameters]
    let φ := ((LinearMap.proj (0 : Fin 4)).baseChange ℝ).comp
      (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α))
    have heq : φ (V.projectedOrbitCoefficient α - E α - Q α) =
        φ (V.projectedOrbitCoefficient α) - φ (E α) - φ (Q α) := by
      exact (map_sub φ (V.projectedOrbitCoefficient α - E α) (Q α)).trans
        (congrArg₂ (· - ·) (map_sub φ (V.projectedOrbitCoefficient α) (E α)) rfl)
    change φ (V.projectedOrbitCoefficient α - E α - Q α) ∈ _ at hm
    rw [heq] at hm
    change (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (V.projectedOrbitCoefficient α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (E α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (Q α)) ∈ _ at hm
    rw [V.projectedOrbitCoefficient_native_component hs c τ hG α 0, hfirst,
      W.rank.filtration.realFourLayerComponent_horizontal,
      W.rank.filtration.realFourLayerComponent_horizontal] at hm
    exact hm

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem native_scaled_correction
    (D : R.CommonData P) (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f) := by
  intro β
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_coordinate_corrections hs hP t ht α hα f hf
  let I := R.interval ⟨t, D.subset ht⟩
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖E‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    intro j
    simpa only [Real.norm_eq_abs, M, mul_div_assoc] using hE j
  refine ⟨E, Q, ?_, ?_, ?_⟩
  · have h := I.norm_bound_on_modulus hp α hα hM E hnorm
    simpa only [M, Real.exp_add, mul_div_assoc, mul_assoc] using h
  · change Q ∈ realDenominatorGrid
      (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * (D.witness t ht).projectedDenominator) at hQ
    simpa only [hdenom t ht] using hQ
  · have hcoeff : W.rank.filtration.realFourAmbientCoordinates
        (Finsupp.weight (fun _ : Unit => 1) α) f ((D.witness t ht).projectedOrbitCoefficient α).val =
        rankCoordinateTuple β t := by
      funext j
      exact (D.witness t ht).projectedOrbitCoefficient_native_coordinates hs c τ hG α f j.1 j.2
    rw [hcoeff] at hres
    exact hres

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_sparse_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36))) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
        ‖e₁₂‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        ‖e₁₃‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
        β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
        β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  intro β J
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)
  have hcorrect (t) (ht : t ∈ D.quadruples) : ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ M / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan J := by
    obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_scaled_correction hs hp hP c τ hG l hdenom α hα f hf t ht
    exact ⟨E, Q, by simpa only [M, mul_div_assoc] using hE, hQ, hres⟩
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_rank_sparse_family A.shifts h₀ hh₀ J v hv hJH
    (Nat.mul_pos (matrixDenominator_pos _) hl) hvH hz hfour hcols hJHz hlz
    (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, hlm, ?_⟩
  exact hsolve α hα₀ β A.anchors12.1 A.anchors12.2 A.anchors13.1 A.anchors13.2 M hslow
    (fun h hh => hcorrect _ (A.relations h hh).1)
    (fun h hh => hcorrect _ (A.relations h hh).2)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N)
    (hNdep : Real.exp (separationBudget
      (rankDependentInputBudget z + sparseGeneratorBudget (rankDependentInputBudget z))) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    let Z := rankDependentInputBudget z
    let Q := Z + sparseGeneratorBudget Z
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (Q + ((Q + 2) ^ 3 + (Q + 2) ^ 36)) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e q : ι → ℝ,
        ‖e‖ ≤ (Real.exp Q + Real.exp ((Q + 2) ^ 3 + (Q + 2) ^ 18 + Q)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧ q ∈ realDenominatorGrid m ∧
        β h - β h₀ - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro β J Z Q
  obtain ⟨m₀, hm₀, hmp₀, hdiv₀, hpairs⟩ := A.exists_native_sparse_approximations h₀ hh₀
    hs hp hP c τ hG l hl hdenom α hα hα₀ f hf v hv hJH hvH hz hfour hcols hJHz hlz hslow hN
  obtain ⟨hZ, hzZ, h2zZ, hdenZ, hslowZ⟩ := rankDependentInputBudget_bounds hz
  have hZQ : Z ≤ Q := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hZ)
  have hdim : (Fintype.card ι : ℝ) ≤ z := by
    have hcard : Fintype.card ι ≤ Fintype.card (Σ _ : Fin 4, ι) :=
      Fintype.card_le_of_injective (fun i : ι => (⟨0, i⟩ : Σ _ : Fin 4, ι))
        (fun _ _ h => congrArg (fun j : Σ _ : Fin 4, ι => j.2) h)
    exact (Nat.cast_le.mpr hcard).trans hfour
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ Z :=
    ((Nat.cast_le.mpr (card_selected_four_le K)).trans hfour).trans hzZ
  have hdoublecols : (Fintype.card (ν ⊕ ν) : ℝ) ≤ Z := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨m, hm, hmp, hdiv, hsolve⟩ := exists_dependent_coordinate_corrections J v hv hJH hm₀ hvH
    hZ (hdim.trans hzZ) (hselected _) (hselected _) hdoublecols
    (hJHz.trans (Real.exp_le_exp.mpr hzZ)) (hmp₀.trans (Real.exp_le_exp.mpr hdenZ))
    (fun _ : Unit => (N : ℝ)) (fun _ => hNdep)
  refine ⟨m, hm, hmp, hdiv₀.trans hdiv, ?_⟩
  intro h hh
  obtain ⟨e₁, q₁, e₂, q₂, he₁, he₂, hq₁, hq₂, hres₁, hres₂⟩ := hpairs h hh
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
  have hcost : 2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) ≤ Real.exp Q :=
    hslowZ.trans (Real.exp_le_exp.mpr hZQ)
  have hsingle : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Q := by
    linarith [Real.exp_pos z, Real.exp_pos ((z + 2) ^ 3 + (z + 2) ^ 18 + z)]
  have hfirst : ‖e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α :=
    he₁.trans (div_le_div_of_nonneg_right hsingle hscale.le)
  have hdiff : ‖e₂ - e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    calc
      ‖e₂ - e₁‖ ≤ ‖e₂‖ + ‖e₁‖ := norm_sub_le _ _
      _ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α +
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α := add_le_add he₂ he₁
      _ = (2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) /
          monomialScale (fun _ : Unit => (N : ℝ)) α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcost hscale.le
  exact hsolve α hα₀ (β h - β h₀) e₁ e₂ q₁ q₂ hres₁ hres₂ hfirst hdiff hq₁ hq₂

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_bounded_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    ∃ m : ℕ, m ≤ W.dim ∧
      ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2),
        (∀ i j, rationalLogHeight
          (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) ≤
          (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ h ∈ A.shifts, ∃ e q : Fin m → ℝ,
            ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
            q ∈ realDenominatorGrid n ∧
            W.nativeCoefficientCoordinates hs c τ hG α f h -
                W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - q ∈
              realRationalCoordinateSpan (fourDependentProjection
                (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)) := by
  have heval : α () ≠ 0 := by
    intro hzero
    apply hα₀
    apply Finsupp.ext
    intro u
    cases u
    exact hzero
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  have hd : 1 ≤ d.val := Finsupp.le_weight_of_ne_zero' (fun _ : Unit => 1) heval
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let K := ⌈Real.exp ((P + 3) ^ 7)⌉₊
  let JH := ⌈Real.exp (horizontalCoordinateBudget P)⌉₊
  let z := nativeCoordinateInputBudget s P
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1) := ceil_exp_le_exp_add_one (by positivity)
  obtain ⟨_, h4PU, _, _, hGU, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hUz := (nativeCoordinateInputBudget_bounds s hP).1
  have hcount (a : ℕ) (ha : a ≤ W.dim) : (Fintype.card (Σ _ : Fin 4, Fin a) : ℝ) ≤ z := by
    have haP : (a : ℝ) ≤ P := (Nat.cast_le.mpr ha).trans hdim
    have h4 : 4 * (a : ℝ) ≤ z :=
      (mul_le_mul_of_nonneg_left haP (by norm_num : (0 : ℝ) ≤ 4)).trans (h4PU.trans hUz)
    simpa [Fintype.card_sigma] using h4
  have hJHz : (JH : ℝ) ≤ Real.exp z :=
    (ceil_exp_le_exp_add_one (horizontalCoordinateBudget_nonneg hP)).trans
      (Real.exp_le_exp.mpr (hGU.trans hUz))
  have hden : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤
      Real.exp z := nativeCoordinate_denominator_bound s hP _ l hlP
        (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hm).trans hdim)
        (by simpa only [Fintype.card_fin] using hdim) hf
  obtain ⟨hN₁, hN₂⟩ := nativeCoordinateSeparationBudget_cutoffs s hP hN
  obtain ⟨n, hn, hnp, hln, hsolve⟩ := A.exists_native_dependent_approximations h₀ hh₀ hs hp hP
    c τ hG l hl hdenom α hα hα₀ f (fun i j => rationalHeightLE_ceil_exp (hf i j))
    v hv (one_le_ceil_exp _) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    (nativeCoordinateInputBudget_nonneg s hP) (hcount m hm)
    (by simpa only [Fintype.card_fin] using hcount W.dim le_rfl) hJHz hden
    (nativeCoordinate_slow_bound s hP hpP W.dim K hdim hK) hN₁ hN₂
  refine ⟨m, hm, f, hf, n, hn, ?_, (dvd_mul_left l _).trans hln, ?_⟩
  · simpa only [nativeDependentDenominatorBudget, nativeDependentBudget, add_assoc] using hnp
  · intro h hh
    obtain ⟨e, q, he, hq, hres⟩ := hsolve h hh
    refine ⟨e, q, ?_, hq, hres⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
    exact he.trans (div_le_div_of_nonneg_right (nativeDependentSlowBudget_bound s hP) hscale.le)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRealDependentProjection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

theorem coordinateSpace_first :
    fourFirstProjection (D.coordinateSpace d f) =
      (fourFirstProjection (D.horizontal d)).map (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourFirstProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f) (D.horizontal d)

theorem coordinateSpace_dependent :
    fourDependentProjection (D.coordinateSpace d f) =
      (fourDependentProjection (D.horizontal d)).map
        (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourDependentProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f)
    (W.rank.filtration.higherHorizontalCoordinates_injective d.val f) (D.horizontal d)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem real_dependent_coordinateSpace_eq (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f)) =
      ((fourDependentProjection (D.horizontal d)).baseChange ℝ).map
        (W.rank.filtration.realHigherHorizontalCoordinates d.val f) := by
  rw [D.coordinateSpace_dependent]
  exact (W.rank.filtration.realHigherHorizontalCoordinates_image d.val f
    (fourDependentProjection (D.horizontal d))).symm

theorem exists_real_dependent_remainder (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))
    (x y : ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal d.val) (e u : ι → ℝ)
    (hmem : W.rank.filtration.realHigherHorizontalCoordinates d.val f x -
        W.rank.filtration.realHigherHorizontalCoordinates d.val f y - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f))) :
    ∃ z ∈ (fourDependentProjection (D.horizontal d)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = e + u := by
  rw [D.real_dependent_coordinateSpace_eq d f] at hmem
  obtain ⟨z, hz, hcoord⟩ := hmem
  refine ⟨z, hz, ?_⟩
  rw [map_sub, map_sub, hcoord]
  abel

theorem exists_native_dependent_remainder (D : R.CommonData P) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h h₀ : ZMod N) (e u : ι → ℝ)
    (hmem : W.nativeCoefficientCoordinates hs c τ hG α f h -
        W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f))) :
    ∃ z ∈ (fourDependentProjection
        (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h - W.horizontalCoefficient hs c τ hG α h₀ - z) = e + u := by
  apply D.exists_real_dependent_remainder
    ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    (W.horizontalCoefficient hs c τ hG α h) (W.horizontalCoefficient hs c τ hG α h₀) e u
  simpa only [W.nativeCoefficientCoordinates_eq_real hs c τ hG α f] using hmem

end NativeRankRelation.CommonData

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def commonCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourFirstProjection (D.horizontal d))

noncomputable def dependentCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourDependentProjection (D.horizontal d))

theorem commonCoefficientSpace_le (d : Fin (s + 1)) :
    D.commonCoefficientSpace d ≤ W.rank.filtration.layer d.val 1 :=
  W.rank.filtration.horizontalPreimage_le d.val _

theorem dependentCoefficientSpace_le_common (d : Fin (s + 1)) :
    D.dependentCoefficientSpace d ≤ D.commonCoefficientSpace d :=
  W.rank.filtration.horizontalPreimage_mono d.val (fourDependentProjection_le _)

theorem native_coefficient_mem_common {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.commonCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourFirstProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold commonCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourFirstProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

theorem native_coefficient_mem_dependent {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.dependentCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourDependentProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold dependentCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourDependentProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

theorem coefficient_sunflower (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : Fin n → W.L) (hv : ∀ j, v j ∈ D.commonCoefficientSpace (d j))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentCoefficientSpace (d j))
    (hvk : v k ∈ D.dependentCoefficientSpace (d k)) :
    W.vertical.frequency (lieTreeEval v a) = 0 := by
  let u (i : Fin n) : W.rank.filtration.layer (d i).val 1 :=
    ⟨v i, D.commonCoefficientSpace_le (d i) (hv i)⟩
  exact D.sunflower_representatives n d a hd hr u
    (fun i => (W.rank.filtration.mem_horizontalPreimage _ _ (u i)).mp (hv i))
    j k hjk hj hk
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u j)).mp hvj)
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u k)).mp hvk)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

structure CoefficientBases (Q : ℝ) where
  common : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)
  dependent : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)
  common_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (common d i : W.L) j) ≤ Q
  dependent_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (dependent d i : W.L) j) ≤ Q

def CoefficientBases.mono {Q Q' : ℝ} (B : D.CoefficientBases Q) (h : Q ≤ Q') :
    D.CoefficientBases Q' where
  common := B.common
  dependent := B.dependent
  common_height d i j := (B.common_height d i j).trans h
  dependent_height d i j := (B.dependent_height d i j).trans h

def CoefficientAlphabet : Type :=
  (Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
    (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))

noncomputable instance coefficientAlphabetFintype : Fintype D.CoefficientAlphabet := by
  unfold CoefficientAlphabet
  infer_instance

def coefficientDegree : D.CoefficientAlphabet → Fin (s + 1) :=
  Sum.elim (fun x => ⟨x.1.val + 1, by omega⟩) (fun x => ⟨x.1.val + 1, by omega⟩)

def coefficientWeight (x : D.CoefficientAlphabet) : ℕ := (D.coefficientDegree x).val

theorem coefficientWeight_pos (x : D.CoefficientAlphabet) : 0 < D.coefficientWeight x := by
  cases x with
  | inl x => exact Nat.zero_lt_succ _
  | inr x => exact Nat.zero_lt_succ _

theorem coefficientAlphabet_card : Fintype.card D.CoefficientAlphabet ≤ 2 * s * W.dim := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hdim (U : Submodule ℚ W.L) : finrank ℚ U ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using U.finrank_le
  change Fintype.card
    ((Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
      (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  calc
    _ ≤ (∑ _ : Fin s, W.dim) + ∑ _ : Fin s, W.dim :=
      Nat.add_le_add (Finset.sum_le_sum (fun _ _ => hdim _))
        (Finset.sum_le_sum (fun _ _ => hdim _))
    _ = 2 * s * W.dim := by simp; ring

noncomputable def CoefficientBases.generator {Q : ℝ} (B : D.CoefficientBases Q) :
    D.CoefficientAlphabet → W.L :=
  Sum.elim (fun x => (B.common x.1 x.2 : W.L)) (fun x => (B.dependent x.1 x.2 : W.L))

theorem CoefficientBases.generator_mem_common {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ D.commonCoefficientSpace (D.coefficientDegree x) := by
  cases x with
  | inl x => exact (B.common x.1 x.2).property
  | inr x => exact D.dependentCoefficientSpace_le_common _ (B.dependent x.1 x.2).property

theorem CoefficientBases.generator_mem_layer {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ W.rank.filtration.layer (D.coefficientWeight x) 0 := by
  rw [W.rank.filtration.rank_zero_eq_one]
  exact D.commonCoefficientSpace_le _ (B.generator_mem_common D x)

theorem CoefficientBases.generator_height {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) (i : Fin W.dim) :
    rationalLogHeight (W.model.basis.repr (B.generator D x) i) ≤ Q := by
  cases x with
  | inl x => exact B.common_height x.1 x.2 i
  | inr x => exact B.dependent_height x.1 x.2 i

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

namespace NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficient_space_bases (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ c : Basis (Fin (finrank ℚ (D.commonCoefficientSpace d))) ℚ (D.commonCoefficientSpace d),
      (∀ i j, rationalLogHeight (W.model.basis.repr (c i : W.L) j) ≤ coefficientSpaceBasisBudget P) ∧
      ∃ e : Basis (Fin (finrank ℚ (D.dependentCoefficientSpace d))) ℚ (D.dependentCoefficientSpace d),
        ∀ i j, rationalLogHeight (W.model.basis.repr (e i : W.L) j) ≤ coefficientSpaceBasisBudget P := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hR := W.complexity.mono W.rank hbP
  have hdim : (W.dim : ℝ) ≤ P := hR.1.1
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let J := D.coordinateSpace d f
  let a := coefficientSpaceInputBudget P
  have hhor := horizontalCoordinateBudget_nonneg hP
  have hpow : 0 ≤ (P + 3) ^ 7 := by positivity
  have hPa : P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have h4Pa : 4 * P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hhora : horizontalCoordinateBudget P ≤ a := by
    dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hpowa : (P + 3) ^ 7 ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have ha : 0 ≤ a := hP.trans hPa
  have hma : (m : ℝ) ≤ a := (Nat.cast_le.mpr hm).trans (hdim.trans hPa)
  have hcols : Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) = 4 * W.dim := by simp
  have hcolsa : (Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) : ℝ) ≤ a := by
    rw [hcols, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)).trans h4Pa
  obtain ⟨eD, heD⟩ := exists_dependent_coordinate_basis J v hv ha
    (by simpa only [Fintype.card_fin] using hma) hcolsa
    (fun i k j => (hvH i k j).trans hhora)
  have hdepdim : finrank ℚ (fourDependentProjection J) ≤ m := by
    simpa using (fourDependentProjection J).finrank_le
  let a₁ := W.rank.basis d ⟨1, by omega⟩
  let u : Fin (finrank ℚ (W.rank.filtration.layer d.val 1)) → W.L := fun i => a₁ i
  have hu : Submodule.span ℚ (Set.range u) = W.rank.filtration.layer d.val 1 :=
    span_submodule_basis _ a₁
  have hudim : finrank ℚ (W.rank.filtration.layer d.val 1) ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using
      (W.rank.filtration.layer d.val 1).finrank_le
  have huH (i) (j) : rationalLogHeight (W.model.basis.repr (u i) j) ≤ P :=
    hR.2 d ⟨1, by omega⟩ i j
  let T := W.rank.filtration.ambientHorizontalCoordinates d.val f
  have hTu (i) (j) : rationalLogHeight ((Pi.basisFun ℚ (Fin m)).repr (T (u i)) j) ≤
      (a + 2) ^ 4 := by
    change rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (u i)) j) ≤ _
    exact linearMap_coordinate_logHeight W.model.basis f
      (W.rank.filtration.layer d.val 2).mkQ ha
      (by simpa only [Fintype.card_fin] using hdim.trans hPa)
      (fun k l => (hf l k).trans hpowa) (u i) (fun k => (huH i k).trans hPa) j
  let Q := a + (a + 2) ^ 4 + dependentCoordinateBudget a
  have hdep := dependentCoordinateBudget_nonneg ha
  have hpower : 0 ≤ (a + 2) ^ 4 := by positivity
  have haQ : a ≤ Q := by dsimp only [Q]; linarith
  have hpQ : (a + 2) ^ 4 ≤ Q := by dsimp only [Q]; linarith
  have hdQ : dependentCoordinateBudget a ≤ Q := by dsimp only [Q]; linarith
  have hQ : 0 ≤ Q := ha.trans haQ
  have huQ : (Fintype.card (Fin (finrank ℚ (W.rank.filtration.layer d.val 1))) : ℝ) ≤ Q := by
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hudim).trans (hdim.trans (hPa.trans haQ))
  have hv₀ : Submodule.span ℚ (Set.range (fun i => v i 0)) = fourFirstProjection J := by
    change _ = (D.coordinateSpace d f).map (LinearMap.proj 0)
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hdepSpan : Submodule.span ℚ (Set.range (fun i => (eD i : Fin m → ℚ))) =
      fourDependentProjection J := by
    change Submodule.span ℚ (Set.range ((fourDependentProjection J).subtype ∘ eD)) = _
    rw [Set.range_comp, ← Submodule.map_span, eD.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hc := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourFirstProjection J) T u (fun i => v i 0)
    hu hv₀ hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ (hcolsa.trans haQ)
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (hvH i 0 j).trans (hhora.trans haQ))
    (fun i j => (hTu i j).trans hpQ)
  have he := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourDependentProjection J) T u (fun i => (eD i : Fin m → ℚ))
    hu hdepSpan hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdepdim).trans (hma.trans haQ))
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (heD i j).trans hdQ)
    (fun i j => (hTu i j).trans hpQ)
  have hcspace : D.commonCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourFirstProjection J).comap T := by
    unfold commonCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_first d f]
  have hespace : D.dependentCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourDependentProjection J).comap T := by
    unfold dependentCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_dependent d f]
  rw [← hcspace] at hc
  rw [← hespace] at he
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e, he⟩ := he
  exact ⟨c, hc, e, he⟩

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFourSpace (d : Fin (s + 1)) : Submodule ℚ (Fin 4 → W.L) :=
  ((D.horizontal d).comap (W.rank.filtration.fourHorizontalMap d.val)).map
    (W.rank.filtration.fourHorizontalLayer d.val).subtype

theorem mem_coefficientFourSpace (d : Fin (s + 1))
    (v : W.rank.filtration.fourHorizontalLayer d.val) :
    v.val ∈ D.coefficientFourSpace d ↔
      W.rank.filtration.fourHorizontalMap d.val v ∈ D.horizontal d := by
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = v := Subtype.ext he
    exact h ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem coefficient_four_frequency (n : ℕ) (d : Fin n → Fin (s + 1))
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun j => (d j).val) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → W.L)
    (hv : ∀ j, v j ∈ D.coefficientFourSpace (d j)) :
    fourFunctionDifference (fun x => W.vertical.frequency (lieTreeEval x a)) v = 0 := by
  classical
  have hlift (j : Fin n) : ∃ w : W.rank.filtration.fourHorizontalLayer (d j).val,
      W.rank.filtration.fourHorizontalMap (d j).val w ∈ D.horizontal (d j) ∧ w.val = v j :=
    hv j
  choose w hw he using hlift
  have hvalue (k : Fin 4) :
      W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
          (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j) k) =
        lieTreeEval (fun j => v j k) a := by
    let u (j : Fin n) : W.rank.filtration.layer (d j).val 1 :=
      ⟨(w j).val k, (W.rank.filtration.mem_fourHorizontalLayer _ _).mp (w j).property k⟩
    change W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
      (fun j => W.rank.filtration.higherHorizontalMk (d j).val (u j)) = _
    rw [W.rank.filtration.horizontalTreeValue_mk _ a hd hr u]
    congr 1
    funext j
    exact congrFun (he j) k
  have h := D.horizontal_frequency n d a hd hr
    (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j)) hw
  simpa only [fourFunctionDifference, hvalue] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos

noncomputable def coefficientFreeFiltration : DegreeRankLieFiltration D.CoefficientFreeLieAlgebra s r :=
  FreeDegreeRankLieAlgebra.filtration D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos W.rank.filtration.rank_le_degree

noncomputable def coefficientFreeGenerator (x : D.CoefficientAlphabet) : D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.of D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos x

theorem coefficientFreeGenerator_mem_layer (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeFiltration.layer (D.coefficientWeight x) 1 :=
  FreeDegreeRankLieAlgebra.of_mem_layer _ _ _ _ _ W.rank.filtration.rank_le_degree x

noncomputable def commonFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩)))

noncomputable def dependentFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩)))

theorem commonFreeSpan_le_layer (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inl ⟨d, i⟩)

theorem dependentFreeSpan_le_layer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inr ⟨d, i⟩)

variable {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.freeEvaluation : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ W.L :=
  FreeDegreeRankLieAlgebra.lift W.rank.filtration D.coefficientWeight D.coefficientWeight_pos
    (B.generator D) (B.generator_mem_layer D)

theorem CoefficientBases.freeEvaluation_generator (x : D.CoefficientAlphabet) :
    B.freeEvaluation D (D.coefficientFreeGenerator x) = B.generator D x :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

noncomputable def CoefficientBases.commonFreeLift (d : Fin s) :
    D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.common d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩))

noncomputable def CoefficientBases.dependentFreeLift (d : Fin s) :
    D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.dependent d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩))

theorem CoefficientBases.commonFreeLift_range (d : Fin s) :
    LinearMap.range (B.commonFreeLift D d) = D.commonFreeSpan d :=
  (B.common d).constr_range ℚ

theorem CoefficientBases.dependentFreeLift_range (d : Fin s) :
    LinearMap.range (B.dependentFreeLift D d) = D.dependentFreeSpan d :=
  (B.dependent d).constr_range ℚ

theorem CoefficientBases.freeEvaluation_commonFreeLift (d : Fin s)
    (x : D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.commonFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.commonFreeLift D d) =
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.common d).ext
    intro i
    change B.freeEvaluation D ((B.common d).constr ℚ _ (B.common d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inl ⟨d, i⟩)
  exact LinearMap.congr_fun h x

theorem CoefficientBases.freeEvaluation_dependentFreeLift (d : Fin s)
    (x : D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.dependentFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.dependentFreeLift D d) =
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.dependent d).ext
    intro i
    change B.freeEvaluation D ((B.dependent d).constr ℚ _ (B.dependent d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inr ⟨d, i⟩)
  exact LinearMap.congr_fun h x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.realCommonFreeLift (d : Fin s) :
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.commonFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

noncomputable def CoefficientBases.realDependentFreeLift (d : Fin s) :
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.dependentFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

theorem CoefficientBases.realCommonFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realCommonFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.commonFreeLift D d).baseChange ℝ x :=
  congrArg ((B.commonFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realDependentFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realDependentFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.dependentFreeLift D d).baseChange ℝ x :=
  congrArg ((B.dependentFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realCommonFreeLift_mem (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realCommonFreeLift D d x ∈ (D.commonFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.commonFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem CoefficientBases.realDependentFreeLift_mem (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realDependentFreeLift D d x ∈ (D.dependentFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.dependentFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem CoefficientBases.realEvaluation_commonFreeLift (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realCommonFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.commonFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.commonFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_commonFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem CoefficientBases.realEvaluation_dependentFreeLift (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realDependentFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.dependentFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.dependentFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_dependentFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_commonFreeSpan (d : Fin s) :
    (D.commonFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.commonFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.commonFreeLift D d z) ∈ _
    rw [B.freeEvaluation_commonFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.commonFreeLift D d ⟨x, hx⟩,
      (B.commonFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_commonFreeLift D d ⟨x, hx⟩

theorem CoefficientBases.freeEvaluation_dependentFreeSpan (d : Fin s) :
    (D.dependentFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.dependentFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.dependentFreeLift D d z) ∈ _
    rw [B.freeEvaluation_dependentFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.dependentFreeLift D d ⟨x, hx⟩,
      (B.dependentFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_dependentFreeLift D d ⟨x, hx⟩

noncomputable def CoefficientBases.freeFrequency : D.CoefficientFreeLieAlgebra →ₗ[ℚ] ℚ :=
  W.vertical.frequency.comp (B.freeEvaluation D).toLinearMap

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}

namespace FreeCoordinateFrame

variable {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
    (FreeDegreeRankLieAlgebra X s r w hw)} {p q : ℝ}

end FreeCoordinateFrame
end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  D.commonFreeSpan d ⊔ D.dependentFreeSpan d

theorem commonFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_left

theorem dependentFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_right

theorem coefficientFreeSpan_le_layer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
  sup_le (D.commonFreeSpan_le_layer d) (D.dependentFreeSpan_le_layer d)

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_coefficientFreeSpan (d : Fin s) :
    (D.coefficientFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  rw [coefficientFreeSpan, Submodule.map_sup, B.freeEvaluation_commonFreeSpan D,
    B.freeEvaluation_dependentFreeSpan D]
  exact sup_eq_left.mpr (D.dependentCoefficientSpace_le_common _)

theorem CoefficientBases.combined_free_sunflower (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentFreeSpan (d j)) (hvk : v k ∈ D.dependentFreeSpan (d k)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  have h := D.coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => B.freeEvaluation D (v i))
    (fun i => (B.freeEvaluation_coefficientFreeSpan D (d i)).le ⟨v i, hv i, rfl⟩)
    j k hjk hj hk
    ((B.freeEvaluation_dependentFreeSpan D (d j)).le ⟨v j, hvj, rfl⟩)
    ((B.freeEvaluation_dependentFreeSpan D (d k)).le ⟨v k, hvk, rfl⟩)
  change W.vertical.frequency (B.freeEvaluation D (lieTreeEval v a)) = 0
  rw [map_lieTreeEval]
  exact h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_dependentFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.dependentFreeSpan d))) ℚ (D.dependentFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q :=
  exists_submodule_basis_of_spanning_logHeight e _
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩)) rfl
    (fun a i => F.generator_height hs (Sum.inr ⟨d, a⟩) i)

theorem exists_coefficientFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.coefficientFreeSpan d))) ℚ (D.coefficientFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
  let v := Sum.elim (fun a => D.coefficientFreeGenerator (Sum.inl ⟨d, a⟩))
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩))
  have hspan : Submodule.span ℚ (Set.range v) = D.coefficientFreeSpan d := by
    dsimp only [v]
    rw [span_range_sumElim]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e _ v hspan
  intro a i
  cases a with
  | inl a => exact F.generator_height hs (Sum.inl ⟨d, a⟩) i
  | inr a => exact F.generator_height hs (Sum.inr ⟨d, a⟩) i

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) (marked : X → Bool)

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open VectorPolynomial

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (hr : r ≤ s) {σ : Type*} (g : X → σ →₀ ℕ)

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

end Erdos3

end

section

namespace Erdos3

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (marked : X → Bool)

end FreeDegreeRankLieAlgebra
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

def coefficientLayerIndex : D.CoefficientAlphabet → Fin s := Sum.elim (fun x => x.1) (fun x => x.1)

def coefficientIsDependent : D.CoefficientAlphabet → Bool := Sum.elim (fun _ => false) (fun _ => true)

theorem coefficientWeight_eq_layerIndex (x : D.CoefficientAlphabet) :
    D.coefficientWeight x = (D.coefficientLayerIndex x).val + 1 := by
  cases x <;> rfl

theorem coefficientFreeGenerator_mem_combined (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => exact D.commonFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)
  | inr x => exact D.dependentFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)

theorem coefficientFreeGenerator_mem_dependent (x : D.CoefficientAlphabet)
    (hx : D.coefficientIsDependent x = true) :
    D.coefficientFreeGenerator x ∈ D.dependentFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => cases hx
  | inr x => exact Submodule.subset_span ⟨x.2, rfl⟩

noncomputable def dependentWordLayer (d k l : ℕ) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayer D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

noncomputable def dependentWordIdeal (d k l : ℕ) : LieIdeal ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayerIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

theorem dependentWordLayer_antitone {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    D.dependentWordLayer e m n ≤ D.dependentWordLayer d k l :=
  markedLieSpan_antitone _ _ _ hde hkm hln

theorem commonFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.commonFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inl ⟨d, i⟩)

theorem dependentFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 1 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inr ⟨d, i⟩)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreePowerBound
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_uniform_native_degree_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
      ∃ f : ∀ d, Basis (Fin (m d)) ℚ
        (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
        (∀ d i j, rationalLogHeight
          ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
            (W.model.basis j)) i) ≤ (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
            ∃ e q : Fin (m d) → ℝ,
              ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) /
                monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧ q ∈ realDenominatorGrid n ∧
              W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                realRationalCoordinateSpan (fourDependentProjection
                  (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  classical
  intro α
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    intro hz
    have h := congrArg (fun x : Unit →₀ ℕ => x ()) hz
    simp [α] at h
  have hchoice (d : Fin s) := A.exists_bounded_native_dependent_approximations h₀ hh₀
    hs hp hP hbP hpP c τ hG l hl hlP hdenom (α d) (hdegree d) (hnonzero d) hN
  choose m hm f hf n hn hnB hln happrox using hchoice
  let n₀ : ℕ := ∏ d : Fin s, n d
  have hn₀ : 0 < n₀ := Finset.prod_pos (fun d _ => hn d)
  have hn₀B : (n₀ : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) := by
    change ((∏ d : Fin s, n d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      ∏ d : Fin s, (n d : ℝ) ≤ ∏ _d : Fin s, Real.exp (nativeDependentDenominatorBudget s P) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun d _ => hnB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hdvd (d : Fin s) : n d ∣ n₀ := Finset.dvd_prod_of_mem n (Finset.mem_univ d)
  let d₀ : Fin s := ⟨0, by omega⟩
  refine ⟨m, hm, f, hf, n₀, hn₀, hn₀B, (hln d₀).trans (hdvd d₀), ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d h hh
  exact ⟨e, q, he, realDenominatorGrid_subset_of_dvd (hn d) (hdvd d) hq, hres⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_degree_approximation_bound (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}
      (A : D.SparseAnchors) (h₀ : ZMod N), h₀ ∈ A.shifts →
      0 ≤ p → 0 ≤ P → b ≤ P → p ≤ P →
      ∀ (c : Basis κ ℚ W.L) (τ : κ → ℕ)
        (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
        (l : ℕ), 0 < l → (l : ℝ) ≤ Real.exp P →
        (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l) →
        Real.exp ((P + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
          ∃ f : ∀ d, Basis (Fin (m d)) ℚ
            (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
            (∀ d i j, rationalLogHeight
              ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                (W.model.basis j)) i) ≤ (P + C) ^ C) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((P + C) ^ C) ∧ l ∣ n ∧
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ e q : Fin (m d) → ℝ,
                  ‖e‖ ≤ Real.exp ((P + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  q ∈ realDenominatorGrid n ∧
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                      W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                    realRationalCoordinateSpan (fourDependentProjection
                      (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_coordinate_polynomial_budget s
  refine ⟨C, hC, ?_⟩
  intro κ r N _ b p q P W out H R D A h₀ hh₀ hp hP hbP hpP c τ hG l hl hlP hdenom hN α
  obtain ⟨hcut, hden, hslow, hf⟩ := hbudget P hP
  obtain ⟨m, hm, f, hfheight, n, hn, hnB, hln, happrox⟩ :=
    A.exists_uniform_native_degree_approximations h₀ hh₀ hs hp hP hbP hpP c τ hG l hl hlP hdenom
      ((Real.exp_le_exp.mpr hcut).trans hN)
  have hden0 : 0 ≤ nativeDependentDenominatorBudget s P := by
    have hQ := nativeDependentBudget_nonneg s hP
    unfold nativeDependentDenominatorBudget
    positivity
  have hden' : (s : ℝ) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C :=
    (mul_le_mul_of_nonneg_right (by linarith : (s : ℝ) ≤ (s : ℝ) + 1) hden0).trans hden
  refine ⟨m, hm, f, (fun d i j => (hfheight d i j).trans hf), n, hn,
    hnB.trans (Real.exp_le_exp.mpr hden'), hln, ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d hd h hh
  refine ⟨e, q, ?_, hq, hres⟩
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
  exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDependentRepresentativeFamily
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_coordinate_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.family.dim) ∧
              ∃ f : ∀ d, Basis (Fin (m d)) ℚ
                (W.family.L ⧸ W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
                (∀ d i j, rationalLogHeight
                  ((f d).repr ((W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                    (W.family.model.basis j)) i) ≤ (p + C) ^ C) ∧
                ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                  (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                    ∃ e u : Fin (m d) → ℝ,
                      ‖e‖ ≤ Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                      u ∈ realDenominatorGrid n ∧
                      W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                          W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - u ∈
                        realRationalCoordinateSpan (fourDependentProjection
                          (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) ∧
                      ∃ z ∈ (fourDependentProjection
                          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ,
                        W.family.rank.filtration.realHigherHorizontalCoordinates
                            (Finsupp.weight (fun _ : Unit => 1) (α d)) (f d)
                            (W.family.horizontalCoefficient hs c τ hG (α d) h -
                              W.family.horizontalCoefficient hs c τ hG (α d) h₀ - z) = e + u := by
  obtain ⟨a, _, hcommon⟩ := exists_native_common_rank_relation s hs
  obtain ⟨b, _, hdegrees⟩ := exists_native_degree_approximation_bound s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_dependent_selection_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let P₀ := (p + a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  have hP₀ : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP₀P : P₀ ≤ P := by
    have hc : 0 ≤ (P₀ + 2) ^ 3 := by positivity
    dsimp only [P]
    linarith
  obtain ⟨hP₀C, h2PC, hdegreeC⟩ := hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, hHW, hH, hshort, _, hpq, hqP₀, R, ⟨D₀⟩⟩ :=
    hcommon W hF ((Real.exp_le_exp.mpr hP₀C).trans hN)
  obtain ⟨D, l, _, _, hl, hlbound, hdenom⟩ := D₀.exists_common_projected_denominator hP₀
  have hqP : q ≤ P := hqP₀.trans hP₀P
  have hpP : p ≤ P := hpq.trans hqP
  have hlP : (l : ℝ) ≤ Real.exp P := by
    apply hlbound.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    linarith
  obtain ⟨A⟩ := D.exists_sparse_anchors
  obtain ⟨h₀, hh₀⟩ := A.nonempty
  obtain ⟨m, hm, f, hf, n, hn, hnB, hln, happrox⟩ := hdegrees A h₀ hh₀
    (hp.trans hpq) hP hpP hqP c τ hG l hl hlP hdenom
    ((Real.exp_le_exp.mpr hdegreeC).trans hN)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, A.shifts_subset.trans hHW, ?_, m, hm, f, (fun d i j => (hf d i j).trans hdegreeC),
    n, hn, hnB.trans (Real.exp_le_exp.mpr hdegreeC), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h2PC))
      (Nat.cast_nonneg _)).trans A.density
  · intro t ht
    rw [hdenom t ht]
    exact hln
  · intro d hd h hh
    obtain ⟨e, u, he, hu, hres⟩ := happrox d hd h hh
    obtain ⟨z, hz, hcoords⟩ := D.exists_native_dependent_remainder hs c τ hG (α d) hd (f d) h h₀ e u hres
    refine ⟨e, u, ?_, hu, hres, z, hz, hcoords⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdegreeC) hscale.le)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_representative_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ E Q : (W.family.rank.filtration.layer
                    (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                  ‖(W.family.model.basis.baseChange ℝ).equivFun E.val‖ ≤
                    Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  (W.family.model.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid n ∧
                  W.family.horizontalCoefficient hs c τ hG (α d) h -
                      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) E -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) Q ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_coordinate_family s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_horizontal_lift_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let L := (B + 3) ^ 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBL : B ≤ L := by
    have h := le_power_budget (p := B + 1) (by linarith) (by decide : 1 ≤ 4)
    have heq : B + 1 + 2 = B + 3 := by ring
    rw [heq] at h
    exact (by linarith : B ≤ B + 1).trans h
  obtain ⟨hBC, hcut, hslow, hden⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, k, hk, f, hf, n, hn, hnB, hproj, happrox⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B := hpq.trans (hqP.trans hPB)
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) = d.val + 1 := by
    simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    rw [hdegree]
    omega
  have hpos (d : Fin s) : 1 ≤ Finsupp.weight (fun _ : Unit => 1) (α d) := by
    rw [hdegree]
    omega
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    simp only [α, ne_eq, Finsupp.single_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, not_false_eq_true]
  have hrep (d : Fin s) := W.family.rank.exists_controlled_horizontal_representatives
    ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le (hd d)⟩ (hpos d) hB
    (W.family.complexity.mono W.family.rank hpB) (hk d) (f d) (hf d) hn hnB
    (fun _ : Unit => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hcut).trans hN)
  choose m hm hmB hnm hsolve using hrep
  let M₀ := ∏ d, m d
  have hM₀ : 0 < M₀ := Finset.prod_pos (fun d _ => hm d)
  have hM₀B : (M₀ : ℝ) ≤ Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
    calc
      _ = ∏ d, (m d : ℝ) := by rw [Nat.cast_prod]
      _ ≤ ∏ _d : Fin s, Real.exp (L + ((L + 2) ^ 3 + (L + 2) ^ 36)) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun d _ => hmB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hmM₀ (d : Fin s) : m d ∣ M₀ := Finset.dvd_prod_of_mem m (Finset.mem_univ d)
  have hnM : n ∣ n * M₀ := dvd_mul_right _ _
  have hmM (d : Fin s) : m d ∣ n * M₀ := (hmM₀ d).trans (dvd_mul_left _ _)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC,
    R, D, A, h₀, hh₀, hAW, ?_, n * M₀, Nat.mul_pos hn hM₀, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · calc
      ((n * M₀ : ℕ) : ℝ) ≤ Real.exp B *
          Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hnB hM₀B (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (B + s * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hden
  · intro t ht
    exact (hproj t ht).trans hnM
  · intro d hd' h hh
    obtain ⟨e, u, he, hu, _, z, hz, hcoords⟩ := happrox d hd' h hh
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    obtain ⟨E, Q, _, _, hres, hE, hQ⟩ := hsolve d (α d) (hnonzero d)
      (W.family.horizontalCoefficient hs c τ hG (α d) h)
      (W.family.horizontalCoefficient hs c τ hG (α d) h₀) z e u hcoords
      (he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hBL) hscale.le)) hu
    refine ⟨E, Q, ?_, realDenominatorGrid_subset_of_dvd (hm d) (hmM d) hQ, ?_⟩
    · exact hE.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)
    · rw [hres]
      exact hz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace DegreeRankLieFiltration

end DegreeRankLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_polynomial_corrections (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ h ∈ A.shifts, ∃ E Q : W.family.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra
                  (fun _ : Unit => 1),
                coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) E.val ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n Q.val ∧
                ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  ∃ e u : (W.family.rank.filtration.layer
                      (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                    coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
                    W.family.horizontalCoefficient hs c τ hG (α d) h -
                        W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨C, hC, hfamily⟩ := exists_native_dependent_representative_family s hs
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnC, hproj, hrep⟩ := hfamily W hF c τ hG hN
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, hAW, hdensity, n, hn, hnC, hproj, ?_⟩
  intro h hh
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e u he hu hres using (fun d => hrep d (hd d) h hh)
  let E := positiveUnivariate (fun d => (e d).val)
  let Q := positiveUnivariate (fun d => (u d).val)
  refine ⟨⟨E, W.family.rank.filtration.positiveUnivariate_horizontal_mem e⟩,
    ⟨Q, W.family.rank.filtration.positiveUnivariate_horizontal_mem u⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.family.model.basis.baseChange ℝ)
      (fun d => (e d).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) he
  · exact positiveUnivariate_coefficientGrid (W.family.model.basis.baseChange ℝ)
      (fun d => (u d).val) n hu
  · intro d hd'
    exact ⟨e d, u d, positiveUnivariate_coefficient _ d, positiveUnivariate_coefficient _ d, hres d⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_polynomial_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ E Q : W.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1),
      coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
      CoefficientBound (W.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) E.val ∧
      CoefficientGrid (W.model.basis.baseChange ℝ) n Q.val ∧
      ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
        ∃ e u : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
          coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
          W.horizontalCoefficient hs c τ hG (α d) h₀ -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
            (fourFirstProjection (D.horizontal
              ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  intro α
  obtain ⟨e, u, he, hu, hres⟩ := A.exists_anchor_representative_corrections h₀ hh₀ hs hp hP c τ hG n hdenom
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  let E := positiveUnivariate (fun d => (e (α d)).val)
  let Q := positiveUnivariate (fun d => (u (α d)).val)
  refine ⟨⟨E, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => e (α d))⟩,
    ⟨Q, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => u (α d))⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.model.basis.baseChange ℝ)
      (fun d => (e (α d)).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) (fun d => he (α d) (hd d))
  · exact positiveUnivariate_coefficientGrid (W.model.basis.baseChange ℝ)
      (fun d => (u (α d)).val) n (fun d => hu (α d))
  · intro d hd'
    exact ⟨e (α d), u (α d), positiveUnivariate_coefficient _ d,
      positiveUnivariate_coefficient _ d, hres (α d) hd'⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

end NilpotentLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_dependent_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d) ξ) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ h ∈ A.shifts, ∃ ε γ v : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                    (fun _ : Unit => 1),
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 ε = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 γ = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 v = 1 ∧
                  CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                    (Real.exp ((p + C) ^ C)) ε.log ∧
                  CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                  ε * ξ * v * γ = W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                    Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                      hs c τ hG (fun _ : Unit => 1) (α d) v) ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_polynomial_corrections s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_reference_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hcost⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnB, hproj, hcorrection⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hq : 0 ≤ q := hp.trans hpq
  have hP : 0 ≤ P := hq.trans hqP
  let S := (P + 3) ^ 2 + (s : ℝ) * q
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hSB : S ≤ (B + 3) ^ 2 + s * B :=
    add_le_add (pow_le_pow_left₀ (by linarith) (add_le_add hPB (le_refl 3)) 2)
      (mul_le_mul_of_nonneg_left (hqP.trans hPB) (Nat.cast_nonneg s))
  have hsum : Real.exp B + Real.exp S ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp B + Real.exp B + Real.exp S := by linarith [Real.exp_nonneg B]
      _ ≤ Real.exp (B + S + 2) := exp_repeated_add_le hB hS
      _ ≤ _ := Real.exp_le_exp.mpr ((add_le_add (add_le_add (le_refl B) hSB) (le_refl 2)).trans hcost)
  obtain ⟨E₀, Q₀, hE₀zero, hQ₀zero, hE₀, hQ₀, href⟩ :=
    A.exists_anchor_polynomial_corrections h₀ hh₀ hs hq hP c τ hG n hproj
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e₀ u₀ he₀ hu₀ hfirst using (fun d => href d (hd d))
  let ε₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨E₀.val⟩, E₀.property⟩
  let γ₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨Q₀.val⟩, Q₀.property⟩
  let g₀ := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h₀)
  let ξ := ε₀⁻¹ * g₀ * γ₀⁻¹
  have hε₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ε₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε₀).mpr hE₀zero
  have hγ₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 γ₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ₀).mpr hQ₀zero
  have hg₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g₀ = 1 := W.family.orbit_rank_normalized h₀
  have hξzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ξ = 1 := by
    simp only [ξ, map_mul, map_inv, hε₀zero, hγ₀zero, hg₀, inv_one, one_mul]
  have hξvalue (d : Fin s) :
      Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hG (fun _ : Unit => 1) (α d) ξ) =
      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (e₀ d) -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (u₀ d) := by
    have he := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) ε₀ (e₀ d) (he₀ d).symm
    have hu := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) γ₀ (u₀ d) (hu₀ d).symm
    have h := toAdd_hom_corrected_reference
      (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ε₀ g₀ γ₀
    rw [he, hu] at h
    exact h
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξzero, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd'
    rw [hξvalue]
    exact hfirst d
  · intro h hh
    obtain ⟨E, Q, hEzero, hQzero, hE, hQ, hres⟩ := hcorrection h hh
    let ε : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(E + E₀).val⟩, (E + E₀).property⟩
    let γ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(Q + Q₀).val⟩, (Q + Q₀).property⟩
    let g := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h)
    let v := ξ⁻¹ * ε⁻¹ * g * γ⁻¹
    have hεzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 ε = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε).mpr
      change coefficients (E.val + E₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hEzero, hE₀zero, add_zero]
    have hγzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 γ = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ).mpr
      change coefficients (Q.val + Q₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hQzero, hQ₀zero, add_zero]
    have hg : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 g = 1 := W.family.orbit_rank_normalized h
    refine ⟨ε, γ, v, hεzero, hγzero, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, map_mul, map_inv, hξzero, hεzero, hg, hγzero, inv_one, one_mul]
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N)
        (CoefficientBound.add _ _ hE hE₀) hsum
    · exact CoefficientGrid.add _ _ hQ hQ₀
    · change ε * ξ * v * γ = g
      dsimp only [v]
      group
    · intro d hd'
      obtain ⟨e, u, he, hu, hdep⟩ := hres d hd'
      let π := W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d))
      have hεvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) ε) = π e + π (e₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) ε (e + e₀ d) ?_).trans (map_add π e (e₀ d))
        change e.val + (e₀ d).val = coefficients (E.val + E₀.val) (α d)
        rw [map_add, Finsupp.add_apply, he, he₀]
      have hγvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) γ) = π u + π (u₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) γ (u + u₀ d) ?_).trans (map_add π u (u₀ d))
        change u.val + (u₀ d).val = coefficients (Q.val + Q₀.val) (α d)
        rw [map_add, Finsupp.add_apply, hu, hu₀]
      have hv := toAdd_hom_corrected_factor
        (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ξ ε g γ
      rw [hξvalue d, hεvalue, hγvalue] at hv
      have hv' := hv.trans (sub_corrected_reference_add_errors
        (W.family.horizontalCoefficient hs c τ hG (α d) h)
        (W.family.horizontalCoefficient hs c τ hG (α d) h₀) (π e) (π u) (π (e₀ d)) (π (u₀ d)))
      exact (congrArg (fun z => z ∈ (fourDependentProjection (D.horizontal
        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd'⟩)).baseChange ℝ) hv').mpr hdep

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_periodic_common_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_common_dependent_factorization s hs
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨C, hC, hbudget⟩ := exists_native_periodic_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hperiodC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, hn, hnB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 1 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  obtain ⟨M, hM, hMB, hMsolve⟩ := hperiod W.family.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) (B + 1) (by linarith)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono W.family.model W.family.complexity.1 hpB)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using (show (1 : ℝ) ≤ B + 1 by linarith))
    n hn (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
  have hlog (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1)) :
      ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g).log = g.log := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_log (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g)).symm
  have heval (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1))
      (x : Unit → ℤ) :
      W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x
          ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) =
        W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) x g := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_eval (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) x).symm
  let ξ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ξ
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hperiodC), hproj, ξ', (heval ξ 0).trans hξ₀, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd
    simpa only [ξ', MulEquiv.apply_symm_apply] using hfirst d hd
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep⟩ := hsplit h hh
    let ε' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ε
    let γ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm γ
    let v' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm v
    have hgrid : CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ'.log := by
      simpa only [γ', hlog] using hγ
    refine ⟨ε', γ', v', (heval ε 0).trans hε₀, (heval γ 0).trans hγ₀,
      (heval v 0).trans hv₀, ?_, hgrid, ?_, ?_, hMsolve γ' hgrid⟩
    · apply CoefficientBound.mono (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
        (M := Real.exp B) _ (Real.exp_le_exp.mpr hBC)
      simpa only [ε', hlog] using hε
    · have hf := congrArg (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm heq
      simpa only [map_mul, MulEquiv.symm_apply_apply] using hf
    · intro d hd
      simpa only [v', MulEquiv.apply_symm_apply] using hdep d hd

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_frozen_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                (∃ y : ZMod N,
                  (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
                    (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
                  Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                    (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
                      (W.family.vertical.observable i) ε (ξ * v) γ y x)))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_periodic_common_factorization s (by omega)
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_common_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hFC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep, hperiod⟩ := hsplit h hh
    have hε' : CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp (((B + 2) + 2) ^ 1)) ε.log :=
      CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
        (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
    obtain ⟨y, hunit, V⟩ := hfreeze W hF ⟨h, hAW hh⟩ (B + 2) (by linarith) hpB M hM
      (hMB.trans (Real.exp_le_exp.mpr (by linarith))) ε ξ v γ heq hε'
      (fun x y hxy => (hperiod x y hxy).1) ((Real.exp_le_exp.mpr hFC).trans hN)
    refine ⟨ε, γ, v, hε₀, hγ₀, hv₀, ?_, hγ, heq, hdep,
      ⟨y, hunit, ⟨(Classical.choice V).mono hFC⟩⟩, hperiod⟩
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
      (Real.exp_le_exp.mpr hBC)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def realCoefficientFourSpace (d : Fin (s + 1)) :
    Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] W.L) :=
  ((D.coefficientFourSpace d).baseChange ℝ).map
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).toLinearMap

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem mem_real_coefficientFourSpace (d : Fin (s + 1))
    (v : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) v.val ∈
        D.realCoefficientFourSpace d ↔
      W.rank.filtration.realFourHorizontalMap d.val v ∈ (D.horizontal d).baseChange ℝ := by
  obtain ⟨x, rfl⟩ :=
    (realificationSubmoduleEquiv (W.rank.filtration.fourHorizontalLayer d.val)).surjective v
  rw [W.rank.filtration.realFourHorizontalMap_baseChange]
  unfold realCoefficientFourSpace
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    realificationSubmoduleEquiv_coe, coefficientFourSpace, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := realification_subtype_injective (W.rank.filtration.fourHorizontalLayer d.val) he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.finite_combined_free_sunflower {J : Type*} [Fintype J]
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → D.CoefficientFreeLieAlgebra) (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (i j : J) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ D.dependentFreeSpan (d i)) (hvj : v j ∈ D.dependentFreeSpan (d j)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp (k : J) (hk : k ∈ lieTreeSupport a) : e k ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨k, hk, rfl⟩
  have h := B.combined_free_sunflower D (Fintype.card J) (fun k => d (e.symm k))
    (FreeMagma.map e a) hweight ((lieTreeLength_relabel e a).trans hr)
    (fun k => v (e.symm k)) (fun k => hv (e.symm k)) (e i) (e j)
    (fun h => hij (e.injective h)) (hsupp i hi) (hsupp j hj)
    (by simpa only [Equiv.symm_apply_apply] using hvi)
    (by simpa only [Equiv.symm_apply_apply] using hvj)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.exists_free_tree_linearization {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x : J → D.CoefficientFreeLieAlgebra) (hx : ∀ i, x i ∈ D.coefficientFreeSpan (d i)) :
    ∃ A : (∀ i, D.dependentFreeSpan (d i)) →ₗ[ℚ] ℚ, ∀ y : ∀ i, D.dependentFreeSpan (d i),
      B.freeFrequency D (lieTreeEval (fun i => x i + (y i : D.CoefficientFreeLieAlgebra)) a) =
        B.freeFrequency D (lieTreeEval x a) + A y := by
  apply exists_linear_lieTree_expansion (B.freeFrequency D)
    (fun i => D.coefficientFreeSpan (d i)) (fun i => D.dependentFreeSpan (d i))
    (fun i => D.dependentFreeSpan_le_coefficientFreeSpan (d i)) a x hx
  intro v hv i j hij hi hj
  exact B.finite_combined_free_sunflower D (fun k => d (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i j hij
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi hj

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.free_refined_four_identity {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℚ (Fin 4 → D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0)
    (v : J → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (K i)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  four_refined_affine_identity _ _ _
    (fun x hx => B.exists_free_tree_linearization D d a hd hr x hx) K hK v hv

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.correlation_four_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 := by
  have h := D'.coefficient_four_frequency n (fun i => ⟨(d i).val + 1, by omega⟩)
    a hd hr v hv
  change fourFunctionDifference (fun x => V.frequency (lieTreeEval x a)) v = 0 at h
  simpa only [hfreq] using h

theorem CoefficientBases.correlation_refined_four_identity
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  B.free_refined_four_identity D d a hd hr _
    (B.correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Finset
open scoped _root_.Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => _root_.OAI.Finset.addEnergy' s t
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => _root_.OAI.Finset.addEnergy' s s

end Finset

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'


variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [StarRing K]

scoped[BSGConvolution] infixl:71 " ○ " => _root_.OAI.Erdos3.BSG.dconv

open scoped BSGConvolution

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Function
open scoped ComplexConjugate BSGConvolution

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  [StarRing K] [StarOrderedRing K] {f g : G → K}

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset hiding card
open _root_.OAI.Finset
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator BSGConvolution

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma1

end lemma1

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

end lemma2

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.BSG

end

section

namespace Erdos3

open scoped Pointwise

variable {G V : Type*} [DecidableEq G] [DecidableEq V]

variable [AddCommGroup G] [Fintype G] [AddCommGroup V] [Fintype V]

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem variable_coefficient_graph_energy {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    Real.exp (-(P + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  apply variable_graph_energy_density H D.quadruples a c M l ε _ hsmall _ _
  · intro t ht
    let J := R.interval ⟨t, D.subset ht⟩
    exact ⟨J.first_mem, J.second_mem, J.third_mem, J.fourth_mem⟩
  · intro t ht
    exact hnear t ht
  · have hcard : (H.card : ℝ) ≤ Fintype.card (ZMod N) := by
      exact_mod_cast Finset.card_le_univ H
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3)
      (Real.exp_nonneg _)).trans D.density

theorem variable_graph_small_difference {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J (fun h => variableRoundedCoefficient M l (a h)) -
        additiveGraph J (fun h => variableRoundedCoefficient M l (a h))).card : ℝ) ≤
          (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  intro K
  classical
  obtain ⟨t, ht⟩ := D.nonempty
  have hH : H.Nonempty := ⟨t.2.1, (R.interval ⟨t, D.subset ht⟩).first_mem⟩
  apply exists_large_graph_subset_small_difference H hH (fun h => variableRoundedCoefficient M l (a h))
    (Real.exp_pos _) _
  simpa only [Real.exp_neg] using D.variable_coefficient_graph_energy a c M l ε hsmall hnear

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonOrbit
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem paired_affine_orbit_coefficient_mem_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
    (d : Fin s) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      (petalComparisonSpace
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
        (fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
        (D.coefficientFreeFiltration.layer (d.val + 1) 2)).baseChange ℝ := by
  have h₁ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) A K
  have h₂ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) (A * K) U
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at h₁ h₂
  have herr : coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
      (coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1))) ∈
      (D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ := by
    rw [← hTfil]
    convert ((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem
      (((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem h₂ h₁) (hK d) using 1
    abel
  have hp : ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      petalComparisonSpace
        (((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
        ((fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
        ((D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ) := by
    apply (mem_petalComparisonSpace _ _ _ _).mpr
    constructor
    · exact Submodule.mem_sup_left (hA d)
    · apply Submodule.mem_sup.mpr
      refine ⟨_, hU d, _, herr, ?_⟩
      change coefficients U.log (Finsupp.single () (d.val + 1)) +
        (coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          (coefficients A.log (Finsupp.single () (d.val + 1)) +
            coefficients U.log (Finsupp.single () (d.val + 1)))) =
        coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          coefficients A.log (Finsupp.single () (d.val + 1))
      abel
  rw [← realification_petalComparisonSpace] at hp
  obtain ⟨y, hy, heq⟩ := hp
  have hy' : (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] = y := by
    rw [← heq]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hy']
  exact hy

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end


