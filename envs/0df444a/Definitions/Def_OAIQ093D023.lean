-- Prove2me | Definitions.Def_OAIQ093D023
-- name    : OAIQ093D023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T19:18:12.548996+00:00
-- url     : https://prove2.me/theorems/57adfa90-0e53-4526-9b37-eef8da2af451
-- title:
--   Definitions bundle OAIQ093D023 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 10 definitions and 9 theorems. The definitions and types are `OAI.PolycyclicRecognition.ComplexWeightFactorModel.cartanFactorToRotation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.nilpotentFactorToRotation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.originalToSmoothRotationExtension`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationExponentialProduct`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationFactorAction`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationFactorParameter`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationWeightCharacter`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothModificationToRotationExtension`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationHomeomorph`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationMetric`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Geometry_ActualSmoothRotation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/ActualSmoothRotation.lean), [`PolycyclicRecognition_Geometry_RotationExponentialProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationExponentialProduct.lean), [`PolycyclicRecognition_Geometry_RotationFactorAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationFactorAction.lean), [`PolycyclicRecognition_Geometry_RotationFactorKernel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationFactorKernel.lean), [`PolycyclicRecognition_Geometry_RotationFactorLifts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationFactorLifts.lean), [`PolycyclicRecognition_Geometry_RotationFactorParameter`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationFactorParameter.lean), [`PolycyclicRecognition_Geometry_RotationFactorProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationFactorProduct.lean), [`PolycyclicRecognition_Geometry_SmoothRotationExtension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/SmoothRotationExtension.lean).
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundle `OAIQ093D022` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D025`; the statements `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_conjugation` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_faithful`; the proofs of `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_conjugation`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_faithful`, `OAI.PolycyclicRecognition.cornulierTesseraModelInput`, `OAI.PolycyclicRecognition.group_recognition_of_gromov` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ActualSmoothRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth rotational modification from the actual Cartan factors

The chosen compact action retains its factor formula. This constructs a
smooth graph group; its Lie algebra identification and triangular matrix
realization are separate steps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

attribute [local instance] semidirectProductTopology

attribute [local instance] smoothRotationalModificationChartedSpace

def smoothRotationalModificationHomeomorph : F.SmoothRotationalModification hExp ≃ₜ G :=
  rotationalTwistHomeomorph (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.continuous_rotationCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothRotationExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth graph and its compact extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

/-- The metric has exactly the existing graph topology. -/
@[instance_reducible]
def smoothRotationalModificationMetric : MetricSpace (F.SmoothRotationalModification hExp) :=
  (F.smoothRotationalModificationHomeomorph hExp).isEmbedding.comapMetricSpace
    (F.smoothRotationalModificationHomeomorph hExp)

def originalToSmoothRotationExtension :
    ProperCocompactHom G (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirect_inl_properCocompact (F.factorCompactRotationAction hExp)

def smoothModificationToRotationExtension :
    ProperCocompactHom (F.SmoothRotationalModification hExp)
      (G ⋊[F.factorCompactRotationAction hExp] realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact rotationalTwist_properCocompact (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.continuous_rotationCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original nilpotent factors inside the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

local instance instFactContinuousSubtypeForallWeightComplexTensorProductRealGroupLieAlgebraModelWithCornersSelfMemLieSubalgebraComplexifiedSubalgebraCircleSubgroupComplexCartanTorusRealRotationTorusCoeMonoidHomRotationCharacter_r4ee6de_1 : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
local instance instChartedSpaceSmoothRotationalModification_1_r4ee6de_1 : ChartedSpace E (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationChartedSpace hExp
set_option maxHeartbeats 1000000 in
theorem rotationCharacter_inclusionN (n : F.N.carrier) :
    F.rotationCharacter (F.inclusionN n) = 1 := by
  obtain ⟨x,rfl⟩ := F.expN_surjective n
  exact F.rotationCharacter_nilradical x

set_option maxHeartbeats 1000000 in
theorem inverse_rotation_fixes_nilpotent_factor (n m : F.N.carrier) :
    F.factorCompactRotationAction hExp ((F.rotationCharacter (F.inclusionN n))⁻¹)
      (F.inclusionN m) = F.inclusionN m := by
  exact rotation_inv_apply_of_eq_one (F.factorCompactRotationAction hExp)
    (F.rotationCharacter_inclusionN n) (F.inclusionN m)

set_option maxHeartbeats 1000000 in
theorem inverse_rotation_fixes_cartan_factor (d e : F.D.carrier) :
    F.factorCompactRotationAction hExp ((F.rotationCharacter (F.inclusionD d))⁻¹)
      (F.inclusionD e) = F.inclusionD e :=
  F.rotation_fixes_cartan_factor (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp) _ e

set_option maxHeartbeats 1000000 in
/-- The actual nilpotent kernel embeds with its original multiplication. -/
def nilpotentFactorToRotation : F.N.carrier →* F.SmoothRotationalModification hExp :=
  rotationalTwistLift (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionN
    (F.inverse_rotation_fixes_nilpotent_factor hExp)

set_option maxHeartbeats 1000000 in
/-- The Cartan factor also retains its original multiplication. -/
def cartanFactorToRotation : F.D.carrier →* F.SmoothRotationalModification hExp :=
  rotationalTwistLift (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionD
    (F.inverse_rotation_fixes_cartan_factor hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global factor coordinates for the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem closedEmbedding_nilpotentFactorToRotation :
    Topology.IsClosedEmbedding (F.nilpotentFactorToRotation hExp) :=
  Topology.IsClosedEmbedding.of_comp
    (F.smoothRotationalModificationHomeomorph hExp).isEmbedding F.closedN

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationExponentialProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global exponential factor coordinates and cancellation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationExponentialProduct (p : T.kernelIdeal × H) : F.SmoothRotationalModification hExp :=
  F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv p.1)) *
    F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv p.2))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent factor remains the kernel of the weight character -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

omit [H.IsCartanSubalgebra] in
theorem weightCharacter_inclusionN (n : F.N.carrier) :
    F.weightCharacter (F.inclusionN n) = 1 := by
  obtain ⟨x,rfl⟩ := F.expN_surjective n
  exact F.weightCharacter_nilradical x

theorem inclusionN_range_eq_weightKernel :
    Set.range F.inclusionN = (F.weightCharacter.ker : Set G) := by
  ext g
  constructor
  · rintro ⟨n,rfl⟩
    exact F.weightCharacter_inclusionN n
  · intro hg
    obtain ⟨⟨n,d⟩,rfl⟩ := F.surjective g
    obtain ⟨h,rfl⟩ := F.expD_surjective d
    have hh : F.weightCharacter (Exp h) = 1 := by
      change F.weightCharacter (F.inclusionN n * F.inclusionD (F.ExpD (F.D.equiv h))) = 1 at hg
      rw [map_mul, F.weightCharacter_inclusionN, one_mul, F.compatibleD] at hg
      exact hg
    have hw : T.weightMap.rangeRestrict h = 0 :=
      (F.weightCharacter_exp h).symm.trans (congrArg Multiplicative.toAdd hh)
    have hz : T.weightMap h = 0 := congrArg Subtype.val hw
    let x : T.kernelIdeal := ⟨h,hz⟩
    refine ⟨n * F.ExpN (F.N.equiv x), ?_⟩
    change F.inclusionN (n * F.ExpN (F.N.equiv x)) =
      F.inclusionN n * F.inclusionD (F.ExpD (F.D.equiv h))
    rw [map_mul, F.compatibleN, F.compatibleD]

variable (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem weightCharacter_invariant_rotation (z) (g : G) :
    F.weightCharacter (F.factorCompactRotationAction hExp z g) = F.weightCharacter g := by
  exact character_invariant_of_factor_coordinates F.inclusionN F.inclusionD
    F.weightCharacter (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    F.expN_surjective F.surjective (fun z x => T.nilradicalRotation H z x)
    (fun z g => F.factorCompactRotationAction hExp z g) F.weightCharacter_nilradical
    (F.factorCompactRotationAction_formula hExp) z g

/-- The full vector-valued character survives the modification. -/
def rotationWeightCharacter :
    F.SmoothRotationalModification hExp →* Multiplicative T.weightMap.range :=
  rotationalTwistCharacter (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.weightCharacter
    (F.weightCharacter_invariant_rotation hExp)

theorem rotationWeightCharacter_kernel :
    (F.rotationWeightCharacter hExp).ker = (F.nilpotentFactorToRotation hExp).range := by
  apply SetLike.ext
  intro g
  change F.weightCharacter g.val.left = 1 ↔
    ∃ n, F.nilpotentFactorToRotation hExp n = g
  constructor
  · intro hg
    have hr : g.val.left ∈ Set.range F.inclusionN := by
      rw [F.inclusionN_range_eq_weightKernel]
      exact hg
    obtain ⟨n,hn⟩ := hr
    exact ⟨n,(F.smoothRotationalModificationHomeomorph hExp).injective hn⟩
  · rintro ⟨n,rfl⟩
    exact F.weightCharacter_inclusionN n

/-- Normality now follows from an actual homomorphism kernel. -/
theorem normal_nilpotentFactorToRotation :
    (F.nilpotentFactorToRotation hExp).range.Normal := by
  rw [← F.rotationWeightCharacter_kernel hExp]
  infer_instance

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Cartan action on the nilpotent factor of the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationFactorAction : F.D.carrier →* MulAut F.N.carrier :=
  conjugationLiftOfNormal (F.nilpotentFactorToRotation hExp) (F.cartanFactorToRotation hExp)
    (F.closedEmbedding_nilpotentFactorToRotation hExp).injective
    (F.normal_nilpotentFactorToRotation hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorParameter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local coordinates for the rotational graph from the original factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationFactorParameter (v : E) : F.SmoothRotationalModification hExp :=
  F.nilpotentFactorToRotation hExp (F.ExpN (F.kernelParameter v)) *
    F.cartanFactorToRotation hExp (F.ExpD (F.cartanParameter v))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end


