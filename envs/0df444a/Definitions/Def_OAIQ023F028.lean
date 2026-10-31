-- Prove2me | Definitions.Def_OAIQ023F028
-- name    : OAIQ023F028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:01:54.929254+00:00
-- url     : https://prove2.me/theorems/6e2fa510-ac61-4cca-ac66-5eafbac0b179
-- title:
--   Definitions bundle OAIQ023F028 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 18 definitions, 1 instance and 13 theorems. The definitions and types are `OAI.LittleFinitistic.CanonicalArrowCompatibility.compatibility01`, `OAI.LittleFinitistic.CanonicalArrowCompatibility.compatibility12`, `OAI.LittleFinitistic.ConcreteAdjacentGraded.arrow01Sum`, `OAI.LittleFinitistic.ConcreteAdjacentGraded.arrow12Sum`, `OAI.LittleFinitistic.ConcreteTensorEvaluation.idealEquiv`, `OAI.LittleFinitistic.EncodingLinearity.linearEquiv`, `OAI.LittleFinitistic.EncodingLinearity.linearMap`, `OAI.LittleFinitistic.EvaluationVertexDiagram.action`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.ordinaryOObject`, `OAI.LittleFinitistic.QuadraticEncoding.BoundedK`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.ofAction`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.ofModule`, `OAI.LittleFinitistic.QuadraticEncoding.actionArrow`, `OAI.LittleFinitistic.RelationVertexSequence.originalSequence`, `OAI.LittleFinitistic.SelectedFixedDiagram.P`, `OAI.LittleFinitistic.SelectedRectification.F`, `OAI.LittleFinitistic.SelectedTensorComparison.tensor`, `OAI.LittleFinitistic.ThirdVertex.iota`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_EncodingGenerators`, `Finitistic_Encoding_EncodingLinearity`, `Finitistic_Encoding_RelationVertexSequence`, `Finitistic_Localization_BoundedQuotientEvaluation`, `Finitistic_Localization_ConcreteTensorEvaluation`, `Finitistic_Localization_EvaluationFromAlgebra`, `Finitistic_Localization_EvaluationVertexDiagram`, `Finitistic_Localization_HomotopyVertexEvaluation`, `Finitistic_Localization_QuotientActionEvaluation`, `Finitistic_Ordinary_OrdinaryXResolution`, `Finitistic_Rectification_CanonicalArrowCompatibility`, `Finitistic_Rectification_ConcreteAdjacentGraded`, `Finitistic_Rectification_CornerArrowCoordinates`, `Finitistic_Rectification_ThirdVertex`, `Finitistic_Selected_SelectedFixedDiagram`, `Finitistic_Selected_SelectedRectification`, `Finitistic_Selected_SelectedTensorComparison`.
--
--   **Imports.** It imports the bundles `OAIQ023F025` and `OAIQ023F026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F031` and `OAIQ023F032`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F025
import Definitions.Def_OAIQ023F026

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingGenerators
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.EncodingGenerators
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma path_mem (S : Subalgebra k (B P))
    (h01 : ∀ a, arrow01 P a ∈ S) (h12 : ∀ a, arrow12 P a ∈ S)
    (x : Paths k d) : pathMap P x ∈ S := by
  have hx := congrArg (pathMap P)
    ((RelationBasisCoefficients.pathBasis (k := k) (d := d)).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  apply S.sum_mem
  intro ⟨b,a⟩ _
  rw [map_smul]
  apply S.smul_mem
  simp only [RelationBasisCoefficients.pathBasis, Module.Basis.tensorProduct_apply,
    Pi.basisFun_apply]
  change pathMap P (basis b ⊗ₜ[k] basis a) ∈ S
  rw [← arrow_product]
  exact S.mul_mem (h12 b) (h01 a)

/-- Vertices and the specified finite arrow list generate the full encoding,
including the quotient length-two path component. -/
theorem eq_top (S : Subalgebra k (B P))
    (hv : ∀ i, ThreeVertexAlgebra.vertex (composition P) i ∈ S)
    (h01 : ∀ a, arrow01 P a ∈ S) (h12 : ∀ a, arrow12 P a ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  rcases x with ⟨c0,c1,c2,v,w,z⟩
  obtain ⟨r,hr⟩ := Submodule.Quotient.mk_surjective (relationSpace P) z
  have hz : lengthTwo P z ∈ S := by
    rw [← hr]
    exact path_mem P S h01 h12 r
  have h := S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem
    (S.smul_mem (hv 0) c0) (S.smul_mem (hv 1) c1)) (S.smul_mem (hv 2) c2))
    (first_mem P S h01 v)) (second_mem P S h12 w)) hz
  simpa [ThreeVertexAlgebra.vertex, ThreeVertexAlgebra.add_eq,
    ThreeVertexAlgebra.smul_eq, first, second, lengthTwo] using h
end LittleFinitistic.EncodingGenerators

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingLinearity
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.EncodingLinearity
open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module (B P) M] [Module (B P) N]
  [IsScalarTower k (B P) M] [IsScalarTower k (B P) N]

/-- Full B-linearity follows from the actual three vertex and two finite arrow lists.
Length-two actions require no additional hypothesis. -/
theorem map_smul (f : M →ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x)
    (b : B P) (x : M) : f (b • x) = b • f x := by
  have h := EncodingGenerators.eq_top P (intertwining P f) hv h01 h12
  have hb : b ∈ intertwining P f := by rw [h]; trivial
  exact hb x

/-- The original k-linear map, upgraded without changing its values. -/
def linearMap (f : M →ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x) : M →ₗ[B P] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_smul P f hv h01 h12

/-- A vector-space isomorphism respecting the finite generating actions is a
B-module isomorphism with exactly the original forward and inverse functions. -/
def linearEquiv (f : M ≃ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x) : M ≃ₗ[B P] N :=
  { linearMap P f.toLinearMap hv h01 h12, f.toEquiv with }
end LittleFinitistic.EncodingLinearity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerArrowCoordinates
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.CornerArrowCoordinates
open QuadraticEncoding CornerColumnPaths
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- On the adjacent 1,0 corner, the original a-arrow inserts its actual basis vector. -/
theorem arrow01_coordinate (a : Fin (d+1)) (c : k) :
    CornerSpaces.corner10Equiv (composition P)
      (cornerMap (composition P) 1 0 1 (arrow01 P a)
        ((ConcreteQuadraticDiagram.quadratic P).ha a)
        ((CornerSpaces.diagonalEquiv (composition P) 1).symm c)) = c • basis a := by
  simp [CornerSpaces.corner10Equiv,cornerMap,CornerSpaces.diagonalEquiv,
    arrow01,ThreeVertexAlgebra.mul,ThreeVertexAlgebra.vertex]

/-- On the adjacent 2,1 corner, the original b-arrow inserts its actual basis vector. -/
theorem arrow12_coordinate (b : Fin (d+1)) (c : k) :
    CornerSpaces.corner21Equiv (composition P)
      (cornerMap (composition P) 2 1 2 (arrow12 P b)
        ((ConcreteQuadraticDiagram.quadratic P).hb b)
        ((CornerSpaces.diagonalEquiv (composition P) 2).symm c)) = c • basis b := by
  simp [CornerSpaces.corner21Equiv,cornerMap,CornerSpaces.diagonalEquiv,
    arrow12,ThreeVertexAlgebra.mul,ThreeVertexAlgebra.vertex]

/-- Length-two multiplication is exactly the quotient of the original tensor path. -/
theorem lengthTwo_coordinate (a : Fin (d+1)) (w : Arrows k d) :
    CornerSpaces.corner20Equiv (composition P)
      (cornerMap (composition P) 2 0 1 (arrow01 P a)
        ((ConcreteQuadraticDiagram.quadratic P).ha a)
        ((CornerSpaces.corner21Equiv (composition P)).symm w)) =
      (relationSpace P).mkQ (w ⊗ₜ[k] basis a) := by
  change (0 : k) • (0 : Paths k d ⧸ relationSpace P) +
    (relationSpace P).mkQ (w ⊗ₜ[k] basis a) + (0 : k) • 0 = _
  simp only [zero_smul, zero_add, add_zero]

end LittleFinitistic.CornerArrowCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexSequence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexSequence
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
open ExternalTensor.Section4.SourceFiltration RelationVertexCoordinates
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
local notation "data" => Exactness.data s D₀ D₁ D₂ f g

attribute [local instance] OAI.LittleFinitistic.RelationVertexSequence.instHasFiniteBiproductsRightComplexB
attribute [local instance] OAI.LittleFinitistic.RelationVertexSequence.instHasFiniteBiproductsBiComplexB
def originalSequence : ShortComplex (BiComplex k T) := .mk (q0 data) (p0 data) (q0_p0 data)

end LittleFinitistic.RelationVertexSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy IdempotentTensor
universe u v

namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The exact bounded-projective source category used in Section 3. -/
abbrev BoundedK := K.{u,u} (B P)ᵐᵒᵖ

end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ConcreteTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TensorComplex.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Category
namespace LittleFinitistic.ConcreteTensorEvaluation
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- Match the opposite-regular presentation of eB to the fixed-point presentation. -/
def idealEquiv (e : B P) (he : e*e=e) :
    VertexProjectives.ideal e ≃ₗ[(B P)ᵐᵒᵖ] IdempotentTensor.rightIdeal e where
  toFun x := ⟨x.val.unop, by
    exact congrArg MulOpposite.unop (VertexProjectives.fixed e he x)⟩
  invFun x := ⟨MulOpposite.op x.val, ⟨MulOpposite.op x.val, by
    change MulOpposite.op x.val * MulOpposite.op e = MulOpposite.op x.val
    exact congrArg MulOpposite.op x.property⟩⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' a x := rfl

instance vertexScalarTower (i : Fin 3) :
    IsScalarTower k (B P)ᵐᵒᵖ (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj) :=
  BalancedTensor.scalarModuleTower k (B P) (SourceVerdier.E P i).obj

end LittleFinitistic.ConcreteTensorEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationFromAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {R : Type v} [Ring R] [Algebra k R]

namespace Representation
variable {P} {Y : Type w} [AddCommGroup Y] [Module k Y]

/-- Evaluate the quadratic presentation in any actual algebra action. -/
def ofAction (x : Fin d → R) (hx : P.Satisfies x) (ρ : R →ₐ[k] Module.End k Y) :
    Representation P Y where
  generator h := ρ (x h)
  relation j := by
    have h := congrArg ρ (hx j)
    simpa only [map_add, map_sum, map_smul, map_mul, map_one, map_zero] using h

/-- In particular, every R-module supplies the required representation. -/
def ofModule (x : Fin d → R) (hx : P.Satisfies x)
    [Module R Y] [IsScalarTower k R Y] : Representation P Y :=
  ofAction x hx (Algebra.lsmul k k Y)

@[simp] theorem ofModule_generator (x : Fin d → R) (hx : P.Satisfies x)
    [Module R Y] [IsScalarTower k R Y] (h : Fin d) (y : Y) :
    (ofModule (Y := Y) x hx).generator h y = x h • y := rfl
end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationVertexDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.EvaluationVertexDiagram
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def action (a : Fin (d+1)) : ModuleCat.of k Y ⟶ ModuleCat.of k Y :=
  ModuleCat.ofHom (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator a)

end LittleFinitistic.EvaluationVertexDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_HomotopyVertexEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open BalancedTensor FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def actionArrow (h : Fin (d+1)) : ModuleCat.of k (ULift.{u} Y) ⟶ ModuleCat.of k (ULift.{u} Y) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h).comp
      ULift.moduleEquiv.toLinearMap))

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_QuotientActionEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

@[simp] lemma actionArrow_zero : actionArrow X 0 = 𝟙 _ := by ext y; rfl

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

abbrev ordinaryOObject : ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ) :=
  RetainedBimodule.object k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)

end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ConcreteAdjacentGraded
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ConcreteAdjacentGraded
open ExternalTensor.Section4 QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D : RightComplex (QuadraticEncoding.B P))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

def arrow01Sum : (⨁ fun _ : Fin (d+1) => (columnComplex k T (s).e₁).obj D) ⟶
    (columnComplex k T (s).e₀).obj D :=
  biproduct.desc (fun a => path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D)

def arrow12Sum : (⨁ fun _ : Fin (d+1) => (columnComplex k T (s).e₂).obj D) ⟶
    (columnComplex k T (s).e₁).obj D :=
  biproduct.desc (fun b => path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D)

theorem vertex1_arrow01_isIso :
    IsIso ((AdjacentArrowSum.vertexComplex (composition P) 1).map (arrow01Sum P D)) := by
  let F := AdjacentArrowSum.vertexComplex (composition P) 1
  have hdesc := AdjacentArrowSum.desc_isIso (composition P) D 1 0 d
    (CornerSpaces.corner10Equiv (composition P)) (arrow01 P) ((s).ha)
    (CornerArrowCoordinates.arrow01_coordinate P)
  let : IsIso (biproduct.desc (fun a => F.map
    (path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D))) := hdesc
  change IsIso (F.map (biproduct.desc _))
  rw [← biproduct.mapBiproduct_hom_desc,isIso_comp_left_iff]
  exact hdesc

theorem vertex2_arrow12_isIso :
    IsIso ((AdjacentArrowSum.vertexComplex (composition P) 2).map (arrow12Sum P D)) := by
  let F := AdjacentArrowSum.vertexComplex (composition P) 2
  have hdesc := AdjacentArrowSum.desc_isIso (composition P) D 2 1 d
    (CornerSpaces.corner21Equiv (composition P)) (arrow12 P) ((s).hb)
    (CornerArrowCoordinates.arrow12_coordinate P)
  let : IsIso (biproduct.desc (fun b => F.map
    (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))) := hdesc
  change IsIso (F.map (biproduct.desc _))
  rw [← biproduct.mapBiproduct_hom_desc,isIso_comp_left_iff]
  exact hdesc

/-- The first adjacent graded cone is acyclic for the actual arrow map. -/
theorem vertex1_cone_acyclic :
    (CochainComplex.mappingCone
      ((AdjacentArrowSum.vertexComplex (composition P) 1).map (arrow01Sum P D))).Acyclic := by
  let := vertex1_arrow01_isIso P D
  exact RectificationAcyclic.cone_acyclic _

/-- The second adjacent graded cone is acyclic for the actual arrow map. -/
theorem vertex2_cone_acyclic :
    (CochainComplex.mappingCone
      ((AdjacentArrowSum.vertexComplex (composition P) 2).map (arrow12Sum P D))).Acyclic := by
  let := vertex2_arrow12_isIso P D
  exact RectificationAcyclic.cone_acyclic _
end LittleFinitistic.ConcreteAdjacentGraded

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ThirdVertex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
local notation "s" => ConcreteQuadraticDiagram.quadratic P

def iota : D₂ ⟶ (vertexComplex P).obj (Exactness.P s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂).hom ≫
    (vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)

/-- The final-vertex map is the original e2 tensor insertion followed by the original total inclusion. -/
theorem iota_original : iota P D₀ D₁ D₂ f g H =
    (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂).hom ≫
      (vertexComplex P).map ((Exactness.data s D₀ D₁ D₂ f g).in₂) ≫
      (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H) := by
  dsimp only [iota]
  erw [← (vertexComplex P).map_comp (Exactness.i2 s D₀ D₁ D₂ f g)
    (Exactness.i1 s D₀ D₁ D₂ f g H),
    (Exactness.exact_source_filtration s D₀ D₁ D₂ f g H 0).2.2, Functor.map_comp]
  rfl
end LittleFinitistic.ThirdVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CanonicalArrowCompatibility
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace LittleFinitistic.CanonicalArrowCompatibility
open ExternalTensor.Section4 ExternalTensor.Section4.ArrowVertex
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- The homotopy uses exactly the original first and second vertex equivalences. -/
def compatibility01 (a : Fin (d+1)) : Homotopy
    (FirstVertex.iota P D₀ D₁ D₂ f g H ≫ arrow01Map P D₀ D₁ D₂ f g H a)
    (f a ≫ SecondVertex.iota P D₀ D₁ D₂ f g H) := by
  rw [FirstVertex.iota, SecondVertex.iota_original,
    diagonal_original, diagonal_original]
  exact NativeBridge.nativeCompatibility01 (ConcreteQuadraticDiagram.quadratic P)
    D₀ D₁ D₂ f g H ((ThreeVertexAlgebra.directedSystem (composition P)).idem 0)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1) a (arrow01_target P a)

set_option maxHeartbeats 0 in
/-- The homotopy uses exactly the original second and third vertex equivalences. -/
def compatibility12 (b : Fin (d+1)) : Homotopy
    (SecondVertex.iota P D₀ D₁ D₂ f g H ≫ arrow12Map P D₀ D₁ D₂ f g H b)
    (g b ≫ ThirdVertex.iota P D₀ D₁ D₂ f g H) := by
  rw [SecondVertex.iota_original, ThirdVertex.iota_original,
    diagonal_original, diagonal_original]
  exact NativeBridge.nativeCompatibility12 (ConcreteQuadraticDiagram.quadratic P)
    D₀ D₁ D₂ f g H ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2) b (arrow12_target P b)
end LittleFinitistic.CanonicalArrowCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFixedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.SelectedFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction

abbrev P := encoding.relations
end LittleFinitistic.SelectedFixedDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedRectification
open SelectedFixedDiagram ExternalTensor.Section4 RelationBasisCoefficients

abbrev F := (UnderlyingRepresentatives.forget P).mapHomologicalComplex (.up ℤ)
end LittleFinitistic.SelectedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTensorComparison
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

abbrev tensor (D : SourceVerdier.K P) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).obj
    (UnderlyingRepresentatives.complex P D)

end LittleFinitistic.SelectedTensorComparison

end

end OAI
end


