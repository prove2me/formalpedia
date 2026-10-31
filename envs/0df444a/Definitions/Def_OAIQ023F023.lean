-- Prove2me | Definitions.Def_OAIQ023F023
-- name    : OAIQ023F023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:30:26.323699+00:00
-- url     : https://prove2.me/theorems/744aaf3d-f3ef-4147-8785-a67bc7ed62e8
-- title:
--   Definitions bundle OAIQ023F023 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 175 declarations of OpenAI's Lean: 87 definitions, 1 inductive type or structure, 11 instances and 76 theorems. The definitions and types are `OAI.LittleFinitistic.BimoduleTotal.actualBarResolutionIso`, `OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation`, `OAI.LittleFinitistic.BimoduleTotal.fromNativeScalar`, `OAI.LittleFinitistic.BimoduleTotal.inputBimoduleIso`, `OAI.LittleFinitistic.BimoduleTotal.insertion`, `OAI.LittleFinitistic.BimoduleTotal.integerTotalFunctor`, `OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor`, `OAI.LittleFinitistic.BimoduleTotal.ofNonpositiveResolution`, `OAI.LittleFinitistic.BimoduleTotal.resolvedStalkIso`, `OAI.LittleFinitistic.BimoduleTotal.scalarEvaluationIso`, `OAI.LittleFinitistic.BimoduleTotal.scalarTensorIso`, `OAI.LittleFinitistic.BimoduleTotal.stalkChainIso`, `OAI.LittleFinitistic.BimoduleTotal.stalkTotalColumnIso`, `OAI.LittleFinitistic.BimoduleTotal.stalkTotalColumnNatIso`, `OAI.LittleFinitistic.BimoduleTotal.stalkTotalIso`, `OAI.LittleFinitistic.BimoduleTotal.toNativeScalar`, `OAI.LittleFinitistic.BimoduleTotal.zeroDegreeIndex`, `OAI.LittleFinitistic.BimoduleTotalPresentation.boundedNonpositiveTotalIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.enumerationIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.nonpositiveTotalFunctorIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.totalFunctorIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.totalIso`, `OAI.LittleFinitistic.EncodingGenerators.first`, `OAI.LittleFinitistic.EncodingGenerators.second`, `OAI.LittleFinitistic.EncodingLinearity.intertwining`, `OAI.LittleFinitistic.EncodingModuleAssembly.system`, `OAI.LittleFinitistic.FirstVertex.vertexComplex`, `OAI.LittleFinitistic.FullTensorRectification.source`, `OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftAction`, `OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensorVertexEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensorVertexSpaceEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalIso`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.directedSystem`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.leftMultiply`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.rightTerm`, `OAI.LittleFinitistic.OrdinarySimulation.VertexTensor`, `OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action`, `OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation`, `OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.mk` and 48 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleBarComparisonMap`, `Finitistic_Bimodule_BimoduleBarResolution`, `Finitistic_Bimodule_BimoduleBarStalk`, `Finitistic_Bimodule_BimoduleBoundedPresentation`, `Finitistic_Bimodule_BimoduleDerivedPresentation`, `Finitistic_Bimodule_BimoduleExactRows`, `Finitistic_Bimodule_BimoduleFiniteRowsAcyclic`, `Finitistic_Bimodule_BimoduleInputNaturality`, `Finitistic_Bimodule_BimoduleResolutionBarAPI`, `Finitistic_Bimodule_BimoduleScalarEvaluation`, `Finitistic_Bimodule_BimoduleShiftColumns`, `Finitistic_Bimodule_BimoduleShiftHorizontal`, `Finitistic_Bimodule_BimoduleShiftedPresentation`, `Finitistic_Bimodule_BimoduleSingleDifferential`, `Finitistic_Bimodule_BimoduleStalkTotal`, `Finitistic_Bimodule_BimoduleTotalCoefficient`, `Finitistic_Bimodule_BimoduleTotalInsertion`, `Finitistic_Bimodule_BimoduleTotalPresentation`, `Finitistic_Bimodule_BimoduleTotalShortExact`, `Finitistic_Encoding_EncodingGenerators`, `Finitistic_Encoding_EncodingLinearity`, `Finitistic_Encoding_EncodingModuleAssembly`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Encoding_RelationBasisAction`, `Finitistic_Encoding_RelationBasisCoefficients`, `Finitistic_Encoding_RelationMatrixSequence`, `Finitistic_Encoding_RelationPathCoordinates`, `Finitistic_Encoding_RelationSequence`, `Finitistic_Encoding_RelationVertexCoordinates`, `Finitistic_Encoding_RelationVertexSequence`, `Finitistic_Localization_SourceVerdier`, `Finitistic_Localization_TwoDegreeExtVanishing`, `Finitistic_Localization_TwoDegreeFormalityNaturality`, `Finitistic_Localization_TwoDegreeSplitting`, `Finitistic_Ordinary_OrdinaryBimodule`, `Finitistic_Ordinary_OrdinaryChainDirected`, `Finitistic_Ordinary_OrdinaryChainResolution`, `Finitistic_Ordinary_OrdinaryComplexAction`, `Finitistic_Ordinary_OrdinaryCompression`, `Finitistic_Ordinary_OrdinaryFirstBlockTotal`, `Finitistic_Ordinary_OrdinaryShiftDerivedTensor`, `Finitistic_Ordinary_OrdinarySimulationComparison`, `Finitistic_Ordinary_OrdinaryTensorBimoduleComparison`, `Finitistic_Ordinary_OrdinaryTensorVertex`, `Finitistic_Rectification_CanonicalArrowCompatibility`, `Finitistic_Rectification_FirstVertex`, `Finitistic_Rectification_FullTensorRectification`, `Finitistic_Rectification_InducedRectification`, `Finitistic_Rectification_SecondVertex`, `Finitistic_Rectification_TensorArrowComparison`, `Finitistic_Rectification_ThirdVertex`, `Finitistic_Rectification_ThirdVertexFiltration`, `Finitistic_Rectification_VertexCategoricalAssembly`, `Finitistic_Rectification_VertexHomotopyEquivalence`, `Finitistic_Rectification_VertexZeroTotal`.
--
--   **Imports.** It imports the bundles `OAIQ023F039`, `OAIQ023F018`, `OAIQ023F019` and `OAIQ023F020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F025`, `OAIQ023F026` and `OAIQ023F027`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F039
import Definitions.Def_OAIQ023F018
import Definitions.Def_OAIQ023F019
import Definitions.Def_OAIQ023F020

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.OrdinaryTerms.finiteDimensional _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

variable (P : Relations k d t)

theorem finiteDimensional : FiniteDimensional k (B P) := by
  have : FiniteDimensional k (Arrows k d) := inferInstance
  have : FiniteDimensional k (Paths k d) := inferInstance
  have : FiniteDimensional k (Paths k d ⧸ relationSpace P) := inferInstance
  exact inferInstanceAs (FiniteDimensional k
    (k × k × k × Arrows k d × Arrows k d × (Paths k d ⧸ relationSpace P)))

open CategoryTheory in
/-- Actual global dimensions of the constructed finite-dimensional encoding. -/
theorem globalDimension_le_two :
    (⨆ N : ModuleCat.{max u v} (B P), projectiveDimension N) ≤ (2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} (B P)ᵐᵒᵖ, projectiveDimension N) ≤ (2 : ℕ) :=
  ThreeVertexAlgebra.globalDimension_le_two (composition P)

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationSequence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.OrdinaryTerms.finiteDimensional _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.cyclicRing_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RelationSequence
open CategoryTheory CategoryTheory.Limits
open QuadraticEncoding

variable {k : Type*} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual length-two relation subspace, all paths, and their quotient. -/
noncomputable def sequence : ShortComplex (ModuleCat k) where
  X₁ := ModuleCat.of k (relationSpace P)
  X₂ := ModuleCat.of k (Paths k d)
  X₃ := ModuleCat.of k (Paths k d ⧸ relationSpace P)
  f := ModuleCat.ofHom
    { toFun := fun x => x.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  g := ModuleCat.ofHom
    { toFun := (relationSpace P).mkQ
      map_add' := (relationSpace P).mkQ.map_add
      map_smul' := (relationSpace P).mkQ.map_smul }
  zero := by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.property

/-- No additional relation appears: the path quotient sequence is genuinely exact. -/
theorem sequence_shortExact : (sequence P).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (relationSpace P).mkQ x = 0 ↔ ∃ y : relationSpace P, (y : Paths k d) = x
    constructor
    · intro hx
      exact ⟨⟨x,(Submodule.Quotient.mk_eq_zero _).1 hx⟩,rfl⟩
    · rintro ⟨y,hy⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 (hy ▸ y.property)
  · exact (relationSpace P).injective_subtype
  · exact (relationSpace P).mkQ_surjective

/-- The finite relation basis used by the manuscript exists for this exact subspace. -/
noncomputable def relationBasis : Module.Basis (Fin (Module.finrank k (relationSpace P))) k
    (relationSpace P) := by
  letI : Module.Free k (relationSpace P) := Module.Free.of_divisionRing k (relationSpace P)
  exact Module.finBasis k (relationSpace P)

end LittleFinitistic.RelationSequence

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisCoefficients
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisCoefficients
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- Coefficient of the path b a in a vector of the actual relation subspace. -/
def coefficient (r : relationSpace P) (a b : Fin (d+1)) : k :=
  (pathBasis (k := k) (d := d)).repr r.val (b,a)

theorem expansion (r : relationSpace P) :
    (∑ a, ∑ b, coefficient P r a b • (basis b ⊗ₜ[k] basis a)) = r.val := by
  rw [Finset.sum_comm]
  simpa only [coefficient,pathBasis,Fintype.sum_prod_type,
    Module.Basis.tensorProduct_apply,Pi.basisFun_apply,basis] using
    (pathBasis (k := k) (d := d)).sum_repr r.val

abbrev RelationIndex := Fin (Module.finrank k (relationSpace P))

def basisCoefficient (r : RelationIndex P) (a b : Fin (d+1)) : k :=
  coefficient P (RelationSequence.relationBasis P r) a b

end LittleFinitistic.RelationBasisCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationPathCoordinates
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationPathCoordinates
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The coefficient matrix of an actual relation, grouped by its first traversed arrow. -/
theorem relation_coordinate (r : relationSpace P) (a : Fin (d+1)) :
    coordinates (r : Paths k d) a = ∑ b, coefficient P r a b • basis b := by
  have h := congrArg (fun z : Paths k d => coordinates z a) (expansion P r)
  simpa [coordinates,TensorProduct.piScalarRightHom_tmul,Finset.sum_apply,
    basis,Pi.single_apply] using h.symm

/-- The actual independent relation basis has precisely the manuscript's q coefficients. -/
theorem basis_coordinate (r : RelationIndex P) (a : Fin (d+1)) :
    coordinates ((RelationSequence.relationBasis P r : relationSpace P) : Paths k d) a =
      ∑ b, basisCoefficient P r a b • basis b :=
  relation_coordinate P (RelationSequence.relationBasis P r) a
end LittleFinitistic.RelationPathCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationMatrixSequence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.RelationMatrixSequence
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev relationIso := FiniteBasisIso.iso (k := k) (V := relationSpace P) (RelationSequence.relationBasis P)

def inclusion := (relationIso P).hom ≫ (RelationSequence.sequence P).f ≫ (pathIso (k := k) (d := d)).inv

def quotient := (pathIso (k := k) (d := d)).hom ≫ (RelationSequence.sequence P).g

def sequence : ShortComplex (ModuleCat.{u} k) :=
  .mk (inclusion P) (quotient P)
    (transported_zero (relationIso P) pathIso _ _ (RelationSequence.sequence P).zero)

/-- The actual independent relation columns and first-arrow path columns are the canonical exact sequence. -/
def sequenceIso : sequence P ≅ RelationSequence.sequence P :=
  ShortComplex.isoMk (relationIso P) (pathIso (k := k) (d := d)) (Iso.refl _)
    (transported_comp_hom (relationIso P) pathIso _) (by simp [sequence,quotient]; rfl)

theorem shortExact : (sequence P).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (sequenceIso P)).2 (RelationSequence.sequence_shortExact P)

/-- The concrete matrix sequence splits over the base field. -/
def splitting : (sequence P).Splitting := (shortExact P).splittingOfProjective

/-- Each middle column maps by the original length-two path quotient. -/
theorem quotient_injection (a : Fin (d+1)) (w : Arrows k d) :
    (biproduct.ι (PathBasisIso.family k d) a ≫ quotient P).hom w =
      (relationSpace P).mkQ (w ⊗ₜ[k] basis a) := by
  change (relationSpace P).mkQ ((biproduct.ι (PathBasisIso.family k d) a ≫
    (PathBasisIso.iso k d).hom).hom w) = _
  rw [PathBasisIso.injection_apply]

/-- An independent relation column has exactly the source coefficient matrix. -/
theorem inclusion_coordinate (r : RelationIndex P) (a : Fin (d+1)) (c : k) :
    (biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
      inclusion P ≫ biproduct.π (PathBasisIso.family k d) a).hom c =
        c • ∑ b, basisCoefficient P r a b • basis b := by
  have hp : (pathIso (k := k) (d := d)).inv ≫ biproduct.π (PathBasisIso.family k d) a =
      ModuleCat.ofHom ((LinearMap.proj a).comp RelationPathCoordinates.coordinates.toLinearMap) := by
    simp only [pathIso,PathBasisIso.iso,Iso.trans_inv,Category.assoc,
      ModuleCat.biproductIsoPi_inv_comp_π]
    rfl
  simp only [inclusion, Category.assoc]
  erw [Category.assoc (RelationSequence.sequence P).f, hp]
  change RelationPathCoordinates.coordinates
    (((biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
      (relationIso P).hom).hom c : relationSpace P) : Paths k d) a = _
  rw [FiniteBasisIso.injection_apply]
  change RelationPathCoordinates.coordinates
    (c • ((RelationSequence.relationBasis P r : relationSpace P) : Paths k d)) a = _
  rw [map_smul]
  exact congrArg (c • ·) (RelationPathCoordinates.basis_coordinate P r a)
end LittleFinitistic.RelationMatrixSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_add _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_arrow _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_one _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_vertex _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k : Type u} [Field k] {l : ℕ}
namespace ChainAlgebra

@[simp] theorem arrow_mul (i : Fin l) (x : ChainAlgebra k l) :
    arrow k l i * x = x.1 i.castSucc • arrow k l i := by
  apply Prod.ext <;> funext j
  · change (0:k) * x.1 j = x.1 i.castSucc * 0
    simp
  · change 0 * x.2 j + (Pi.single i 1 : Fin l → k) j * x.1 j.castSucc =
      x.1 i.castSucc * (Pi.single i 1 : Fin l → k) j
    by_cases h : j = i <;> simp [h]

@[simp] theorem smul_diagonal (c : k) (x : ChainAlgebra k l) (i : Fin (l+1)) :
    (c • x).1 i = c * x.1 i := rfl
@[simp] theorem smul_radical (c : k) (x : ChainAlgebra k l) (i : Fin l) :
    (c • x).2 i = c * x.2 i := rfl
@[simp] theorem vertex_diagonal (i j : Fin (l+1)) :
    (vertex k l i).1 j = (Pi.single i 1 : Fin (l+1) → k) j := rfl
@[simp] theorem arrow_diagonal (i : Fin l) (j : Fin (l+1)) :
    (arrow k l i).1 j = 0 := rfl
@[simp] theorem arrow_radical (i j : Fin l) :
    (arrow k l i).2 j = (Pi.single i 1 : Fin l → k) j := rfl

/-- The two displayed coordinates of each noninitial right projective. -/
theorem vertex_succ_mul (i : Fin l) (x : ChainAlgebra k l) :
    vertex k l i.succ * x = x.1 i.succ • vertex k l i.succ + x.2 i • arrow k l i := by
  rw [add_eq, smul_eq, smul_eq]
  apply Prod.ext <;> funext j
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j * x.1 j =
      x.1 i.succ * (Pi.single i.succ 1 : Fin (l+1) → k) j + x.2 i * 0
    by_cases h : j = i.succ <;> simp [h]
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j.succ * x.2 j + 0 * x.1 j.castSucc =
      x.1 i.succ * 0 + x.2 i * (Pi.single i 1 : Fin l → k) j
    by_cases h : j = i
    · subst j; simp
    · have hs : j.succ ≠ i.succ := fun e => h (Fin.succ_injective _ e)
      simp [h, hs]

/-- The initial projective has no radical coordinate. -/
theorem vertex_zero_mul (x : ChainAlgebra k l) :
    vertex k l 0 * x = x.1 0 • vertex k l 0 := by
  rw [smul_eq]
  apply Prod.ext <;> funext j
  · change (Pi.single 0 1 : Fin (l+1) → k) j * x.1 j =
      x.1 0 * (Pi.single 0 1 : Fin (l+1) → k) j
    by_cases h : j = 0 <;> simp [h]
  · change (Pi.single 0 1 : Fin (l+1) → k) j.succ * x.2 j + 0 * x.1 j.castSucc = x.1 0 * 0
    simp

/-- Actual right projectives in the source resolution. -/
abbrev rightTerm (i : Fin (l+1)) := IdempotentTensor.rightIdeal (vertex k l i)

def leftMultiply (x : ChainAlgebra k l) : ChainAlgebra k l →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] ChainAlgebra k l where
  toFun y := x*y
  map_add' := mul_add x
  map_smul' r y := (mul_assoc x y r.unop).symm

/-- The differential is actual left multiplication by the source arrow. -/
def resolutionMap (i : Fin l) : rightTerm (k := k) i.castSucc →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] rightTerm (k := k) i.succ :=
  ((leftMultiply (arrow k l i)).comp (rightTerm (k := k) i.castSucc).subtype).codRestrict _ (fun x => by
    change vertex k l i.succ * (arrow k l i * x.val) = arrow k l i * x.val
    rw [← mul_assoc, vertex_target_arrow])

@[simp] theorem resolutionMap_value (i : Fin l) (x : rightTerm (k := k) i.castSucc) :
    (resolutionMap (k := k) i x).val = x.val.1 i.castSucc • arrow k l i := arrow_mul i x.val

/-- This is the explicit two-coordinate expansion, not a dimension argument. -/
theorem rightTerm_succ_expansion (i : Fin l) (x : rightTerm (k := k) i.succ) :
    x.val = x.val.1 i.succ • vertex k l i.succ + x.val.2 i • arrow k l i := by
  rw [← vertex_succ_mul]
  exact x.property.symm

theorem resolutionMap_zero_iff (i : Fin l) (x : rightTerm (k := k) i.castSucc) :
    resolutionMap (k := k) i x = 0 ↔ x.val.1 i.castSucc = 0 := by
  constructor
  · intro h
    have hr := congrArg (fun y : rightTerm (k := k) i.succ => y.val.2 i) h
    rw [resolutionMap_value, smul_radical, arrow_radical] at hr
    simpa using hr
  · intro h
    apply Subtype.ext
    rw [resolutionMap_value, h, zero_smul]
    rfl

/-- Exact description of the image: the one-dimensional radical in the next term. -/
theorem resolutionMap_range (i : Fin l) (x : rightTerm (k := k) i.succ) :
    (∃ y, resolutionMap (k := k) i y = x) ↔ x.val.1 i.succ = 0 := by
  constructor
  · rintro ⟨y,rfl⟩
    rw [resolutionMap_value, smul_diagonal, arrow_diagonal, mul_zero]
  · intro hx
    let y : rightTerm (k := k) i.castSucc := ⟨x.val.2 i • vertex k l i.castSucc, by
      change vertex k l i.castSucc * (x.val.2 i • vertex k l i.castSucc) =
        x.val.2 i • vertex k l i.castSucc
      rw [mul_smul_comm, vertex_idempotent]⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [resolutionMap_value]
    have hy : y.val.1 i.castSucc = x.val.2 i := by
      dsimp [y]
      simp
    rw [hy]
    have he := rightTerm_succ_expansion i x
    rw [hx, zero_smul, zero_add] at he
    exact he.symm

/-- Injectivity of the first nonzero differential in the resolution. -/
theorem resolution_first_injective (hl : 0 < l) :
    Function.Injective (resolutionMap (k := k) (⟨0,hl⟩ : Fin l)) := by
  intro x y hxy
  have hx : resolutionMap (k := k) (⟨0,hl⟩ : Fin l) (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hz := (resolutionMap_zero_iff _ (x-y)).mp hx
  have he := vertex_zero_mul (x-y).val
  have hp : vertex k l 0 * (x-y).val = (x-y).val := (x-y).property
  change (x-y).val.1 0 = 0 at hz
  rw [hp, hz, zero_smul] at he
  have hsub : x-y = 0 := Subtype.ext he
  exact sub_eq_zero.mp hsub
end ChainAlgebra
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap_value _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_diagonal _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k : Type u} [Field k] {l : ℕ}

namespace OrdinaryTerms
variable (V : Fin (l+1) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (d : ∀ i j, V i →ₗ[k] V j)

variable (dd : ∀ i j h, (d j h).comp (d i j) = 0)

/-- The constructed action retains the given k-vector-space structure. -/
theorem scalarTower : letI := module V d dd; IsScalarTower k (ChainAlgebra k l) (OrdinaryTerms V) := by
  let := module V d dd
  refine ⟨?_⟩
  intro c x v
  change action V d (c • x) v = c • action V d x v
  funext i
  have hc (i j : Fin (l+1)) :
      ChainAlgebra.coefficient (c • x) i j = c * ChainAlgebra.coefficient x i j := by
    unfold ChainAlgebra.coefficient
    split <;> simp [ChainAlgebra.smul_eq]
  simp only [action, hc]
  simp only [ChainAlgebra.smul_eq, Pi.smul_apply, action,
    smul_eq_mul, mul_smul, smul_add, Finset.smul_sum]
end OrdinaryTerms
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryCompression
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.finiteDimensional _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

namespace Compression
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)
instance instIsScalarTowerChainAlgebra : IsScalarTower k (ChainAlgebra k l) (Compression P a l) :=
  OrdinaryTerms.scalarTower _ _ (intervalDifferential_square (underlyingComplex (k := k) P) a l)

end Compression
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimodule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

namespace BimoduleO
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
instance instIsScalarTowerChainAlgebra : IsScalarTower k (ChainAlgebra k l) (BimoduleO P a l) :=
  inferInstanceAs (IsScalarTower k (ChainAlgebra k l) (Compression P a l))

/-- The left B tensor C action takes values in actual right-B-linear maps. -/
def leftAction : (B ⊗[k] ChainAlgebra k l) →ₐ[k] Module.End Bᵐᵒᵖ (BimoduleO P a l) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k Bᵐᵒᵖ (BimoduleO P a l))
    (Algebra.lsmul k Bᵐᵒᵖ (BimoduleO P a l)) (by
      intro b x
      ext v
      exact (smul_comm x b v).symm)

instance leftModule : Module (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
  Module.compHom (BimoduleO P a l) (leftAction P a l).toRingHom

instance towerTensor : IsScalarTower k (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) where
  smul_assoc c x v := by
    change leftAction P a l (c • x) v = c • leftAction P a l x v
    rw [map_smul]
    rfl

instance commuteTensorRight : SMulCommClass (B ⊗[k] ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm x b v := (leftAction P a l x).map_smul b v

end BimoduleO
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleInputNaturality
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The canonical maps in the two tensor variables commute, preserving the full outside action. -/
theorem input_tensor_square {M M' : ModuleCat.{u} (Enveloping k B)}
    {N N' : ModuleCat.{u} B} (f : M ⟶ M') (g : N ⟶ N') :
    (inputFunctor k B M).map g ≫
      (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N')).map f =
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map f ≫
      (inputFunctor k B M').map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)

/-- On the unique nonzero summands, the total differential becomes the original native tensor differential. -/
theorem single_horizontal (n m : ℤ) (h : n+1=m) :
    ModuleCat.ofHom (horizontalBetween k B P (singleInput B N) n m n m h h) ≫
      (singleTermIso k B P N m m rfl).hom =
    (singleTermIso k B P N n n rfl).hom ≫ (moduleEvaluation k B P N).d n m := by
  let φn := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (n + -n) (by omega)).hom
  let φm := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (m + -m) (by omega)).hom
  let e := eqToHom (congrArg (singleInput B N).X (show n + -n = m + -m by omega))
  have he : e ≫ φm = φn := by
    simp only [e,φn,φm,HomologicalComplex.singleObjXIsoOfEq,eqToIso.hom,eqToHom_trans]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht a b =>
    change BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
        (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) (φm.hom (e.hom b)) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
        (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) (φn.hom b)
    exact congrArg (fun t => BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
      (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) t)
      (congrArg (fun f => f.hom b) he)
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem single_total_d (i j : Fin l) (h : p i+1=p j)
    (x : TotalTerm k B P p (singleInput B N) (p i)) :
    ((total k B P p hp (singleInput B N)).d (p i) (p j)).hom x j =
      horizontalBetween k B P (singleInput B N) (p i) (p j) (p i) (p j) h h (x i) := by
  rw [total_d_apply k B P (singleInput B N) p hp (p i) (p j) h]
  have hv : ((ComplexTensor.column k B (right k B P) (singleInput B N) (p j)).d (p i) (p j)).hom (x j) = 0 := by
    rw [ComplexTensor.column_d]
    simp only [singleInput,HomologicalComplex.single_obj_d,ComplexTensor.map_zero_right,
       smul_zero]
    rfl
  erw [hv,zero_add]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [entryBetween,dite_eq_left h]
  · intro t _ ht
    let := ModuleCat.subsingleton_of_isZero
      (singleTerm_isZero k B P N (p i) (p t) (fun he => ht (hp.injective he)))
    have hx : x t=0 := Subsingleton.elim _ _
    rw [hx,map_zero]
  · simp

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.InducedRectification
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

theorem total_bounded (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo-2 ∨ hi < n → IsZero ((total s D₀ D₁ D₂ f g H).X n) := by
  have hc := columns_bounded s D₀ D₁ D₂ f g lo hi h₀ h₁ h₂
  exact RectificationTotal.total_bounded _ _ _ lo hi
    (fun n hn => (hc n hn).1) (fun n hn => (hc n hn).2.1)
    (fun n hn => (hc n hn).2.2)

end LittleFinitistic.InducedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarResolution
attribute [-instance] _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} (data : BoundedProjective k B P)

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions
abbrev integerTotalFunctor := DerivedBar.integerExtension B ⋙
  functor k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ⋙ DerivedCategory.Q

/-- The original bar augmentation, followed by the fixed finite bimodule total. -/
def barInputAugmentation : DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data ⟶
    integerTotalFunctor data :=
  Functor.whiskerRight (DerivedBar.barTotalAugmentationNat k B) (integerTotalFunctor data)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftColumns
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The B-valued column has exactly the frozen signed differential on underlying elements. -/
theorem fullColumn_d (p n m : ℤ) (x : Term k B P Z p (n + -p)) :
    (((columnFunctor k B P p).obj Z).d n m).hom x =
      ((ComplexTensor.column k B (right k B P) Z p).d n m).hom x := by
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht a b => rfl
  | ha a b ha hb =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ _ _).symm)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleStalkTotal
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (X : ModuleCat.{u} (Enveloping k B))
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (hi₀ : p i₀=0)

include hp hi₀ in
/-- Every off-zero column of the stalk bimodule total is actually zero. -/
theorem stalkTerm_isZero (Z : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ)
    (i : Fin l) (hi : i ≠ i₀) :
    IsZero (ModuleCat.of B (Term k B (bimoduleStalk k B X) Z (p i) (n + -(p i)))) := by
  have hpi : p i ≠ 0 := fun h => hi (hp.injective (h.trans hi₀.symm))
  exact (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (p i) hpi)

/-- Projecting onto its sole nonzero column is a genuine B-linear chain isomorphism. -/
def stalkTotalColumnIso (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    total k B (bimoduleStalk k B X) p hp Z ≅
      (columnFunctor k B (bimoduleStalk k B X) (p i₀)).obj Z :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (piSingleEquiv (fun i => Term k B (bimoduleStalk k B X) Z (p i) (n + -(p i)))
      i₀ (fun i hi => ModuleCat.subsingleton_of_isZero
        (stalkTerm_isZero k B X p hp i₀ hi₀ Z n i hi))).toModuleIso)
    (by
      intro n m h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (((columnFunctor k B (bimoduleStalk k B X) (p i₀)).obj Z).d n m).hom (x i₀) =
        ((total k B (bimoduleStalk k B X) p hp Z).d n m).hom x i₀
      erw [fullColumn_d,total_d_apply k B (bimoduleStalk k B X) Z p hp n m h]
      have hd (a b : ℤ) : (bimoduleStalk k B X).d a b = 0 := by
        simp [bimoduleStalk]
      have he (i : Fin l) : entryBetween k B (bimoduleStalk k B X) Z n m (p i) (p i₀) h = 0 := by
        unfold entryBetween horizontalBetween
        split_ifs
        · rw [hd,← tensorAcross_eq_termMap,tensorAcross_zero_left]
        · rfl
      simp only [he,LinearMap.zero_apply,Finset.sum_const_zero]
      exact (add_zero _).symm)

/-- The stalk-total comparison is natural in the entire input complex. -/
def stalkTotalColumnNatIso : functor k B (bimoduleStalk k B X) p hp ≅
    columnFunctor k B (bimoduleStalk k B X) (p i₀) :=
  NatIso.ofComponents (stalkTotalColumnIso k B X p hp i₀ hi₀) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((ComplexTensor.finiteTotalMap k B (right k B (bimoduleStalk k B X)) p hp f).f n).hom x i₀ = _
    erw [ComplexTensor.finiteTotalMap_apply]
    change ComplexTensor.inputMap k B (right k B (bimoduleStalk k B X)) f
      (p i₀) (n + -(p i₀)) (x i₀) =
        inputModuleMap k B ((bimoduleStalk k B X).X (p i₀)) (f.f (n + -(p i₀))) (x i₀)
    induction x i₀ using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simpa only [map_add] using congrArg₂ HAdd.hAdd hx hy)

/-- An actual bimodule isomorphism induces a natural isomorphism of input tensor functors. -/
def inputBimoduleIso {M M' : ModuleCat.{u} (Enveloping k B)} (e : M ≅ M') :
    inputFunctor k B M ≅ inputFunctor k B M' :=
  NatIso.ofComponents (fun N =>
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapIso e)
    (by intro N N' f; exact input_tensor_square k B e.hom f)

/-- Finite total with the stalk bimodule is the ordinary tensor functor on all
integer complexes. The only indexing condition is that degree zero is included. -/
def stalkTotalIso : functor k B (bimoduleStalk k B X) p hp ≅
    (inputFunctor k B X).mapHomologicalComplex (.up ℤ) := by
  refine stalkTotalColumnNatIso k B X p hp i₀ hi₀ ≪≫ ?_
  rw [hi₀]
  exact Functor.isoWhiskerLeft
      ((inputFunctor k B ((bimoduleStalk k B X).X 0)).mapHomologicalComplex (.up ℤ))
      (shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ) ≪≫
    Functor.rightUnitor _ ≪≫
    NatIso.mapHomologicalComplex
      (inputBimoduleIso k B (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 X 0 rfl)) (.up ℤ)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonMap
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)
variable (i₀ : Fin ((res.data.upper-res.data.lower).toNat+1)) (hi₀ : res.data.degrees i₀=0)

/-- The stalk total on extended chains agrees with the exact tensor functor used by DerivedBar. -/
def stalkChainIso : DerivedBar.integerExtension B ⋙
    functor k B (bimoduleStalk k B X) res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) ≅
    (actualBarFunctor (X := X)).mapHomologicalComplex (.down ℕ) ⋙ DerivedBar.integerExtension B :=
  isoWhiskerLeft (DerivedBar.integerExtension B)
    (stalkTotalIso k B X res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) i₀ hi₀) ≪≫
  isoWhiskerLeft (DerivedBar.integerExtension B)
    (NatIso.mapHomologicalComplex (BimoduleBarComparison.tensorFunctorIso k B X) (.up ℤ)) ≪≫
  IntegerExtensionFunctor.naturalIso (actualBarFunctor (X := X))

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_1
def resolvedStalkIso :
    DerivedBar.barTotalFunctor k B ⋙ DerivedBar.integerExtension B ⋙
      functor k B (bimoduleStalk k B X) res.data.degrees
        (intervalDegrees_strictMono res.data.lower res.data.upper) ⋙ DerivedCategory.Q ≅
    DerivedBar.tensorTotalFunctor k B (barModule (X := X)) ⋙ DerivedBar.integerQ B :=
  isoWhiskerLeft (DerivedBar.barTotalFunctor k B)
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (stalkChainIso res i₀ hi₀) DerivedCategory.Q ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The native bar functor's defining localization comparisons, with integer extension. -/
def actualBarResolutionIso :
    DerivedBar.chainQ B ⋙
      (DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B) ≅
    DerivedBar.tensorTotalFunctor k B (barModule (X := X)) ⋙ DerivedBar.integerQ B :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedBar.derivedTensorResolutionIso k B (barModule (X := X)))
      (DerivedBar.chainToIntegerDerived B) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (DerivedBar.tensorTotalFunctor k B (barModule (X := X)))
      (DerivedBar.chainToIntegerDerivedIso B)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleExactRows
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The cross-variable tensor map with an identity input is the original bimodule map. -/
theorem tensorAcross_right_id {M M' : ModuleCat.{u} (Enveloping k B)}
    (f : M ⟶ M') (N : ModuleCat.{u} B) :
    tensorAcross f (𝟙 N) = BimoduleBalancedTensor.map k B (BalancedTensor.ScalarLeftModule k B N) f := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable (k B) (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable (hP : P.Acyclic) [∀ q, Projective (Z.X q)]

include hP in
/-- Every row of an acyclic bimodule complex tensored with a projective input term is exact. -/
theorem row_exact (a q : ℤ) :
    Function.Exact (tensorAcross (P.d (a-1) a) (𝟙 (Z.X q)))
      (tensorAcross (P.d a (a+1)) (𝟙 (Z.X q))) := by
  let : Module.Projective B (BalancedTensor.ScalarLeftModule k B (Z.X q)) :=
    inferInstanceAs (Module.Projective B (Z.X q))
  let S := ShortComplex.mk (P.d (a-1) a) (P.d a (a+1)) (P.d_comp_d (a-1) a (a+1))
  have hs : S.Exact :=
    (HomologicalComplex.exactAt_iff' P (a-1) a (a+1) (by simp) (by simp)).mp (hP a)
  have ht := BimoduleBalancedTensor.projectiveInput_mapsExact k B
    (BalancedTensor.ScalarLeftModule k B (Z.X q)) S hs
  rw [tensorAcross_right_id,tensorAcross_right_id]
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp ht

include hP in
/-- The row exactness statement with precisely the transports occurring in the signed total. -/
theorem horizontal_exact (n a : ℤ) :
    Function.Exact
      (horizontalBetween k B P Z (n-1) n (a-1) a (by omega) (by omega))
      (horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl) := by
  have ht := row_exact k B P Z hP a (n + -a)
  have transport (q₀ q₂ : ℤ) (h₀ : q₀ = n + -a) (h₂ : n + -a = q₂) :
      Function.Exact
        (tensorAcross (P.d (a-1) a) (eqToHom (congrArg Z.X h₀)))
        (tensorAcross (P.d a (a+1)) (eqToHom (congrArg Z.X h₂))) := by
    subst q₀ q₂
    exact ht
  unfold horizontalBetween
  rw [← tensorAcross_eq_termMap,← tensorAcross_eq_termMap]
  exact transport ((n-1) + -(a-1)) ((n+1) + -(a+1)) (by omega) (by omega)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalCoefficient
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

include hp in
@[simp] theorem coefficient_at (n : ℤ) (i : Fin l) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p n (p i) x = x i :=
  FiniteSupportReindex.coefficient_at
    (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) p hp.injective i x

theorem coefficient_outside (n a : ℤ) (ha : ∀ i, p i ≠ a) : coefficient k B P Z p n a = 0 :=
  FiniteSupportReindex.coefficient_outside _ p a ha

theorem term_left_isZero (a q : ℤ) (ha : IsZero (P.X a)) :
    IsZero (ModuleCat.of B (Term k B P Z a q)) :=
  (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z q)).map_isZero ha

variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))

include hP in
/-- The original total differential, read in any integer left degree, including
zero degrees outside the chosen finite support. -/
theorem coefficient_d_sum (n a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p (n+1) a (((total k B P p hp Z).d n (n+1)).hom x) =
      (show Term k B P Z a ((n+1) + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n (n+1)).hom
          (coefficient k B P Z p n a x)) +
      ∑ i : Fin l, entryBetween k B P Z n (n+1) (p i) a rfl (x i) := by
  classical
  by_cases ha : ∃ i, p i=a
  · obtain ⟨i,rfl⟩ := ha
    erw [coefficient_at k B P Z p hp,coefficient_at k B P Z p hp]
    exact total_d_apply k B P Z p hp n (n+1) rfl x i
  · let := ModuleCat.subsingleton_of_isZero
      (term_left_isZero k B P Z a ((n+1) + -a) (hP a (by simpa only [not_exists] using ha)))
    exact Subsingleton.elim _ _

include hp in
/-- The horizontal sum has at most its immediately preceding left-degree component. -/
theorem horizontal_sum_predecessor (n a : ℤ) (x : TotalTerm k B P p Z n) :
    (∑ i : Fin l, entryBetween k B P Z n (n+1) (p i) a rfl (x i)) =
      horizontalBetween k B P Z n (n+1) (a-1) a rfl (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  classical
  by_cases ha : ∃ i, p i=a-1
  · obtain ⟨i,hi⟩ := ha
    rw [Finset.sum_eq_single i]
    · have transfer (b : ℤ) (hb : b=p i) (hba : b+1=a) :
          horizontalBetween k B P Z n (n+1) b a rfl hba
            (coefficient k B P Z p n b x) =
          entryBetween k B P Z n (n+1) (p i) a rfl (x i) := by
        subst b
        rw [coefficient_at k B P Z p hp]
        unfold entryBetween
        rw [dite_eq_left hba]
      exact (transfer (a-1) hi.symm (by omega)).symm
    · intro j _ hji
      unfold entryBetween
      rw [dite_eq_right (fun h => hji (hp.injective (by omega)))]
      rfl
    · simp
  · have ha' : ∀ i, p i ≠ a-1 := by simpa only [not_exists] using ha
    rw [coefficient_outside k B P Z p n (a-1) ha',LinearMap.zero_apply,map_zero]
    apply Finset.sum_eq_zero
    intro i _
    unfold entryBetween
    rw [dite_eq_right (fun h => ha' i (by omega))]
    rfl

include hP in
/-- The complete finite tensor differential consists of its signed vertical term
and its immediately preceding horizontal term. -/
theorem coefficient_d (n a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p (n+1) a (((total k B P p hp Z).d n (n+1)).hom x) =
      (show Term k B P Z a ((n+1) + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n (n+1)).hom
          (coefficient k B P Z p n a x)) +
      horizontalBetween k B P Z n (n+1) (a-1) a rfl (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  rw [coefficient_d_sum k B P Z p hp hP,horizontal_sum_predecessor k B P Z p hp]
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalInsertion
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Insert one actual left-degree component into the finite total. -/
def insertion (n a : ℤ) : Term k B P Z a (n + -a) →ₗ[B] TotalTerm k B P p Z n := by
  classical
  exact LinearMap.pi (fun i => if h : p i=a then
    (eqToHom (congrArg (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) h.symm)).hom else 0)

@[simp] theorem insertion_same (n : ℤ) (i : Fin l) (y : Term k B P Z (p i) (n + -(p i))) :
    insertion k B P Z p n (p i) y i = y := by
  classical
  simp [insertion]

theorem insertion_other (n a : ℤ) (i : Fin l) (h : p i ≠ a) (y : Term k B P Z a (n + -a)) :
    insertion k B P Z p n a y i = 0 := by
  classical
  simp only [insertion,LinearMap.pi_apply,dite_eq_right h,LinearMap.zero_apply]

include hp in
theorem coefficient_insertion_other (n a b : ℤ) (h : b ≠ a) (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p n b (insertion k B P Z p n a y) = 0 := by
  classical
  by_cases hb : ∃ i, p i=b
  · obtain ⟨i,rfl⟩ := hb
    rw [coefficient_at k B P Z p hp]
    exact insertion_other k B P Z p n a i h y
  · rw [coefficient_outside k B P Z p n b (by simpa only [not_exists] using hb),LinearMap.zero_apply]

variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))

include hp hP in
theorem coefficient_insertion_self (n a : ℤ) (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p n a (insertion k B P Z p n a y) = y := by
  classical
  by_cases ha : ∃ i, p i=a
  · obtain ⟨i,rfl⟩ := ha
    rw [coefficient_at k B P Z p hp,insertion_same]
  · let := ModuleCat.subsingleton_of_isZero
      (term_left_isZero k B P Z a (n + -a) (hP a (by simpa only [not_exists] using ha)))
    exact Subsingleton.elim _ _

include hP in
theorem coefficient_d_between (n m : ℤ) (h : n+1=m) (a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p m a (((total k B P p hp Z).d n m).hom x) =
      (show Term k B P Z a (m + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n m).hom
          (coefficient k B P Z p n a x)) +
      horizontalBetween k B P Z n m (a-1) a h (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  subst m
  exact coefficient_d k B P Z p hp hP n a x

include hP in
/-- A correction inserted in degree a cannot affect total coordinates above a+1. -/
theorem coefficient_d_insertion_above (n m : ℤ) (h : n+1=m) (a b : ℤ) (hab : a+1<b)
    (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p m b
      (((total k B P p hp Z).d n m).hom (insertion k B P Z p n a y)) = 0 := by
  rw [coefficient_d_between k B P Z p hp hP n m h b]
  rw [coefficient_insertion_other k B P Z p hp n a b (by omega),
    coefficient_insertion_other k B P Z p hp n a (b-1) (by omega)]
  erw [map_zero, add_zero]
  rfl

include hP in
/-- The next coordinate of the inserted correction is exactly its horizontal differential. -/
theorem coefficient_d_insertion_next (n m : ℤ) (h : n+1=m) (a b : ℤ) (hab : a+1=b)
    (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p m b
      (((total k B P p hp Z).d n m).hom (insertion k B P Z p n a y)) =
      horizontalBetween k B P Z n m a b h hab y := by
  rw [coefficient_d_between k B P Z p hp hP n m h b]
  erw [coefficient_insertion_other k B P Z p hp n a b (by omega),map_zero,zero_add]
  have transfer (c : ℤ) (hc : c=a) (hcb : c+1=b) :
      horizontalBetween k B P Z n m c b h hcb
        (coefficient k B P Z p n c (insertion k B P Z p n a y)) =
      horizontalBetween k B P Z n m a b h hab y := by
    subst c
    rw [coefficient_insertion_self k B P Z p hp hP]
  exact transfer (b-1) (by omega) (by omega)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleFiniteRowsAcyclic
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))
variable (hacyc : P.Acyclic) [∀ q, Projective (Z.X q)]

include hP in
omit [∀ q, Projective (Z.X q)] in
/-- A closed total element whose higher coordinates vanish is closed in the next row. -/
theorem closed_horizontal (n a : ℤ) (x : TotalTerm k B P p Z n)
    (hx : ((total k B P p hp Z).d n (n+1)).hom x = 0)
    (hhigh : coefficient k B P Z p n (a+1) x = 0) :
    horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl
      (coefficient k B P Z p n a x) = 0 := by
  have hc := congrArg (coefficient k B P Z p (n+1) (a+1)) hx
  erw [coefficient_d k B P Z p hp hP,hhigh,map_zero,zero_add,map_zero] at hc
  have transfer (b : ℤ) (hb : b=a) (hba : b+1=a+1) :
      horizontalBetween k B P Z n (n+1) b (a+1) rfl hba
        (coefficient k B P Z p n b x) =
      horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl
        (coefficient k B P Z p n a x) := by
    subst b
    rfl
  rw [transfer (a+1-1) (by omega) (by omega)] at hc
  exact hc

include hP hacyc in
/-- Row-by-row elimination gives an actual preimage for every closed finite-total element. -/
theorem total_exact_of_rows (lo hi n : ℤ) (hlo : ∀ i, lo ≤ p i) (hhi : ∀ i, p i ≤ hi) :
    Function.Exact ((total k B P p hp Z).d (n-1) n).hom
      ((total k B P p hp Z).d n (n+1)).hom := by
  intro z
  constructor
  · intro hz
    let d := ((total k B P p hp Z).d (n-1) n).hom
    let e := ((total k B P p hp Z).d n (n+1)).hom
    have ed (w : TotalTerm k B P p Z (n-1)) : e (d w) = 0 :=
      congrArg (fun f => f.hom w) ((total k B P p hp Z).d_comp_d (n-1) n (n+1))
    have step (j : ℕ) : ∃ w : TotalTerm k B P p Z (n-1),
        ∀ b : ℤ, hi+1-(j : ℤ) ≤ b → coefficient k B P Z p n b (z-d w) = 0 := by
      induction j with
      | zero =>
        refine ⟨0, ?_⟩
        intro b hb
        erw [map_zero,sub_zero,coefficient_outside k B P Z p n b (by
          intro i heq
          have := hhi i
          omega),LinearMap.zero_apply]
      | succ j ih =>
        obtain ⟨w,hw⟩ := ih
        let a : ℤ := hi-(j : ℤ)
        let x := z-d w
        have hx : e x = 0 := by
          dsimp [x]
          rw [map_sub,hz,ed,sub_self]
        have hxhigh : coefficient k B P Z p n (a+1) x = 0 := hw (a+1) (by dsimp [a]; omega)
        have hc := closed_horizontal k B P Z p hp hP n a x hx hxhigh
        obtain ⟨y,hy⟩ := (horizontal_exact k B P Z hacyc n a _).mp hc
        let v := insertion k B P Z p (n-1) (a-1) y
        have hv : coefficient k B P Z p n a (d v) = coefficient k B P Z p n a x := by
          exact (coefficient_d_insertion_next k B P Z p hp hP (n-1) n (by omega)
            (a-1) a (by omega) y).trans hy
        refine ⟨w+v, ?_⟩
        intro b hb
        have hba : a ≤ b := by dsimp [a] at *; omega
        have hr : coefficient k B P Z p n b (z-d (w+v)) =
            coefficient k B P Z p n b x - coefficient k B P Z p n b (d v) := by
          dsimp [x]
          erw [map_add,map_sub,map_sub,map_add]
          abel
        rw [hr]
        by_cases hbeq : b=a
        · subst b
          rw [hv,sub_self]
        · have hbgt : a < b := lt_of_le_of_ne hba (Ne.symm hbeq)
          have hx0 := hw b (by dsimp [a] at *; omega)
          have hv0 : coefficient k B P Z p n b (d v) = 0 :=
            coefficient_d_insertion_above k B P Z p hp hP (n-1) n (by omega) (a-1) b (by omega) y
          rw [hx0,hv0,sub_self]
    obtain ⟨w,hw⟩ := step ((hi-lo).toNat+1)
    refine ⟨w, ?_⟩
    funext i
    have hwi := hw (p i) (by have := hlo i; omega)
    erw [coefficient_at k B P Z p hp] at hwi
    exact (sub_eq_zero.mp hwi).symm
  · rintro ⟨w,rfl⟩
    exact congrArg (fun f => f.hom w) ((total k B P p hp Z).d_comp_d (n-1) n (n+1))

include hP hacyc in
/-- A bounded acyclic bimodule complex tensors to an acyclic finite total with
any complex of projective left modules. The full outside B-action is retained. -/
theorem total_acyclic_of_rows (lo hi : ℤ) (hlo : ∀ i, lo ≤ p i) (hhi : ∀ i, p i ≤ hi) :
    (total k B P p hp Z).Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp)).mpr
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (total_exact_of_rows k B P Z p hp hP hacyc lo hi n hlo hhi)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalShortExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ) [∀ q, Projective (Z.X q)]
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Fixed-input finite tensor total as an actual functor on bimodule complexes. -/
def leftTotalFunctor : BiComplex k B ⥤ CochainComplex (ModuleCat.{u} B) ℤ where
  obj P := total k B P p hp Z
  map f := leftTotalMap f Z p hp
  map_id _ := leftTotalMap_id p hp Z
  map_comp f g := leftTotalMap_comp p hp f g Z

instance leftTotalFunctor_preservesZeroMorphisms : (leftTotalFunctor k B Z p hp).PreservesZeroMorphisms where
  map_zero := by
    intros P P'
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change tensorAcross (0 : P.X (p i) ⟶ P'.X (p i)) (𝟙 (Z.X (n + -(p i)))) (x i) = 0
    rw [tensorAcross_zero_left,LinearMap.zero_apply]

/-- Short exact sequences of bimodules remain short exact after the finite total
on an input complex of projective left modules. -/
theorem leftTotal_shortExact (S : ShortComplex (BiComplex k B)) (hS : S.ShortExact) :
    (S.map (leftTotalFunctor k B Z p hp)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hs (i : Fin l) :
      ((S.map (HomologicalComplex.eval _ (.up ℤ) (p i))).map
        (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i))))).ShortExact := by
    let : Module.Projective B (ComplexTensor.leftTerm k B Z (n + -(p i))) :=
      inferInstanceAs (Module.Projective B (Z.X (n + -(p i))))
    let := BimoduleBalancedTensor.projectiveInput_preservesHomology k B
      (ComplexTensor.leftTerm k B Z (n + -(p i)))
    let F := BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))
    let := Functor.preservesMonomorphisms_of_map_exact F
      (BimoduleBalancedTensor.projectiveInput_mapsExact k B _)
    let := Functor.preservesEpimorphisms_of_map_exact F
      (BimoduleBalancedTensor.projectiveInput_mapsExact k B _)
    have hSe := hS.map (HomologicalComplex.eval _ (.up ℤ) (p i))
    let := hSe.mono_f
    let := hSe.epi_g
    exact hSe.map F
  have hf (i : Fin l) : Function.Injective
      (leftTermMap S.f Z (p i) (n + -(p i))) := by
    have := (hs i).mono_f
    rw [leftTermMap,tensorAcross_right_id]
    exact (ModuleCat.mono_iff_injective
      ((BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map (S.f.f (p i)))).mp (hs i).mono_f
  have hg (i : Fin l) : Function.Surjective
      (leftTermMap S.g Z (p i) (n + -(p i))) := by
    have := (hs i).epi_g
    rw [leftTermMap,tensorAcross_right_id]
    exact (ModuleCat.epi_iff_surjective
      ((BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map (S.g.f (p i)))).mp (hs i).epi_g
  have he (i : Fin l) : Function.Exact
      (leftTermMap S.f Z (p i) (n + -(p i)))
      (leftTermMap S.g Z (p i) (n + -(p i))) := by
    rw [leftTermMap,leftTermMap,tensorAcross_right_id,tensorAcross_right_id]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hs i).exact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    have hyi (i : Fin l) : leftTermMap S.g Z (p i) (n + -(p i)) (y i) = 0 :=
      congrArg (fun x => x i) hy
    choose x hx using fun i => (he i (y i)).mp (hyi i)
    exact ⟨x,funext hx⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    funext i
    exact hf i (congrArg (fun x => x i) h)
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    choose x hx using fun i => hg i (y i)
    exact ⟨x,funext hx⟩
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarStalk
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- A support interval containing degree zero supplies the finite-total index;
this is automatic for the ordinary resolution's interval [-length,0]. -/
def zeroDegreeIndex (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper) :
    Fin ((res.data.upper-res.data.lower).toNat+1) :=
  Classical.choose (intervalDegrees_covers res.data.lower res.data.upper 0 ⟨hlo,hhi⟩)

theorem zeroDegreeIndex_eq (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper) :
    res.data.degrees (zeroDegreeIndex res hlo hhi) = 0 :=
  Classical.choose_spec (intervalDegrees_covers res.data.lower res.data.upper 0 ⟨hlo,hhi⟩)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalPresentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u

variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The two signed totals coincide through their actual tensor-summand equivalences. -/
def totalIso : BimoduleComplexTensor.total k B B P Z p hp ≅
    BimoduleTotal.total k B P p hp Z :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalTermEquiv k B P Z p n).toModuleIso) (by
    intro n m h
    change n + 1 = m at h
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f => f.hom x)
      ((BimoduleComplexTensor.forgetTotalIso k B B P Z p hp).hom.comm n (n+1))
    exact h)

variable {Z} {Z' : CochainComplex (ModuleCat.{u} B) ℤ}
theorem totalIso_natural (f : Z ⟶ Z') :
    BimoduleComplexTensor.totalMap k B B P f p hp ≫ (totalIso k B P Z' p hp).hom =
      (totalIso k B P Z p hp).hom ≫ BimoduleTotal.totalMap k B P p hp f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact BimoduleComplexTensor.forget_totalInputMap k B B P f p hp n x

/-- Natural comparison on all input complexes, with the complete outside action. -/
def totalFunctorIso : BimoduleComplexTensor.totalFunctor k B B P p hp ≅
    BimoduleTotal.functor k B P p hp :=
  NatIso.ofComponents (fun Z => totalIso k B P Z p hp)
    (fun f => totalIso_natural k B P p hp f)
end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerivedPresentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotalPresentation

section
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i))]

/-- The coefficient presentations have exactly the same right module structure. -/
instance ordinaryProjective : ∀ i, Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleComplexTensor.rightComplex k B B P) (p i)) :=
  fun i => inferInstanceAs (Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i)))

end

open CategoryTheory ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B)

/-- Transport only the finite indexing type; every degree and both signed maps are unchanged. -/
def enumerationIso {l l' : ℕ} (p : Fin l → ℤ) (q : Fin l' → ℤ)
    (hp : StrictMono p) (hq : StrictMono q) (hl : l = l')
    (he : ∀ i, p i = q (Fin.cast hl i)) :
    BimoduleTotal.functor k B P p hp ≅ BimoduleTotal.functor k B P q hq := by
  subst l'
  have h : p = q := by funext i; exact he i
  subst q
  exact Iso.refl _

/-- Exact comparison of the ordinary resolution's finite list with the native interval. -/
def nonpositiveTotalFunctorIso (length : ℕ) :
    BimoduleComplexTensor.totalFunctor k B B P
      (OrdinarySimulation.TensorResolution.finiteDegrees length)
      (OrdinarySimulation.TensorResolution.finiteDegrees_strictMono length) ≅
    BimoduleTotal.functor k B P (BimoduleTotal.intervalDegrees (-(length : ℤ)) 0)
      (BimoduleTotal.intervalDegrees_strictMono (-(length : ℤ)) 0) :=
  totalFunctorIso k B P _ _ ≪≫ enumerationIso k B P _ _ _ _ (by omega) (by intro i; rfl)

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBoundedPresentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B)

instance projectiveDegrees {l : ℕ} (p : Fin l → ℤ)
    [hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) n)] :
    ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) (p i)) :=
  fun i => hproj (p i)

variable (data : BimoduleTotal.BoundedProjective k B P) (length : ℕ)
local notation "p" => OrdinarySimulation.TensorResolution.finiteDegrees length
local notation "hp" => OrdinarySimulation.TensorResolution.finiteDegrees_strictMono length

/-- Any native bounded model with these endpoints uses exactly the ordinary finite degree list. -/
def boundedNonpositiveTotalIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    BimoduleComplexTensor.totalFunctor k B B P p hp ≅
      BimoduleTotal.functor k B P data.degrees
        (BimoduleTotal.intervalDegrees_strictMono data.lower data.upper) := by
  dsimp only [BimoduleTotal.BoundedProjective.degrees]
  rw [hlo, hhi]
  exact nonpositiveTotalFunctorIso k B P length

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleResolutionBarAPI
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (X : ModuleCat.{u} (Enveloping k B)) (length : ℕ)
variable (ε : P ⟶ bimoduleStalk k B X) (hε : QuasiIso ε)
variable (hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n))
variable (hbound : ∀ n, n < -(length : ℤ) ∨ 0 < n → IsZero (P.X n))

/-- Package exactly the ordinary worker's actual bounded bimodule resolution
API. Augmentation, quasi-isomorphism, projectivity and support are all explicit. -/
def ofNonpositiveResolution : AugmentedProjective k B P X where
  data := { lower := -(length : ℤ), upper := 0, bounded := hbound, projective := hproj }
  augmentation := ε
  quasiIso := hε

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleScalarEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N] [hN : IsScalarTower k B N]

variable (M : ModuleCat.{u} (Enveloping k B))

def toNativeScalar : BimoduleBalancedTensor.Tensor k B M (CanonicalInput k B N) →ₗ[B]
    BimoduleBalancedTensor.Tensor k B M N where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    (CanonicalInput k B N) N _ _ _ _ _ _
    _ _ _ (BalancedTensor.scalarLeftTower k B (ModuleCat.of B N)) _ _ _ hN (LinearMap.id : CanonicalInput k B N →ₗ[B] N)).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

def fromNativeScalar : BimoduleBalancedTensor.Tensor k B M N →ₗ[B]
    BimoduleBalancedTensor.Tensor k B M (CanonicalInput k B N) where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    N (CanonicalInput k B N) _ _ _ _ _ _
    _ _ _ hN _ _ _ (BalancedTensor.scalarLeftTower k B (ModuleCat.of B N)) (LinearMap.id : N →ₗ[B] CanonicalInput k B N)).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

/-- Canonical restriction and the native compatible k action give the same B-valued tensor. -/
def scalarTensorIso :
    (BimoduleBalancedTensor.functor k B (CanonicalInput k B N)).obj M ≅
      (BimoduleBalancedTensor.functor k B N).obj M where
  hom := ModuleCat.ofHom (toNativeScalar k B N M)
  inv := ModuleCat.ofHom (fromNativeScalar k B N M)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {M} {M' : ModuleCat.{u} (Enveloping k B)}
theorem scalarTensor_natural (f : M ⟶ M') :
    (BimoduleBalancedTensor.functor k B (CanonicalInput k B N)).map f ≫ (scalarTensorIso k B N M').hom =
      (scalarTensorIso k B N M).hom ≫ (BimoduleBalancedTensor.functor k B N).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Exact comparison to native module evaluation with its original compatible scalar structure. -/
def scalarEvaluationIso (P : BiComplex k B) :
    moduleEvaluation k B P (ModuleCat.of B N) ≅
      ((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => scalarTensorIso k B N (P.X n))
    (fun n m _ => (scalarTensor_natural k B N (P.d n m)).symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftHorizontal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {Z : CochainComplex (ModuleCat.{u} B) ℤ}

/-- Reindexing the unchanged input degree commutes with the original bimodule map. -/
theorem termMap_transport {a b q₁ q₂ q₃ q₄ : ℤ} (f : P.X a ⟶ P.X b)
    (h₁₂ : q₁=q₂) (h₃₄ : q₃=q₄) (h₁₃ : q₁=q₃) (h₂₄ : q₂=q₄) :
    ModuleCat.ofHom (termMap (Z := Z) (Z' := Z) f (eqToHom (congrArg Z.X h₁₂))) ≫
      eqToHom (congrArg (fun q => ModuleCat.of B (Term k B P Z b q)) h₂₄) =
    eqToHom (congrArg (fun q => ModuleCat.of B (Term k B P Z a q)) h₁₃) ≫
      ModuleCat.ofHom (termMap (Z := Z) (Z' := Z) f (eqToHom (congrArg Z.X h₃₄))) := by
  subst q₂ q₃ q₄
  simp

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (b : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The native derived tensor functor computed by the source's actual bounded P[b]. -/
def shiftedDerivedTensor : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  BimoduleComplexTensor.derivedTotal k B B (P⟦b⟧)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftedPresentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (b : ℤ) (length : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((OrdinarySimulation.underlyingRightComplex P).X n)]

local instance instProjectiveMulOppositeCarrierRightTermRightObjBiComplexShiftFunctorInt : ∀ n, Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleTotal.right k B (P⟦b⟧)) n) :=
  fun n => inferInstanceAs (Module.Projective Bᵐᵒᵖ
    ((OrdinarySimulation.underlyingRightComplex P).X (n+b)))

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingGenerators
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
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

/-- The entire first arrow space inside the encoding algebra. -/
def first : Arrows k d →ₗ[k] B P where
  toFun x := (0,0,0,x,0,0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The entire second arrow space inside the encoding algebra. -/
def second : Arrows k d →ₗ[k] B P where
  toFun x := (0,0,0,0,x,0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

end LittleFinitistic.EncodingGenerators

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingLinearity
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Elements whose action commutes with a specified linear map form a subalgebra. -/
def intertwining (f : M →ₗ[k] N) : Subalgebra k (B P) where
  carrier := {b | ∀ x, f (b • x) = b • f x}
  zero_mem' := by intro x; simp only [zero_smul, map_zero]
  one_mem' := by intro x; simp only [one_smul]
  add_mem' := by
    intro a b ha hb x
    simp only [add_smul, map_add]
    rw [ha x, hb x]
  mul_mem' := by
    intro a b ha hb x
    simp only [mul_smul]
    rw [ha (b • x), hb x]
  algebraMap_mem' := by intro c x; simp only [IsScalarTower.algebraMap_smul, map_smul]

end LittleFinitistic.EncodingLinearity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexCoordinates
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexCoordinates
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D : RightComplex (QuadraticEncoding.B P))
abbrev vertex := AdjacentArrowSum.vertexComplex (composition P) 2
abbrev tensor := TensorComplex.tensorFunctor (k := k) D

def zeroIso := CornerPathTransport.coordinateIso (composition P) D 2 0
  (CornerSpaces.corner20Equiv (composition P))
def oneIso := CornerPathTransport.coordinateIso (composition P) D 2 1
  (CornerSpaces.corner21Equiv (composition P))
def twoIso := CornerPathTransport.coordinateIso (composition P) D 2 2
  (CornerSpaces.diagonalEquiv (composition P) 2)

def quotientEntry (a : Fin (d+1)) :=
  biproduct.ι (PathBasisIso.family k d) a ≫ RelationMatrixSequence.quotient P

def relationEntry (r : RelationIndex P) (a : Fin (d+1)) :=
  biproduct.ι (FiniteBasisIso.family (k := k) : RelationIndex P → _) r ≫
    RelationMatrixSequence.inclusion P ≫ biproduct.π (PathBasisIso.family k d) a

theorem relationEntry_eq (r : RelationIndex P) (a : Fin (d+1)) :
    relationEntry P r a = ∑ b, basisCoefficient P r a b • TensorArrowSum.insertion k d b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (biproduct.ι _ r ≫ RelationMatrixSequence.inclusion P ≫ biproduct.π _ a).hom c = _
  rw [RelationMatrixSequence.inclusion_coordinate]
  simp only [Finset.smul_sum,ModuleCat.hom_sum,ModuleCat.hom_smul,
    LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro b hb
  rw [TensorArrowSum.insertion_apply]
  simp only [smul_smul,mul_comm]

end LittleFinitistic.RelationVertexCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexSequence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local instance instHasFiniteBiproductsRightComplexB : HasFiniteBiproducts (RightComplex T) := HasFiniteBiproducts.of_hasFiniteProducts
local instance instHasFiniteBiproductsBiComplexB : HasFiniteBiproducts (BiComplex k T) := HasFiniteBiproducts.of_hasFiniteProducts

end LittleFinitistic.RelationVertexSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ThirdVertexFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertexFiltration
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
abbrev vertexComplex := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2

end LittleFinitistic.ThirdVertexFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ThirdVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
abbrev vertexComplex := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2

end LittleFinitistic.ThirdVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexZeroTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexZeroTotal
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
local notation "B" => QuadraticEncoding.B P
abbrev vertexFunctor := BimoduleVertex.functor k (QuadraticEncoding.B P)
  (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 0)

/-- Actual column terms vanish at vertex zero when their supporting vertex is positive. -/
theorem column_zero (j : Fin 3) (hj : 0 < j) (D : RightComplex (QuadraticEncoding.B P)) (n : ℤ) :
    IsZero ((vertexFunctor P).obj
      (((columnComplex k B (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) j)).obj D).X n)) := by
  exact (HomologicalComplex.eval _ _ n).map_isZero
    (VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 j hj D)

end LittleFinitistic.VertexZeroTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FirstVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.FirstVertex
open ExternalTensor.Section4

universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
abbrev vertexComplex := (VertexZeroTotal.vertexFunctor P).mapHomologicalComplex (.up ℤ)
end LittleFinitistic.FirstVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SecondVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SecondVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
abbrev vertex := BimoduleVertex.functor k (QuadraticEncoding.B P)
  (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 1)
abbrev vertexComplex := (vertex P).mapHomologicalComplex (.up ℤ)

end LittleFinitistic.SecondVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexHomotopyEquivalence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.VertexHomotopyEquivalence
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))

abbrev source (v : Fin 3) : RightComplex (QuadraticEncoding.B P) :=
  Fin.cases D₀ (Fin.cases D₁ (fun _ => D₂)) v
end LittleFinitistic.VertexHomotopyEquivalence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CanonicalArrowCompatibility
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

lemma diagonal_original (i : Fin 3) (D : RightComplex (B P)) :
    (VertexColumnComplex.diagonalComplexIso (composition P) i D).hom =
      diagonalComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem i) D := by
  apply NativeBridge.diagonal_eq_of_original
  intro n x
  exact VertexColumnModels.diagonal_symm_val (composition P) (D.X n) i x

end LittleFinitistic.CanonicalArrowCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingModuleAssembly
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.EncodingModuleAssembly
open QuadraticEncoding VertexDecomposition VertexModuleAssembly
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module (B P) M] [Module (B P) N]
  [IsScalarTower k (B P) M] [IsScalarTower k (B P) N]

abbrev system := ThreeVertexAlgebra.directedSystem (composition P)

end LittleFinitistic.EncodingModuleAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisAction
open QuadraticEncoding RelationBasisCoefficients
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {d t : ℕ} (P : Relations k d t) (x : Fin d → R)

variable (hx : ∀ j, (∑ h, ∑ l, P.quadratic j h l • (x h * x l)) +
  (∑ h, P.linear j h • x h) + P.constant j • (1 : R) = 0)

include hx in
/-- The entire relation space vanishes, including every chosen independent basis vector. -/
theorem relationSpace_le_kernel : relationSpace P ≤ (pathValue x).ker := by
  apply Submodule.span_le.2
  rintro z (⟨h,rfl⟩ | ⟨j,rfl⟩)
  · change pathValue x (commutation h) = 0
    simp [commutation,arrow]
  · change pathValue x (homogenized P j) = 0
    simpa only [homogenized,map_add,map_sum,map_smul,pathValue_basis,arrow,
      Fin.cases_zero,Fin.cases_succ,one_mul,mul_one] using hx j

include hx in
/-- Exact homogeneous coefficient equations for the fixed-diagram lifting theorem. -/
theorem basis_action_relation (r : RelationIndex P) :
    (∑ a, ∑ b, basisCoefficient P r a b • (arrow x b * arrow x a)) = 0 := by
  have hz := relationSpace_le_kernel P x hx (RelationSequence.relationBasis P r).property
  change pathValue x (RelationSequence.relationBasis P r).val = 0 at hz
  rw [← expansion P (RelationSequence.relationBasis P r)] at hz
  simpa only [map_sum,map_smul,pathValue_basis,basisCoefficient] using hz

/-- The concrete selected algebra satisfies all equations of the independent relation basis. -/
theorem encoding_basis_action (E : SelectionEncoding.Encoding k R) (r : RelationIndex E.relations) :
    (∑ a, ∑ b, basisCoefficient E.relations r a b •
      (arrow (SelectionEncoding.generator E) b * arrow (SelectionEncoding.generator E) a)) = 0 :=
  basis_action_relation E.relations (SelectionEncoding.generator E)
    (SelectionEncoding.generator_relations E) r
end LittleFinitistic.RelationBasisAction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceVerdier
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Category Pretriangulated
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

open QuadraticEncoding
abbrev Proj := ProjectiveComplexes.Proj (B P)
abbrev K := ProjectiveComplexes.K (B P)

/-- The manuscript's specified vertex idempotent. -/
abbrev vertex (i : Fin 3) : B P := ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) i

theorem vertex_idem (i : Fin 3) : vertex P i * vertex P i = vertex P i :=
  (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem i

/-- E_i = e_i B as an actual finite projective right module. -/
def E (i : Fin 3) : Proj P := VertexProjectives.object (vertex P i) (vertex_idem P i)

/-- Regard a projective as a bounded complex concentrated in degree zero. -/
def stalk : Proj P ⥤ K P :=
  ObjectProperty.lift _
    (HomologicalComplex.single (Proj P) (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ _)
    (fun _ => (BoundedHomotopy.bounded_quotient_obj_iff _ _).mpr
      ⟨0,0,inferInstance,inferInstance⟩)

end LittleFinitistic.SourceVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoDegreeExtVanishing
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Abelian
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma pd_lt_three (X : ModuleCat.{max u v} (B P)) : HasProjectiveDimensionLT X 3 := by
  have h : projectiveDimension X ≤ (2 : ℕ) :=
    le_trans (le_iSup (fun N : ModuleCat.{max u v} (B P) => projectiveDimension N) X)
      (globalDimension_le_two P).1
  exact (projectiveDimension_le_iff X 2).mp h

/-- Actual higher Ext vanishing from the proved global-dimension bound for B. -/
theorem ext_eq_zero (X Y : ModuleCat.{max u v} (B P)) (n : ℕ) (hn : 3 ≤ n)
    (x : Ext X Y n) : x = 0 := by
  have := pd_lt_three P X
  exact x.eq_zero_of_hasProjectiveDimensionLT 3 hn

/-- In particular every possible degree-four connecting morphism is zero. -/
theorem shifted_hom_eq_zero (X Y : ModuleCat.{max u v} (B P)) (n : ℕ) (hn : 3 ≤ n)
    (f : (DerivedCategory.singleFunctor _ 0).obj X ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(n : ℤ)⟧) : f = 0 := by
  let x : Ext X Y n := Ext.homEquiv.symm f
  have h := ext_eq_zero P X Y n hn x
  have h' := congrArg (fun x : Ext X Y n => x.hom) h
  simpa only [x,Equiv.apply_symm_apply,Ext.zero_hom] using h'
end LittleFinitistic.TwoDegreeFormality

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoDegreeSplitting
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
abbrev C := ModuleCat.{max u v} (B P)
abbrev D := DerivedCategory (C.{u,v} P)
abbrev H (n : ℤ) (X : D.{u,v} P) := (homologyFunctor (C P) n).obj X
abbrev stalk (M : C.{u,v} P) := (singleFunctor (C P) 0).obj M
variable (X : D.{u,v} P) (hX : TwoDegrees X)

def upperIso : upper X ≅ stalk P (H P 0 X) := by
  haveI := upper_isLE X hX
  exact canonicalIso 0 (upper X) ≪≫ (singleFunctor (C P) 0).mapIso
    (upperHomologyIso X 0 (by omega)).symm

def lowerIso : lower X ≅ (stalk P (H P (-3) X))⟦(3 : ℤ)⟧ := by
  haveI := lower_isLE X hX
  haveI := lower_isGE X hX
  exact canonicalIso (-3) (lower X) ≪≫
    (singleFunctor (C P) (-3)).mapIso (lowerHomologyIso X (-3) (by omega)) ≪≫
      ((singleFunctors (C P)).shiftIso 3 (-3) 0 (by omega)).symm.app (H P (-3) X)

def lowerShiftIso : (lower X)⟦(1 : ℤ)⟧ ≅ (stalk P (H P (-3) X))⟦(4 : ℤ)⟧ :=
  (shiftFunctor (D P) (1 : ℤ)).mapIso (lowerIso P X hX) ≪≫
    (shiftFunctorAdd (D P) (3 : ℤ) (1 : ℤ)).symm.app (stalk P (H P (-3) X))

include hX in
/-- The connecting map of the actual truncation triangle vanishes by Ext^4=0. -/
theorem connecting_eq_zero : (triangle X).mor₃ = 0 := by
  have hz := shifted_hom_eq_zero P (H P 0 X) (H P (-3) X) 4 (by omega)
    ((upperIso P X hX).inv ≫ (triangle X).mor₃ ≫ (lowerShiftIso P X hX).hom)
  apply (cancel_epi (upperIso P X hX).inv).mp
  apply (cancel_mono (lowerShiftIso P X hX).hom).mp
  erw [Category.assoc, comp_zero, zero_comp]
  exact hz

/-- A splitting of the actual truncation triangle, retaining its inclusion and projection. -/
structure TruncationSplit where
  iso : X ≅ lower X ⊞ upper X
  inclusion : DerivedTruncation.inclusion X ≫ iso.hom = biprod.inl
  projection : DerivedTruncation.projection X = iso.hom ≫ biprod.snd

def truncationSplit : TruncationSplit P X := Classical.choice (by
  obtain ⟨e,hi,hp⟩ := exists_iso_binaryBiproduct_of_distTriang
    (triangle X) (distinguished X) (connecting_eq_zero P X hX)
  exact ⟨⟨e,hi,hp⟩⟩)

/-- Actual B-linear two-degree formality, with the manuscript's shift by three. -/
def splitIso : X ≅ stalk P (H P 0 X) ⊞ (stalk P (H P (-3) X))⟦(3 : ℤ)⟧ :=
  (truncationSplit P X hX).iso ≪≫ biprod.mapIso (lowerIso P X hX) (upperIso P X hX) ≪≫
    biprod.braiding _ _
end LittleFinitistic.TwoDegreeFormality

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoDegreeFormalityNaturality
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {X Y : D.{u,v} P}

variable (X Y) (hX : TwoDegrees X) (hY : TwoDegrees Y) (f : X ⟶ Y)

/-- Substitute actual B-module identifications of the two cohomology modules. -/
def splitIsoWithModels (M N : C.{u,v} P) (e0 : H P 0 X ≅ M) (em : H P (-3) X ≅ N) :
    X ≅ stalk P M ⊞ (stalk P N)⟦(3 : ℤ)⟧ :=
  splitIso P X hX ≪≫ biprod.mapIso ((singleFunctor (C P) 0).mapIso e0)
    ((shiftFunctor (D P) (3 : ℤ)).mapIso ((singleFunctor (C P) 0).mapIso em))
end LittleFinitistic.TwoDegreeFormality

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainDirected
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_add _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_one _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_vertex _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_zero _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap_value _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_diagonal _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_radical _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.vertex_diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

theorem vertex_corner_diagonal (i : Fin (l+1)) (x : ChainAlgebra k l) :
    vertex k l i * x * vertex k l i = x.1 i • vertex k l i := by
  apply Prod.ext
  · funext t
    change ((Pi.single i (1:k) : Fin (l+1) → k) t * x.1 t) *
      (Pi.single i (1:k) : Fin (l+1) → k) t = x.1 i * (Pi.single i (1:k) : Fin (l+1) → k) t
    by_cases ht : t=i <;> simp [ht]
  · funext t
    change ((Pi.single i (1:k) : Fin (l+1) → k) t.succ * x.1 t.succ) * 0 +
      ((Pi.single i (1:k) : Fin (l+1) → k) t.succ * x.2 t + 0 * x.1 t.castSucc) *
        (Pi.single i (1:k) : Fin (l+1) → k) t.castSucc = x.1 i * 0
    by_cases h₁ : t.succ = i
    · have h₂ : t.castSucc ≠ i := by intro h; have := congrArg Fin.val h₁; have := congrArg Fin.val h; simp at *; omega
      simp [h₂]
    · simp [h₁]

/-- The actual chain algebra has the source's directed vertex system, including l=0. -/
def directedSystem : DirectedBound.DirectedSystem k (ChainAlgebra k l) (l+1) where
  e := vertex k l
  idem := vertex_idempotent k l
  orthogonal := vertex_orthogonal k l
  complete := vertex_complete k l
  diagonal i x := ⟨x.1 i,vertex_corner_diagonal k l i x⟩
  directed := vertex_directed k l
end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstBlockTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BlockTensor
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} L) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
open BimoduleComplexTensor

/-- Actual tensor with the off-diagonal complex on a first-block input is the second-block O-total. -/
def firstTotalIso :
    total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p hp ≅
      BlockModule.secondComplex L R (total k R L O Z p hp) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (firstTotalEquiv k L R O T Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (L × R) (totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n))
        (fun n => ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n)) n
    have h₂ : (total k R L O Z p hp).d n (n+1) = ModuleCat.ofHom (differential k R L O Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of R (totalTerm k R L O Z p n))
        (fun n => ModuleCat.ofHom (differential k R L O Z p n)) n
    change _ ≫ (ProductModules.secondInflation L R).map ((total k R L O Z p hp).d n (n+1)) = _
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (first_differential k L R O T Z p n z).symm)
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorVertex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap_value _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_diagonal _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_radical _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.vertex_diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BimoduleO
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

@[simp] theorem tensor_smul (b : B) (c : ChainAlgebra k l) (v : BimoduleO P a l) :
    (b ⊗ₜ[k] c) • v = b • (c • v) := rfl

@[simp] theorem tensor_vertex_smul (i : Fin (l+1)) (v : BimoduleO P a l) :
    TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i) • v =
      ChainAlgebra.vertex k l i • v := by
  change (1:B) • (ChainAlgebra.vertex k l i • v) = _
  exact one_smul _ _

/-- The BC vertex space is the same actual subspace of O as the C vertex space. -/
def tensorVertexSpaceEquiv (i : Fin (l+1)) :
    IdempotentTensor.leftSpace (k := k) (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i))
      (BimoduleO P a l) ≃ₗ[k] Compression.vertexSpace (k := k) P a l i where
  toFun x := ⟨x.val, by
    have h := x.property
    change TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i) • x.val = x.val at h
    rw [tensor_vertex_smul] at h
    exact h⟩
  invFun x := ⟨x.val, by
    exact (tensor_vertex_smul P a l i (show BimoduleO P a l from x.val)).trans x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation uses the actual balanced tensor over BC, not only over C. -/
def tensorVertexEquiv (i : Fin (l+1)) :
    BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
      (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
      (BimoduleO P a l) ≃ₗ[k] (underlyingComplex (k := k) P).X (a+(i.val:ℤ)) := by
  letI (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k (Enveloping k B))
  have (n : ℤ) : IsScalarTower k (Enveloping k B) (P.X n) := IsScalarTower.of_compHom k (Enveloping k B) (P.X n)
  exact (IdempotentTensor.tensorEquiv (k := k)
    (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)) (BimoduleO P a l)
    (TensorIdeal.vertex_idempotent _ (ChainAlgebra.vertex_idempotent k l i))).trans
      ((tensorVertexSpaceEquiv P a l i).trans
        ((Compression.vertexEquiv (k := k) P a l i).restrictScalars k))
end LittleFinitistic.OrdinarySimulation.BimoduleO

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimoduleComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.IdempotentTensor.leftMultiply_apply _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap_value _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_diagonal _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_radical _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.vertex_diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

def VertexTensor (i : Fin (l+1)) :=
  BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
    (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (BimoduleO P a l)

namespace VertexTensor
variable (i : Fin (l+1))
instance instAddCommGroup : AddCommGroup (VertexTensor P a l i) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l) _ (BimoduleO P a l)))
instance instModule : Module k (VertexTensor P a l i) := inferInstanceAs (Module k (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l) _ (BimoduleO P a l)))

def action : Enveloping k B →ₐ[k] Module.End k (VertexTensor P a l i) :=
  by
    have : SMulCommClass Bᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
      ⟨fun r x v => (smul_comm x r v).symm⟩
    exact BalancedTensor.bimoduleAction

instance instModuleEnveloping : Module (Enveloping k B) (VertexTensor P a l i) := Module.compHom _ (action P a l i).toRingHom

def mk : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)) →ₗ[k]
    BimoduleO P a l →ₗ[k] VertexTensor P a l i := BalancedTensor.mk k (B ⊗[k] ChainAlgebra k l)
    (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (BimoduleO P a l)

@[simp] theorem action_tmul_mk (b : B) (r : Bᵐᵒᵖ)
    (m : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (v : BimoduleO P a l) :
    (b ⊗ₜ[k] r) • mk P a l i m v = mk P a l i (b • m) (r • v) := rfl

local instance termScalar (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k (Enveloping k B))
local instance termTower (n : ℤ) : IsScalarTower k (Enveloping k B) (P.X n) :=
  IsScalarTower.of_compHom k (Enveloping k B) (P.X n)

/-- Evaluation of the actual BC-balanced tensor. -/
def evaluation : VertexTensor P a l i ≃ₗ[k] P.X (a+(i.val:ℤ)) :=
  BimoduleO.tensorVertexEquiv P a l i

@[simp] theorem evaluation_mk
    (m : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (v : BimoduleO P a l) :
    evaluation P a l i (mk P a l i m v) = (m.val • v : BimoduleO P a l) i := rfl

end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySimulationComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

theorem differential_transport {n n' m m' : ℤ} (hn : n = n') (hm : m = m') :
    eqToHom (congrArg P.X hn) ≫ P.d n' m' = P.d n m ≫ eqToHom (congrArg P.X hm) := by
  subst n'
  subst m'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

/-- Align the finite resolution's degree n with the source's degree a+n. -/
def restrictedShiftIso : P.restriction (ComplexShape.embeddingUpIntGE a) ≅
    (unsignedShift P (a+(l:ℤ))).restriction (TensorResolution.degreeEmbedding l) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => eqToIso (by
    change P.X (a+(n:ℤ)) = P.X ((-(l:ℤ)+n)+(a+l))
    congr 1
    omega)) (by
      intro n m _
      have hn : (-(l:ℤ)+(n:ℤ))+(a+l) = a+n := by omega
      have hm : (-(l:ℤ)+(m:ℤ))+(a+l) = a+m := by omega
      change eqToHom (congrArg P.X hn.symm) ≫ P.d ((-(l:ℤ)+n)+(a+l)) ((-(l:ℤ)+m)+(a+l)) =
        P.d (a+n) (a+m) ≫ eqToHom (congrArg P.X hm.symm)
      exact differential_transport P hn.symm hm.symm)

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorArrowComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.TensorArrowComparison
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- Tensor the actual right vertex, then identify it with the vertex of the full
left B-module tensor, preserving the original balanced tensor classes. -/
def component (e : B) (he : e*e=e) (M : ModuleCat.{u} (Enveloping k B)) :
    (BalancedTensor.tensorFunctor k B N).obj ((BimoduleVertex.functor k B e).obj M) ≅
      (LeftVertexHomology.vertex k B e).obj ((BimoduleBalancedTensor.functor k B N).obj M) :=
  (BalancedVertexImage.equiv k B M e he N).toModuleIso ≪≫
    (BimoduleTensorVertexBridge.equiv k B N e M).symm.toModuleIso

/-- The tensor/vertex comparison retains left multiplication by every original
supported arrow, and does not require the evaluation module to be flat. -/
theorem arrow_square (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (M : ModuleCat.{u} (Enveloping k B)) :
    (BalancedTensor.tensorFunctor k B N).map
        ((ArrowVertex.arrow k B ei ej a ha).app M) ≫ (component k B N ej hj M).hom =
      (component k B N ei hi M).hom ≫
        (LeftVertexHomology.arrow k B ei ej a ha).app ((BimoduleBalancedTensor.functor k B N).obj M) := by
  let l := ((BalancedTensor.tensorFunctor k B N).map
    ((ArrowVertex.arrow k B ei ej a ha).app M) ≫ (component k B N ej hj M).hom).hom
  let r := ((component k B N ei hi M).hom ≫
    (LeftVertexHomology.arrow k B ei ej a ha).app
      ((BimoduleBalancedTensor.functor k B N).obj M)).hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change l x = r x
  induction x using BalancedTensor.induction_on with
  | hz => exact l.map_zero.trans r.map_zero.symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (l.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (r.map_add x y).symm)

/-- Natural comparison for the full B-valued tensor functor. -/
def comparison (e : B) (he : e*e=e) :
    BimoduleVertex.functor k B e ⋙ BalancedTensor.tensorFunctor k B N ≅
      BimoduleBalancedTensor.functor k B N ⋙ LeftVertexHomology.vertex k B e :=
  BalancedVertexFunctor.comparison k B e he N ≪≫
    (BimoduleTensorVertexBridge.comparison k B N e).symm

def complexIso (e : B) (he : e*e=e) (P : BiComplex k B) :
    (((BalancedTensor.tensorFunctor k B N).mapHomologicalComplex (.up ℤ)).obj
      (((BimoduleVertex.functor k B e).mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (((LeftVertexHomology.vertex k B e).mapHomologicalComplex (.up ℤ)).obj
      (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => component k B N e he (P.X n))
    (fun n m _ => ((comparison k B N e he).hom.naturality (P.d n m)).symm)

/-- The full chain comparison respects the original left multiplication arrows. -/
theorem complex_arrow_square (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (P : BiComplex k B) :
    ((BalancedTensor.tensorFunctor k B N).mapHomologicalComplex (.up ℤ)).map
        (ArrowVertex.arrowComplex k B ei ej a ha P) ≫ (complexIso k B N ej hj P).hom =
      (complexIso k B N ei hi P).hom ≫
        ((LeftVertexHomology.arrow k B ei ej a ha).mapHomologicalComplex (.up ℤ)).app
          (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact arrow_square k B N ei ej a hi hj ha (P.X n)
end LittleFinitistic.TensorArrowComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FullTensorRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.FullTensorRectification
open ExternalTensor.Section4 QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P) N]

abbrev source (v : Fin 3) :=
  ((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).obj
    (VertexHomotopyEquivalence.source P D₀ D₁ D₂ v)
end LittleFinitistic.FullTensorRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexCategoricalAssembly
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexCategoricalAssembly
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (M N : ModuleCat.{u} (B P))
variable (E : ∀ i : Fin 3,
  (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M ≅
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj N)

abbrev scalar (M : ModuleCat.{u} (B P)) := (ModuleCat.restrictScalars (algebraMap k (B P))).obj M

def vertexEquiv (i : Fin 3) :
    VertexDecomposition.Space (EncodingModuleAssembly.system P) (scalar P M) i ≃ₗ[k]
      VertexDecomposition.Space (EncodingModuleAssembly.system P) (scalar P N) i :=
  (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) M).symm.trans
    ((E i).toLinearEquiv.trans
      (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) N))

end LittleFinitistic.VertexCategoricalAssembly

end

end OAI
end


