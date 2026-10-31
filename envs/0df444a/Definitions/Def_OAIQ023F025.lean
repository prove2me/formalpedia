-- Prove2me | Definitions.Def_OAIQ023F025
-- name    : OAIQ023F025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:54:32.533+00:00
-- url     : https://prove2.me/theorems/07bf46d5-5510-4312-8c8e-d7909e471316
-- title:
--   Definitions bundle OAIQ023F025 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 43 definitions, 12 instances and 41 theorems. The definitions and types are `OAI.DerivedBar.ParityBridge.countObjectComparison`, `OAI.DerivedBar.ParityBridge.derivedIterateWeightShiftIso`, `OAI.DerivedBar.ParityBridge.indexedDeshiftedCountIso`, `OAI.DerivedBar.ParityBridge.integerIndexedCountShiftIso`, `OAI.DerivedBar.ParityBridge.integerIndexedDeshiftedCountIso`, `OAI.DerivedBar.ParityBridge.integerIndexedWeightShiftIso`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.comparison`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.derived`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.nativeEvaluation`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.nativeSingleEvaluation`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.singleEvaluation`, `OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains`, `OAI.LittleFinitistic.BimoduleTotal.derived`, `OAI.LittleFinitistic.BimoduleTotal.derivedComparison`, `OAI.LittleFinitistic.BimoduleTotal.derivedSingleEvaluation`, `OAI.LittleFinitistic.BimoduleTotal.nativeBarIso`, `OAI.LittleFinitistic.BimoduleTotal.nativeBarIterateIso`, `OAI.LittleFinitistic.BimoduleTotal.nativeBarResolutionIso`, `OAI.LittleFinitistic.BimoduleTotal.nativeChainBarResolutionIso`, `OAI.LittleFinitistic.BimoduleTotal.nativeIterate`, `OAI.LittleFinitistic.BimoduleTotal.nativeIterateIndexedIso`, `OAI.LittleFinitistic.BimoduleTotal.nativeStalkIndexedIso`, `OAI.LittleFinitistic.BimoduleTotal.nonpositiveResolutionPowerIso`, `OAI.LittleFinitistic.BimoduleTotal.shiftIso`, `OAI.LittleFinitistic.BimoduleTotal.shiftTotalIso`, `OAI.LittleFinitistic.BimoduleTotal.singleEvaluationIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.boundedNonpositiveDerivedIso`, `OAI.LittleFinitistic.BimoduleTotalPresentation.shiftedDerivedIso`, `OAI.LittleFinitistic.CanonicalArrowCompatibility.arrow01Map`, `OAI.LittleFinitistic.CanonicalArrowCompatibility.arrow12Map`, `OAI.LittleFinitistic.ConcreteQuadraticDiagram.quadratic`, `OAI.LittleFinitistic.EvaluationVertexDiagram.module`, `OAI.LittleFinitistic.FirstVertex.columnInclusion`, `OAI.LittleFinitistic.FirstVertex.iota`, `OAI.LittleFinitistic.QuadraticEncoding.Relations.Satisfies`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.inclusion`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.projection`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexFixedEquiv`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexId`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_DerivedCountShift`, `Finitistic_Bar_IntegerCountObject`, `Finitistic_Bar_IntegerCountRestriction`, `Finitistic_Bar_IntegerCountShift`, `Finitistic_Bimodule_BimoduleAugmentationQuasiIso`, `Finitistic_Bimodule_BimoduleBarComparisonIso`, `Finitistic_Bimodule_BimoduleBarComparisonMap`, `Finitistic_Bimodule_BimoduleBarIteration`, `Finitistic_Bimodule_BimoduleBarResolution`, `Finitistic_Bimodule_BimoduleBarStalk`, `Finitistic_Bimodule_BimoduleBoundedPresentation`, `Finitistic_Bimodule_BimoduleDerivedFunctor`, `Finitistic_Bimodule_BimoduleDerivedShift`, `Finitistic_Bimodule_BimoduleResolutionBarAPI`, `Finitistic_Bimodule_BimoduleShiftCoherence`, `Finitistic_Bimodule_BimoduleShiftHorizontal`, `Finitistic_Bimodule_BimoduleShiftTotal`, `Finitistic_Bimodule_BimoduleShiftedPresentation`, `Finitistic_Bimodule_BimoduleSingleDifferential`, `Finitistic_Bimodule_BimoduleSingleEvaluation`, `Finitistic_Bimodule_BimoduleTotalUnderlying`, `Finitistic_Bimodule_BoundedBimoduleDerived`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Encoding_RelationBasisCoefficients`, `Finitistic_Localization_AmbientQuotientEvaluation`, `Finitistic_Localization_ConcreteQuadraticDiagram`, `Finitistic_Localization_EvaluationFromAlgebra`, `Finitistic_Localization_EvaluationLinear`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Localization_EvaluationVertexDiagram`, `Finitistic_Localization_NativeBoundedDerived`, `Finitistic_Localization_NativeSingleEvaluation`, `Finitistic_Rectification_CanonicalArrowCompatibility`, `Finitistic_Rectification_FirstVertex`, `Finitistic_Rectification_SecondVertex`, `Finitistic_Rectification_VertexTensorEvaluation`.
--
--   **Imports.** It imports the bundles `OAIQ023F021`, `OAIQ023F022` and `OAIQ023F023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F028` and `OAIQ023F030`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F021
import Definitions.Def_OAIQ023F022
import Definitions.Def_OAIQ023F023

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountRestriction
attribute [-instance] _root_.OAI.DerivedBar.outerTensor_free _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.countTensorBar_retract _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt HomologicalComplex
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionScalarTower
local instance integerCountRestrictionIndexDecidableEq_r1eb667_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance integerCountRestrictionShapeDecidableEq_r1eb667_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedModule
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedScalarTower
/-- The standard unit-valued cochain shift sign is the proved count sign. -/
theorem deshiftedCount_sign (r n : ℕ) :
    (-(r:ℤ)).negOnePow • (K r).d (r+(n+1)) (r+n) = indexedDifferential k D X N r n := by
  have hd : (K r).d (r+(n+1)) (r+n) =
      ModuleCat.ofHom (Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r) := by
    change ChainComplex.of.d
      (fun m => ModuleCat.of D (⨁ p : Multibar.Indexed.Shape m r, Multibar.Indexed.outerTensor k D X N p))
      (fun m => ModuleCat.ofHom (Multibar.Indexed.blockDifferential k D X N
        (inflated_ideal_zero D X N) m r)) ((r+n)+1) (r+n) = _
    exact ChainComplex.of_d _ _ (r+n)
  rw [hd]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  erw [units_hom_apply]
  erw [globalIndexedComparison]
  change (-(r:ℤ)).negOnePow •
      Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v =
    (-1:k)^r •
      Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v
  have hu : (r:ℤ).negOnePow = (-1:ℤˣ)^r := by
    apply Units.ext
    simpa using Int.coe_negOnePow_natCast r
  rw [Int.negOnePow_neg, hu]
  exact totalSign_smul k (⨁ p : Multibar.Indexed.Shape (r+n) r, Multibar.Indexed.outerTensor k D X N p) r
    (Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v)

theorem deshiftedCount_d (r n : ℕ) :
    (deshiftedCountRestriction k D X N r).d (n+1) n =
      (deshiftedCountXIso k D X N r (n+1)).hom ≫ indexedDifferential k D X N r n ≫
        (deshiftedCountXIso k D X N r n).inv := by
  change (-(r:ℤ)).negOnePow • ((K r).extend E).d ((E).f (n+1) + -(r:ℤ)) ((E).f n + -(r:ℤ)) = _
  rw [extend_d_eq (K r) E
    (show (E).f (r+(n+1))=(E).f (n+1) + -(r:ℤ) by change -((r+(n+1):ℕ):ℤ) = -((n+1:ℕ):ℤ) + -(r:ℤ); push_cast; omega)
    (show (E).f (r+n)=(E).f n + -(r:ℤ) by change -((r+n:ℕ):ℤ) = -(n:ℤ) + -(r:ℤ); push_cast; omega)]
  rw [← deshiftedCount_sign]
  erw [CategoryTheory.Linear.units_smul_comp, CategoryTheory.Linear.comp_units_smul]
  rfl

/-- A genuine chain isomorphism using the standard integer shift differential,
not a newly stipulated shift or transported count differential. -/
def indexedDeshiftedCountIso (r : ℕ) : indexedMultibar k D X N r ≅
    deshiftedCountRestriction k D X N r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (deshiftedCountXIso k D X N r n).symm) (by
      intro i j hij
      change j+1=i at hij
      subst i
      rw [deshiftedCount_d]
      simp only [Iso.symm_hom]
      erw [Iso.inv_hom_id_assoc]
      simp only [indexedMultibar, ChainComplex.of_d])
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountShift
attribute [-instance] _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

local instance instDecidableEqIndex_3_r1eb667_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instDecidableEqShape_r1eb667_1 (n r : ℕ) : DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
/-- Extension of the genuine recursive complex is the actual -r shift of
the count complex. Strict support, not truncation by assumption, supplies the inverse. -/
def integerIndexedDeshiftedCountIso (r : ℕ) :
    (integerExtension D).obj (indexedMultibar k D X N r) ≅ deshiftedCount k D X N r :=
  (integerExtension D).mapIso (indexedDeshiftedCountIso k D X N r) ≪≫
    strictSupportExtensionIso E (deshiftedCount k D X N r)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_12
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_12
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_11
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_11
/-- The manuscript's actual [r] cochain shift of the indexed recursive bar
is isomorphic to the entire signed count complex. -/
def integerIndexedCountShiftIso (r : ℕ) :
    ((integerExtension D).obj (indexedMultibar k D X N r))⟦(r:ℤ)⟧ ≅
      (integerExtension D).obj (K r) :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (r:ℤ)).mapIso
    (integerIndexedDeshiftedCountIso k D X N r) ≪≫
      ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (-(r:ℤ)) (r:ℤ) 0 (by omega)).symm.app
        ((integerExtension D).obj (K r))) ≪≫
      (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app ((integerExtension D).obj (K r))
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_DerivedCountShift
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.countComplex_projective _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_13
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_13
local instance derivedCountShiftIndexDecidableEq_r1eb667_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance derivedCountShiftShapeDecidableEq_r1eb667_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_12
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_12
/-- Identification with the original count subcomplex, using the actual integer
cochain shift and the already verified component sign involution. -/
def integerIndexedWeightShiftIso (r : ℕ) :
    ((integerExtension D).obj (indexedMultibar k D X N r))⟦(r:ℤ)⟧ ≅
      (integerExtension D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r) :=
  integerIndexedCountShiftIso k D X N r ≪≫
    (integerExtension D).mapIso (Multibar.Indexed.signedBlockIso k D X N (inflated_ideal_zero D X N) r)

attribute [local instance] OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions
/-- Each original count summand is the genuine [r] shift of the constructed
finite derived tensor iterate. -/
def derivedIterateWeightShiftIso (r : ℕ) :
    ((chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)))⟦(r:ℤ)⟧ ≅
    (integerQ D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r) :=
  (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} D)) (r:ℤ)).mapIso
    (integerDerivedIterateIndexedIso D k X N r) ≪≫
      ((DerivedCategory.Q.commShiftIso (r:ℤ)).symm.app
        ((integerExtension D).obj (indexedMultibar k D X N r))) ≪≫
      DerivedCategory.Q.mapIso (integerIndexedWeightShiftIso k D X N r)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountObject
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N

local instance integerCountIndexDecidableEq_r1eb667_1 (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
local instance integerCountShapeDecidableEq_r1eb667_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
local instance integerCountHasDerivedCategory_r1eb667_1 : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
/-- The proved genuine shift comparison, with its target named for downstream use. -/
def countObjectComparison (r : ℕ) :
    ((chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)))⟦(r:ℤ)⟧ ≅ countObject k D X N r :=
  derivedIterateWeightShiftIso k D X N r
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
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

/-- This records that no additional linear length-two relation was introduced. -/
theorem pathMap_eq_zero_iff (z : Paths k d) : pathMap P z = 0 ↔ z ∈ relationSpace P := by
  have hi : Function.Injective (lengthTwo P) := by
    intro x y h
    exact congrArg (fun a : B P => a.2.2.2.2.2) h
  rw [pathMap, LinearMap.comp_apply, (map_eq_zero_iff _ hi)]
  exact Submodule.Quotient.mk_eq_zero _

lemma arrow_product (i j : Fin (d + 1)) :
    arrow12 P i * arrow01 P j = pathMap P (basis i ⊗ₜ[k] basis j) := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,0,0,basis i,0)
    (0,0,0,basis j,0,0) = (0,0,0,0,0,(relationSpace P).mkQ (basis i ⊗ₜ[k] basis j))
  simp [ThreeVertexAlgebra.mul, composition]

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisCoefficients
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Every vector in the chosen relation basis gives the genuine algebra equation. -/
theorem algebra_relation (r : relationSpace P) :
    (∑ a, ∑ b, coefficient P r a b • (arrow12 P b * arrow01 P a)) = 0 := by
  have h := (pathMap_eq_zero_iff P r.val).2 r.property
  rw [← expansion P r] at h
  simpa only [map_sum,map_smul,← arrow_product] using h

theorem basis_relation (r : RelationIndex P) :
    (∑ a, ∑ b, basisCoefficient P r a b • (arrow12 P b * arrow01 P a)) = 0 :=
  algebra_relation P (RelationSequence.relationBasis P r)
end LittleFinitistic.RelationBasisCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ConcreteQuadraticDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.ConcreteQuadraticDiagram
open QuadraticEncoding RelationBasisCoefficients ThreeVertexAlgebra
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The exact three-vertex algebra and its actual independent relation basis,
packaged for the induced-column construction. -/
def quadratic : ExternalTensor.Section4.Quadratic k (B P)
    (A := Fin (d+1)) (J := Fin (d+1)) (R := RelationIndex P) where
  e₀ := vertex (composition P) 0
  e₁ := vertex (composition P) 1
  e₂ := vertex (composition P) 2
  a := arrow01 P
  b := arrow12 P
  ha i := by
    change mul (composition P) (0,0,0,basis i,0,0) (vertex (composition P) 0) = _
    simp [vertex,mul,arrow01]
  hb j := by
    change mul (composition P) (0,0,0,0,basis j,0) (vertex (composition P) 1) = _
    simp [vertex,mul,arrow12]
  coeff := basisCoefficient P
  relation := basis_relation P
end LittleFinitistic.ConcreteQuadraticDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalUnderlying
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The frozen K-flatness proof applies to the total with its complete B action. -/
theorem totalMap_quasiIso
    [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]
    {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (totalMap k B P p hp f) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (totalMap k B P p hp f) (ModuleCat.restrictScalars (algebraMap k B))).mp
  let e : Arrow.mk ((forget k B).map (totalMap k B P p hp f)) ≅
      Arrow.mk (ComplexTensor.finiteTotalMap k B (right k B P) p hp f) := Arrow.isoMk (underlyingIso k B P p hp Z) (underlyingIso k B P p hp Z')
    ((underlyingComparison k B P p hp).hom.naturality f).symm
  apply (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr
  exact ComplexTensor.finiteTotalMap_quasiIso k B (right k B P) f p hp
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerivedFunctor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- Every quasi-isomorphism becomes invertible after applying the actual B-valued total. -/
theorem inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).IsInvertedBy
    (functor k B P p hp ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  let := totalMap_quasiIso k B P p hp f
  exact (inferInstance : IsIso (DerivedCategory.Q.map (totalMap k B P p hp f)))

/-- The actual fixed bimodule tensor total descends to the native derived category of B-modules. -/
def derived : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  Localization.lift (functor k B P p hp ⋙ DerivedCategory.Q)
    (inverts k B P p hp) DerivedCategory.Q

/-- This derived endofunctor is computed by the signed tensor total on every input complex. -/
def derivedComparison : DerivedCategory.Q ⋙ derived k B P p hp ≅
    functor k B P p hp ⋙ DerivedCategory.Q :=
  Localization.fac (functor k B P p hp ⋙ DerivedCategory.Q)
    (inverts k B P p hp) DerivedCategory.Q

instance derived_additive : (derived k B P p hp).Additive := by
  rw [Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} B)).trW]
  let e : HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙
      (DerivedCategory.Qh ⋙ derived k B P p hp) ≅
      functor k B P p hp ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)) _ ≪≫
        derivedComparison k B P p hp
  let := Functor.additive_of_iso e.symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)) _
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The degreewise comparison intertwines the full native differential at every pair of included consecutive degrees. -/
theorem evaluationAtIndex_comm (i j : Fin l) (h : p i+1=p j) :
    (evaluationAtIndex k B P N p hp i).hom ≫ (moduleEvaluation k B P N).d (p i) (p j) =
      (total k B P p hp (singleInput B N)).d (p i) (p j) ≫
        (evaluationAtIndex k B P N p hp j).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((moduleEvaluation k B P N).d (p i) (p j)).hom
      ((singleTermIso k B P N (p i) (p i) rfl).hom.hom (x i)) =
    (singleTermIso k B P N (p j) (p j) rfl).hom.hom
      (((total k B P p hp (singleInput B N)).d (p i) (p j)).hom x j)
  rw [single_total_d k B P N p hp i j h]
  exact (congrArg (fun f => f.hom (x i)) (single_horizontal k B P N (p i) (p j) h)).symm
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
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
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (hP : ∀ n, (∀ i, p i ≠ n) → IsZero (P.X n))

theorem evaluationAtIndex_transport (i j : Fin l) (h : i=j) :
    eqToIso (congrArg (fun n => ModuleCat.of B (TotalTerm k B P p (singleInput B N) n))
      (congrArg p h).symm) ≪≫ evaluationAtIndex k B P N p hp i ≪≫
      (moduleEvaluation k B P N).XIsoOfEq (congrArg p h) = evaluationAtIndex k B P N p hp j := by
  subst j
  simp [HomologicalComplex.XIsoOfEq]

theorem evaluationTermIso_at (i : Fin l) :
    evaluationTermIso k B P N p hp hP (p i) = evaluationAtIndex k B P N p hp i := by
  classical
  unfold evaluationTermIso
  split_ifs with h
  · have hi : h.choose=i := hp.injective h.choose_spec
    exact evaluationAtIndex_transport k B P N p hp h.choose i hi
  · exact False.elim (h ⟨i,rfl⟩)

/-- The ordinary signed total on an input module in degree zero is the exact native P tensor_B N complex. -/
def singleEvaluationIso : total k B P p hp (singleInput B N) ≅ moduleEvaluation k B P N :=
  HomologicalComplex.Hom.isoOfComponents (evaluationTermIso k B P N p hp hP) (by
    intro n m h
    classical
    by_cases hn : ∃ i, p i=n
    · obtain ⟨i,rfl⟩ := hn
      by_cases hm : ∃ j, p j=m
      · obtain ⟨j,rfl⟩ := hm
        rw [evaluationTermIso_at,evaluationTermIso_at]
        exact evaluationAtIndex_comm k B P N p hp i j h
      · exact ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map_isZero
          (hP m (by simpa only [not_exists] using hm))).eq_of_tgt _ _
    · exact (totalSingle_isZero k B P N p n (by simpa only [not_exists] using hn)).eq_of_src _ _)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- Evaluation of the actual derived endofunctor on a degree-zero module is the native tensor complex in D(B-Mod). -/
def derivedSingleEvaluation :
    (derived k B P p hp).obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj (moduleEvaluation k B P N) :=
  (derivedComparison k B P p hp).app (singleInput B N) ≪≫
    DerivedCategory.Q.mapIso (singleEvaluationIso k B P N p hp hP)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BoundedBimoduleDerived
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

namespace BoundedProjective
variable {k B} {P : BiComplex k B} (data : BoundedProjective k B P)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The native derived tensor endofunctor of this one fixed bounded projective bimodule complex. -/
def derived : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

instance additive : data.derived.Additive := by
  let : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived_additive k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

def comparison : DerivedCategory.Q ⋙ data.derived ≅
    BimoduleTotal.functor k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ⋙ DerivedCategory.Q := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact derivedComparison k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

/-- Agreement with the canonical native degree-zero evaluation, including its full B action. -/
def singleEvaluation (N : ModuleCat.{u} B) :
    data.derived.obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj (moduleEvaluation k B P N) := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact derivedSingleEvaluation k B P N data.degrees
    (intervalDegrees_strictMono data.lower data.upper) data.complete
end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarResolution
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
/-- The left leg of the actual comparison zigzag is invertible for every chain input. -/
instance barInputAugmentation_isIso : IsIso (barInputAugmentation data) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let : ∀ i, Module.Projective Bᵐᵒᵖ
      (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  let ε := (DerivedBar.integerExtension B).map (DerivedBar.barTotalAugmentation k B Z)
  have : QuasiIso ε := inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (DerivedBar.barTotalAugmentation k B Z)
      ComplexShape.embeddingDownNat))
  have := totalMap_quasiIso k B P data.degrees
    (intervalDegrees_strictMono data.lower data.upper) ε
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (totalMap k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ε)))

/-- The native derived tensor of the integer extension is computed on its genuine
projective bar resolution, with no hypothesis on the input's terms. -/
def nativeBarResolutionIso : DerivedBar.integerQ B ⋙ data.derived ≅
    DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedBar.integerExtension B) data.comparison ≪≫
    (asIso (barInputAugmentation data)).symm

/-- The same comparison written using the native chain-localization inclusion. -/
def nativeChainBarResolutionIso :
    DerivedBar.chainQ B ⋙ (DerivedBar.chainToIntegerDerived B ⋙ data.derived) ≅
      DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedBar.chainToIntegerDerivedIso B) data.derived ≪≫
    nativeBarResolutionIso data
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleAugmentationQuasiIso
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- The actual bimodule augmentation is an epimorphism of complexes. -/
theorem augmentation_epi : Epi res.augmentation := by
  let : ∀ n, Epi (res.augmentation.f n) := augmentation_epi_f res
  constructor
  intro Y f g h
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_epi (res.augmentation.f n)).mp
  exact congrArg (fun φ => φ.f n) h

/-- Tensoring the actual bounded resolution augmentation with a complex of
projective left modules gives a quasi-isomorphism of B-module complexes. -/
theorem augmentation_total_quasiIso (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    [∀ q, Projective (Z.X q)] :
    QuasiIso (leftTotalMap res.augmentation Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper)) := by
  let := augmentation_epi res
  let K := kernel res.augmentation
  let S : ShortComplex (BiComplex k B) :=
    ShortComplex.mk (kernel.ι res.augmentation) res.augmentation (kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel res.augmentation }
  have hK : K.Acyclic := hS.acyclic_X₁ res.quasiIso
  have hb (a : ℤ) (ha : ∀ i, res.data.degrees i ≠ a) : IsZero (K.X a) := by
    have hz : IsZero (P.X a) := outside_interval_isZero k B P
      res.data.lower res.data.upper res.data.bounded a ha
    have : Subsingleton (P.X a) := ModuleCat.isZero_iff_subsingleton.mp hz
    have hinj := (ModuleCat.mono_iff_injective ((kernel.ι res.augmentation).f a)).mp inferInstance
    have : Subsingleton (K.X a) := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_of_subsingleton _
  have htK : (total k B K res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) Z).Acyclic := by
    apply total_acyclic_of_rows k B K Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) hb hK
      res.data.lower (res.data.lower + (res.data.upper-res.data.lower).toNat)
    · intro i
      dsimp [BoundedProjective.degrees,intervalDegrees]
      omega
    · intro i
      have := i.isLt
      dsimp [BoundedProjective.degrees,intervalDegrees]
      omega
  exact shortExact_quasiIso_g _
    (leftTotal_shortExact k B Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) S hS) htK
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonMap
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_1
/-- Actual comparison induced by the actual bimodule augmentation, before
localization descent. Invertibility is a separate finite-total proof obligation. -/
def augmentationComparisonOnChains :
    DerivedBar.chainQ B ⋙ (DerivedBar.chainToIntegerDerived B ⋙ res.data.derived) ⟶
    DerivedBar.chainQ B ⋙
      (DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B) :=
  (nativeChainBarResolutionIso res.data).hom ≫
    whiskerLeft (DerivedBar.barTotalFunctor k B)
      (whiskerLeft (DerivedBar.integerExtension B)
        (whiskerRight res.tensorAugmentation DerivedCategory.Q)) ≫
    (resolvedStalkIso res i₀ hi₀).hom ≫
    (actualBarResolutionIso (X := X)).inv

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonIso
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.countComplex_projective _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDMinimal.term_projective _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_2
/-- The original augmentation, evaluated on the actual free bar resolution,
becomes an isomorphism in the integer derived category. -/
instance resolvedTensorAugmentation_isIso : IsIso
    (whiskerLeft (DerivedBar.barTotalFunctor k B)
      (whiskerLeft (DerivedBar.integerExtension B)
        (whiskerRight res.tensorAugmentation DerivedCategory.Q))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let : ∀ n, Projective ((DerivedBar.barTotal k B Z).X n) :=
    DerivedBar.barTotal_projective k B Z
  let Z' := (DerivedBar.integerExtension B).obj (DerivedBar.barTotal k B Z)
  have : ∀ n, Projective (Z'.X n) := by
    intro n
    exact inferInstanceAs (Projective
      (((DerivedBar.barTotal k B Z).extend ComplexShape.embeddingDownNat).X n))
  have := augmentation_total_quasiIso res Z'
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (leftTotalMap res.augmentation Z' res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper))))

instance augmentationComparisonOnChains_isIso :
    IsIso (augmentationComparisonOnChains res i₀ hi₀) := by
  unfold augmentationComparisonOnChains
  infer_instance

/-- Natural identification of the native D(B-Mod) tensor by the actual bounded
right-projective bimodule resolution and DerivedBar's genuine localized tensor,
after chainToIntegerDerived. Both outside module actions are retained. -/
def nativeBarIso :
    DerivedBar.chainToIntegerDerived B ⋙ res.data.derived ≅
      DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedBar.chainQ B)
    (DerivedBar.chainQuasiIso B) (DerivedCategory (ModuleCat.{u} B))).preimageIso
      (asIso (augmentationComparisonOnChains res i₀ hi₀))

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarIteration
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.commute _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_3
/-- Iteration of the native full-left-action integer derived endofunctor. -/
def nativeIterate : ℕ → (DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B))
  | 0 => 𝟭 _
  | r+1 => nativeIterate r ⋙ res.data.derived

/-- The augmentation comparison iterates naturally on the genuine localized
chain category. This identifies actual derived functors, not only vector spaces. -/
def nativeBarIterateIso : (r : ℕ) →
    DerivedBar.chainToIntegerDerived B ⋙ nativeIterate res r ≅
      DerivedBar.derivedTensorIterate k B (barModule (X := X)) r ⋙ DerivedBar.chainToIntegerDerived B
  | 0 => (Functor.rightUnitor _) ≪≫ (Functor.leftUnitor _).symm
  | r+1 =>
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (nativeBarIterateIso r) res.data.derived ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DerivedBar.derivedTensorIterate k B (barModule (X := X)) r)
        (nativeBarIso res i₀ hi₀) ≪≫
      (Functor.associator _ _ _).symm

/-- On degree-zero modules, the same native derived iteration is represented
by the actual Section 6 indexed multibar with all module actions retained. -/
def nativeIterateIndexedIso (N : ModuleCat.{u} B) (r : ℕ) :
    (nativeIterate res r).obj ((DerivedBar.integerQ B).obj ((ChainComplex.single₀ _).obj N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (nativeIterate res r).mapIso
      ((DerivedBar.chainToIntegerDerivedIso B).app ((ChainComplex.single₀ _).obj N)).symm ≪≫
    (nativeBarIterateIso res i₀ hi₀ r).app ((DerivedBar.chainQ B).obj ((ChainComplex.single₀ _).obj N)) ≪≫
    DerivedBar.integerDerivedIterateIndexedIso B k (barModule (X := X)) N r
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarStalk
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.commute _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_4
/-- Genuine native iteration on the native integer stalk, identified with the
actual Section 6 indexed multibar. No bar comparison is supplied as a premise. -/
def nativeStalkIndexedIso (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper)
    (N : ModuleCat.{u} B) (r : ℕ) :
    (nativeIterate res r).obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (nativeIterate res r).mapIso (integerSingleIso N).symm ≪≫
    nativeIterateIndexedIso res (zeroDegreeIndex res hlo hhi)
      (zeroDegreeIndex_eq res hlo hhi) N r

/-- Functor iteration here is the usual repeated application of the native
integer-derived tensor on objects. -/
theorem nativeIterate_obj (r : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    (nativeIterate res r).obj Y = (res.data.derived.obj^[r]) Y := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change res.data.derived.obj ((nativeIterate res r).obj Y) = _
    rw [ih,Function.iterate_succ_apply']
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBoundedPresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable (data : BimoduleTotal.BoundedProjective k B P) (length : ℕ)
local notation "p" => OrdinarySimulation.TensorResolution.finiteDegrees length
local notation "hp" => OrdinarySimulation.TensorResolution.finiteDegrees_strictMono length

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (BimoduleTotal.right k B P) n)]

/-- Generic bridge for a shifted P as well as Q_X. No augmentation or target module
is needed to compare two presentations of the very same bounded complex. -/
def boundedNonpositiveDerivedIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    BimoduleComplexTensor.derivedTotal k B B P p hp ≅ data.derived :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
    (DerivedCategory (ModuleCat.{u} B))).preimageIso
      (BimoduleComplexTensor.derivedTotalComparison k B B P p hp ≪≫
        isoWhiskerRight (boundedNonpositiveTotalIso k B P data length hlo hhi) DerivedCategory.Q ≪≫
          data.comparison.symm)

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftHorizontal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
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

variable (k B P Z)

theorem horizontal_shift_reindex (s n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    ModuleCat.ofHom (horizontalBetween k B P (Z⟦s⟧) n m a b h hab) ≫
      (shiftReindex k B P Z s b m).hom =
    (shiftReindex k B P Z s a n).hom ≫
      ModuleCat.ofHom (horizontalBetween k B P Z (n+s) (m+s) a b (by omega) hab) :=
  termMap_transport (k := k) (B := B) (P := P) (Z := Z)
    (q₁ := n + -a + s) (q₂ := m + -b + s)
    (q₃ := n+s + -a) (q₄ := m+s + -b)
    (P.d a b) (by omega) (by omega) (by omega) (by omega)

/-- The Koszul sign compensates exactly for the sign on the shifted horizontal differential. -/
theorem entry_shift (s n m a b : ℤ) (h : n+1=m) :
    ModuleCat.ofHom (entryBetween k B P (Z⟦s⟧) n m a b h) ≫
      ((shiftColumnIso k B P Z s b).hom).f m =
    ((shiftColumnIso k B P Z s a).hom).f n ≫
      (s.negOnePow • ModuleCat.ofHom (entryBetween k B P Z (n+s) (m+s) a b (by omega))) := by
  rw [shiftColumn_hom_f,shiftColumn_hom_f]
  unfold entryBetween
  split_ifs with hab
  · erw [Linear.comp_units_smul,Linear.units_smul_comp,Linear.comp_units_smul,
      smul_smul,horizontal_shift_reindex]
    congr 1
    rw [← Int.negOnePow_add]
    congr 1
    rw [← hab]
    simp [mul_add,add_comm]
  · erw [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
    rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The complete signed total commutes with every integer shift, with the actual horizontal maps. -/
def shiftTotalIso (s : ℤ) : total k B P p hp (Z⟦s⟧) ≅ (total k B P p hp Z)⟦s⟧ :=
  HomologicalComplex.Hom.isoOfComponents (shiftTermIso k B P p hp Z s) (by
    intro n m h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    have hv := congrArg (fun f => f.hom (x j)) ((shiftColumnIso k B P Z s (p j)).hom.comm n m)
    have hh (i : Fin l) := congrArg (fun f => f.hom (x i))
      (entry_shift k B P Z s n m (p i) (p j) h)
    change s.negOnePow • (((total k B P p hp Z).d (n+s) (m+s)).hom
      ((shiftTermIso k B P p hp Z s n).hom.hom x) j) =
      (((shiftColumnIso k B P Z s (p j)).hom).f m).hom
        (((total k B P p hp (Z⟦s⟧)).d n m).hom x j)
    erw [total_d_apply k B P Z p hp (n+s) (m+s) (by change n+1=m at h; omega),
      total_d_apply k B P (Z⟦s⟧) p hp n m h]
    erw [map_add, map_sum, smul_add, Finset.smul_sum]
    refine congrArg₂ HAdd.hAdd ?_ ?_
    · change s.negOnePow • ((((columnFunctor k B P (p j)).obj Z).d (n+s) (m+s)).hom
          (((shiftColumnIso k B P Z s (p j)).hom.f n).hom (x j))) =
        ((shiftColumnIso k B P Z s (p j)).hom.f m).hom
          ((((columnFunctor k B P (p j)).obj (Z⟦s⟧)).d n m).hom (x j)) at hv
      exact (congrArg (s.negOnePow • ·)
        (fullColumn_d k B P Z (p j) (n+s) (m+s)
          (((shiftColumnIso k B P Z s (p j)).hom.f n).hom (x j)))).symm.trans
        (hv.trans (congrArg (((shiftColumnIso k B P Z s (p j)).hom.f m).hom)
          (fullColumn_d k B P (Z⟦s⟧) (p j) n m (x j))))
    · apply Finset.sum_congr rfl
      intro i _
      exact hh i |>.symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftCoherence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id
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

variable (P : BiComplex k B)

variable {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem functor_map_component (f : Z ⟶ Z') (n : ℤ)
    (x : TotalTerm k B P p Z n) (i : Fin l) :
    (((functor k B P p hp).map f).f n).hom x i =
      (((columnFunctor k B P (p i)).map f).f n).hom (x i) := by
  change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i = _
  erw [ComplexTensor.finiteTotalMap_apply]
  exact (fullColumn_map k B P f (p i) n (x i)).symm

@[simp] theorem shiftTotal_hom_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (((shiftTotalIso k B P p hp Z s).hom).f n).hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

/-- Naturality of the full tensor shift, in every input complex and chain map. -/
def shiftIso (s : ℤ) : shiftFunctor _ s ⋙ functor k B P p hp ≅
    functor k B P p hp ⋙ shiftFunctor _ s :=
  NatIso.ofComponents (fun Z => shiftTotalIso k B P p hp Z s) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    have h := congrArg (fun g => (g.f n).hom (x i))
      (((columnFunctor k B P (p i)).commShiftIso s).hom.naturality f)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    change (((shiftColumnIso k B P Z' s (p i)).hom).f n).hom
        ((((functor k B P p hp).map ((shiftFunctor _ s).map f)).f n).hom x i) =
      (((functor k B P p hp).map f).f (n+s)).hom
        (((shiftTotalIso k B P p hp Z s).hom.f n).hom x) i
    erw [functor_map_component,functor_map_component,shiftTotal_hom_apply]
    simp only [Functor.comp_map,Functor.comp_obj,HomologicalComplex.comp_f,ModuleCat.hom_comp,
      CochainComplex.shiftFunctor_map_f'] at h
    convert h using 1 <;> rfl)

theorem total_transport_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (n m : ℤ) (h : n = m) (x : TotalTerm k B P p Z n) (i : Fin l) :
    ((eqToHom (congrArg (fun q => (total k B P p hp Z).X q) h)).hom x) i =
      (eqToHom (congrArg (fun q => ((columnFunctor k B P (p i)).obj Z).X q) h)).hom (x i) := by
  subst m
  rfl

@[simp] theorem shiftIso_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (((shiftIso k B P p hp s).hom.app Z).f n).hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

theorem shiftZero_inv_component (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (n : ℤ) (x : TotalTerm k B P p Z n) (i : Fin l) :
    (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
      ((functor k B P p hp).obj Z)).f n).hom x i =
    (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
      ((columnFunctor k B P (p i)).obj Z)).f n).hom (x i) := by
  convert total_transport_apply k B P p hp Z n (n+0) (by omega) x i using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem shiftAdd_inv_component (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (s t n : ℤ) (x : TotalTerm k B P p Z (n+t+s)) (i : Fin l) :
    (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
      ((functor k B P p hp).obj Z)).f n).hom x i =
    (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
      ((columnFunctor k B P (p i)).obj Z)).f n).hom (x i) := by
  convert total_transport_apply k B P p hp Z (n+t+s) (n+(s+t)) (by omega) x i using 1
  all_goals try with_reducible_and_instances rfl
  rfl

/-- All integer shifts satisfy zero and addition coherence for the actual tensor endofunctor. -/
instance commShift : (functor k B P p hp).CommShift ℤ where
  commShiftIso := shiftIso k B P p hp
  commShiftIso_zero := by
    ext Z n x
    funext i
    have h := congrArg (fun e => ((e.hom.app Z).f n).hom (x i))
      ((columnFunctor k B P (p i)).commShiftIso_zero ℤ)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    simp only [Iso.app_hom,Functor.CommShift.isoZero_hom_app, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply] at h ⊢
    have hc := shiftZero_inv_component k B P p hp Z n
      ((((functor k B P p hp).map ((shiftFunctorZero _ ℤ).hom.app Z)).f n).hom x) i
    have hf := functor_map_component k B P p hp ((shiftFunctorZero _ ℤ).hom.app Z) n x i
    have he := hc.trans (congrArg (fun y =>
      (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
        ((columnFunctor k B P (p i)).obj Z)).f n).hom y) hf)
    exact h.trans he.symm
  commShiftIso_add s t := by
    ext Z n x
    funext i
    have h := congrArg (fun e => ((e.hom.app Z).f n).hom (x i))
      ((columnFunctor k B P (p i)).commShiftIso_add s t)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    simp only [Iso.app_hom,Functor.CommShift.isoAdd_hom_app, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply,CochainComplex.shiftFunctor_map_f'] at h ⊢
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    let y := ((((functor k B P p hp).map ((shiftFunctorAdd _ s t).hom.app Z)).f n).hom x)
    let z := (((shiftIso k B P p hp t).hom.app (Z⟦s⟧)).f n).hom y
    have hf := functor_map_component k B P p hp ((shiftFunctorAdd _ s t).hom.app Z) n x i
    have ht := shiftIso_apply k B P p hp (Z⟦s⟧) t n y i
    have hs := shiftIso_apply k B P p hp Z s (n+t) z i
    have ht' := ht.trans (congrArg (fun w => ((shiftColumnIso k B P (Z⟦s⟧) t (p i)).hom.f n).hom w) hf)
    have hs' := hs.trans (congrArg (fun w => ((shiftColumnIso k B P Z s (p i)).hom.f (n+t)).hom w) ht')
    have hc := shiftAdd_inv_component k B P p hp Z s t n
      ((((shiftIso k B P p hp s).hom.app Z).f (n+t)).hom z) i
    have he := hc.trans (congrArg (fun w =>
      (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
        ((columnFunctor k B P (p i)).obj Z)).f n).hom w) hs')
    exact h.trans he.symm
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_NativeBoundedDerived
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

namespace BoundedProjective
variable {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The exact native module-valued degree-zero evaluation, using the module's original compatible k action. -/
def nativeEvaluation (N : Type u) [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N] :
    data.derived.obj (DerivedCategory.Q.obj (singleInput B (ModuleCat.of B N))) ≅
      DerivedCategory.Q.obj (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) :=
  data.singleEvaluation (ModuleCat.of B N) ≪≫ DerivedCategory.Q.mapIso (scalarEvaluationIso k B N P)
end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerivedShift
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
section Finite
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- The proved total-complex shift structure descends through the native derived localization. -/
instance derived_commShift : (derived k B P p hp).CommShift ℤ := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
      (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp) :=
    ⟨derivedComparison k B P p hp⟩
  exact Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) ℤ
    (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp)
end Finite

namespace BoundedProjective
variable {k B} {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

instance commShift : data.derived.CommShift ℤ := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived_commShift k B P data.degrees
    (intervalDegrees_strictMono data.lower data.upper)

end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleResolutionBarAPI
attribute [-instance] _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.commute _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.shiftIso_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTotal_hom_apply
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

local notation "R" => ofNonpositiveResolution P X length ε hε hproj hbound

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_5
/-- Exact source-style F^r applied to a native degree-zero module, represented
by the genuine Section 6 indexed multibar. All comparison data is constructed. -/
def nonpositiveResolutionPowerIso (N : ModuleCat.{u} B) (r : ℕ) :
    ((R).data.derived.obj^[r]) (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (eqToIso (nativeIterate_obj R r _)).symm ≪≫
    nativeStalkIndexedIso R (by dsimp [ofNonpositiveResolution]; omega) (by rfl) N r
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftedPresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable (data : BimoduleTotal.BoundedProjective k B (P⟦b⟧))

attribute [local instance] OAI.LittleFinitistic.BimoduleTotalPresentation.instProjectiveMulOppositeCarrierRightTermRightObjBiComplexShiftFunctorInt
/-- The ordinary shifted-derived API agrees with any native model of the identical
shifted complex on [-length,0]. No shift-left tensor theorem is reproved or assumed. -/
def shiftedDerivedIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    OrdinarySimulation.shiftedDerivedTensor P b length ≅ data.derived :=
  boundedNonpositiveDerivedIso k B (P⟦b⟧) data length hlo hhi

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
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
variable {Y : Type v} [AddCommGroup Y] [Module k Y]

namespace Representation
variable {P : Relations k d t} (X : Representation P Y)

instance evaluationModule : Module (B P) X.Evaluation where
  smul := X.act
  one_smul y := by
    change X.act (ThreeVertexAlgebra.unit (composition P)) y = y
    rcases y with ⟨a,b,c⟩
    simp [act, ThreeVertexAlgebra.unit]; rfl
  mul_smul a b y := by
    change X.act (ThreeVertexAlgebra.mul (composition P) a b) y = X.act a (X.act b y)
    apply Prod.ext
    · simp [act, ThreeVertexAlgebra.mul, mul_smul]
    apply Prod.ext
    · simp [act, ThreeVertexAlgebra.mul, map_add, map_smul, smul_add, smul_smul]
      module
    · simp [act, ThreeVertexAlgebra.mul, map_add, map_smul, smul_add, smul_smul,
        Module.End.mul_apply]
      module
  smul_zero a := by
    change X.act a (0,0,0) = (0,0,0)
    simp [act]; rfl
  smul_add a y z := by
    change X.act a (y.1+z.1,y.2.1+z.2.1,y.2.2+z.2.2) =
      ((X.act a y).1+(X.act a z).1,(X.act a y).2.1+(X.act a z).2.1,
       (X.act a y).2.2+(X.act a z).2.2)
    apply Prod.ext
    · simp [act, smul_add]
    apply Prod.ext <;> simp [act, smul_add, map_add] <;> abel
  add_smul a b y := by
    change X.act (a+b) y =
      ((X.act a y).1+(X.act b y).1,(X.act a y).2.1+(X.act b y).2.1,
       (X.act a y).2.2+(X.act b y).2.2)
    rw [ThreeVertexAlgebra.add_eq]
    apply Prod.ext
    · simp [act, add_smul]
    apply Prod.ext <;> simp [act, add_smul, map_add] <;> abel
  zero_smul y := by
    change X.act (0,0,0,0,0,0) y = (0,0,0)
    simp [act]; rfl

theorem smul_eq (a : B P) (y : X.Evaluation) : a • y = X.act a y := rfl


instance instIsScalarTowerBEvaluation : IsScalarTower k (B P) X.Evaluation where
  smul_assoc c a y := by
    change X.act (c • a) y = c • X.act a y
    rw [ThreeVertexAlgebra.smul_eq, evaluation_smul]
    apply Prod.ext
    · simp [act, mul_smul]
    apply Prod.ext <;> simp [act, smul_add, smul_smul]

@[simp] theorem vertex0_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 0 • y = (y.1,0,0) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl
@[simp] theorem vertex1_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 1 • y = (0,y.2.1,0) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl
@[simp] theorem vertex2_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 2 • y = (0,0,y.2.2) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl

@[simp] theorem arrow01_smul (i : Fin (d+1)) (y : X.Evaluation) :
    arrow01 P i • y = (0, (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator i) y.1, 0) := by
  simp [smul_eq, act, arrow01]; rfl
@[simp] theorem arrow12_smul (i : Fin (d+1)) (y : X.Evaluation) :
    arrow12 P i • y = (0, 0, (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator i) y.2.1) := by
  simp [smul_eq, act, arrow12]; rfl

@[simp] theorem s_smul (y : X.Evaluation) : arrow01 P 0 • y = (0,y.1,0) := by
  simp; rfl
@[simp] theorem s'_smul (y : X.Evaluation) : arrow12 P 0 • y = (0,0,y.2.1) := by
  simp; rfl
@[simp] theorem generator01_smul (h : Fin d) (y : X.Evaluation) :
    arrow01 P h.succ • y = (0,X.generator h y.1,0) := by simp; rfl
@[simp] theorem generator12_smul (h : Fin d) (y : X.Evaluation) :
    arrow12 P h.succ • y = (0,0,X.generator h y.2.1) := by simp; rfl

@[simp] theorem pathMap_smul (z : Paths k d) (y : X.Evaluation) :
    pathMap P z • y = (0,0,X.rawPathAction z y.1) := by
  simp [smul_eq, act, pathMap, lengthTwo, pathAction]; rfl

/-- Inclusion of the copy of Y at each vertex. -/
def inclusion (i : Fin 3) : Y →ₗ[k] X.Evaluation where
  toFun y := match i with
    | 0 => (y,0,0)
    | 1 => (0,y,0)
    | 2 => (0,0,y)
  map_add' y z := by fin_cases i <;> rw [evaluation_add] <;> simp <;> rfl
  map_smul' c y := by fin_cases i <;> rw [evaluation_smul] <;> simp <;> rfl

def projection (i : Fin 3) : X.Evaluation →ₗ[k] Y where
  toFun y := match i with
    | 0 => y.1
    | 1 => y.2.1
    | 2 => y.2.2
  map_add' y z := by fin_cases i <;> rfl
  map_smul' c y := by fin_cases i <;> rfl

@[simp] theorem projection_inclusion (i : Fin 3) (y : Y) :
    X.projection i (X.inclusion i y) = y := by fin_cases i <;> rfl

theorem vertex_smul (i : Fin 3) (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) i • y = X.inclusion i (X.projection i y) := by
  fin_cases i <;> simp [inclusion, projection] <;> rfl

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.ComplexTensor.column_d _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_comp _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_right _root_.OAI.LittleFinitistic.ComplexTensor.matrix_apply _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.equivalence_tmul _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.left_smul_value _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticEncoding.Representation
open IdempotentTensor BalancedTensor
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]
variable (X : Representation P Y)

abbrev vertexId (i : Fin 3) : B P := ThreeVertexAlgebra.vertex (composition P) i

/-- Identify the actual fixed-point vertex part of M(Y) with Y. -/
def vertexFixedEquiv (i : Fin 3) : leftSpace (k := k) (vertexId (P := P) i) X.Evaluation ≃ₗ[k] Y where
  __ := (X.projection i).comp (leftSpace (k := k) (vertexId (P := P) i) X.Evaluation).subtype
  invFun y := ⟨X.inclusion i y, by
    change vertexId (P := P) i • X.inclusion i y = X.inclusion i y
    rw [X.vertex_smul, X.projection_inclusion]⟩
  left_inv m := by
    apply Subtype.ext
    exact (X.vertex_smul i m.val).symm.trans m.property
  right_inv y := X.projection_inclusion i y

/-- The manuscript's E_i tensor_B M(Y) ≃ Y, for the actual right ideal E_i=e_iB. -/
def vertexTensorEquiv (i : Fin 3) :
    Tensor k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation ≃ₗ[k] Y :=
  (tensorEquiv (k := k) (vertexId (P := P) i) X.Evaluation
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem i)).trans (X.vertexFixedEquiv i)

@[simp] theorem vertexTensorEquiv_mk (i : Fin 3)
    (m : rightIdeal (vertexId (P := P) i)) (y : X.Evaluation) :
    X.vertexTensorEquiv i (BalancedTensor.mk k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation m y) =
      X.projection i (m.val • y) := rfl

@[simp] theorem vertexTensorEquiv_symm (i : Fin 3) (y : Y) :
    (X.vertexTensorEquiv i).symm y =
      BalancedTensor.mk k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation
        ⟨vertexId (P := P) i,(ThreeVertexAlgebra.directedSystem (composition P)).idem i⟩
        (X.inclusion i y) := rfl

end LittleFinitistic.QuadraticEncoding.Representation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_AmbientQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic
open BalancedTensor
universe u v
namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

def degreeZero := HomologicalComplex.single (ModuleCat.{u} (B P)ᵐᵒᵖ) (ComplexShape.up ℤ) (0 : ℤ)
end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationFromAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The displayed finite list of quadratic equations, in an arbitrary k-algebra. -/
def Relations.Satisfies (x : Fin d → R) : Prop := ∀ j,
  (∑ h, ∑ l, P.quadratic j h l • (x h * x l)) +
    (∑ h, P.linear j h • x h) + P.constant j • (1 : R) = 0

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationLinear
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy
universe u v w z
namespace BalancedTensor
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

instance tensorFunctorLinear : (tensorFunctor.{u,v,w,z} k A N).Linear k where
  map_smul {M M'} f c := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    exact LinearMap.congr_fun ((mk k A (ScalarModule k A M') N).map_smul c (f.hom m)) n

instance homotopyEvaluationLinear : (homotopyEvaluation.{u,v,w,z} k A N).Linear k :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (.up ℤ)).Linear k)
end BalancedTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationVertexDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev module := ModuleCat.of (B P) X.Evaluation

end LittleFinitistic.EvaluationVertexDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_NativeSingleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal.BoundedProjective
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- Native degree-zero module embedding, with the module's original compatible scalar action. -/
def nativeSingleEvaluation (N : Type u) [AddCommGroup N] [Module k N] [Module B N]
    [IsScalarTower k B N] :
    data.derived.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B N)) ≅
      DerivedCategory.Q.obj (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) :=
  data.nativeEvaluation N
end LittleFinitistic.BimoduleTotal.BoundedProjective

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FirstVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local notation "B" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- The original first induced column includes into the actual zero column. -/
def columnInclusion : (columnComplex k B (s).e₀).obj D₀ ⟶ L0Prime s D₀ D₁ D₂ f g := biprod.inl

/-- The manuscript's original first-vertex insertion into the constructed total. -/
def iota : D₀ ⟶ (vertexComplex P).obj (InducedRectification.total s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 0 D₀).hom ≫
    (vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H)

end LittleFinitistic.FirstVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SecondVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

def intoF1 : (columnComplex k T (s).e₁).obj D₁ ⟶ Exactness.F1 s D₀ D₁ D₂ f g :=
  biprod.inl ≫ RectificationTotal.inclusion (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0
    (h1 (Exactness.data s D₀ D₁ D₂ f g))

variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

def iota : D₁ ⟶ (vertexComplex P).obj (Exactness.P s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁).hom ≫
    (vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)

/-- The filtration route retains the original vertex-one summand insertion. -/
theorem intoF1_nested : intoF1 P D₀ D₁ D₂ f g ≫ Exactness.i1 s D₀ D₁ D₂ f g H =
    (Exactness.data s D₀ D₁ D₂ f g).in₁ ≫
      InducedRectification.inclusion s D₀ D₁ D₂ f g H := by
  exact (Category.assoc _ _ _).trans (congrArg
    (fun h => (biprod.inl : (columnComplex k T (s).e₁).obj D₁ ⟶
      F1₀ (Exactness.data s D₀ D₁ D₂ f g)) ≫ h)
    ((include1 (inducedData s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)).inclusion_totalMap))

theorem iota_original : iota P D₀ D₁ D₂ f g H =
    (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁).hom ≫
      (vertexComplex P).map ((Exactness.data s D₀ D₁ D₂ f g).in₁) ≫
      (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H) := by
  dsimp only [iota]
  erw [← (vertexComplex P).map_comp (intoF1 P D₀ D₁ D₂ f g)
    (Exactness.i1 s D₀ D₁ D₂ f g H), intoF1_nested, Functor.map_comp]
  rfl
end LittleFinitistic.SecondVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CanonicalArrowCompatibility
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis
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

lemma arrow01_target (a : Fin (d+1)) :
    ThreeVertexAlgebra.vertex (composition P) 1 * arrow01 P a = arrow01 P a := by
  change ThreeVertexAlgebra.mul (composition P) (0,1,0,0,0,0) (0,0,0,basis a,0,0) = _
  simp [ThreeVertexAlgebra.mul, arrow01]

lemma arrow12_target (b : Fin (d+1)) :
    ThreeVertexAlgebra.vertex (composition P) 2 * arrow12 P b = arrow12 P b := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,1,0,0,0) (0,0,0,0,basis b,0) = _
  simp [ThreeVertexAlgebra.mul, arrow12]

/-- Left multiplication by the original first arrow on the actual vertex complexes. -/
def arrow01Map (a : Fin (d+1)) :=
  arrowComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
    (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a) (arrow01_target P a)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

/-- Left multiplication by the original second arrow on the actual vertex complexes. -/
def arrow12Map (b : Fin (d+1)) :=
  arrowComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
    (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b) (arrow12_target P b)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

end LittleFinitistic.CanonicalArrowCompatibility

end

end OAI
end


