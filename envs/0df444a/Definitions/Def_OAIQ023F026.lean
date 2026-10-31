-- Prove2me | Definitions.Def_OAIQ023F026
-- name    : OAIQ023F026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:58:28.345977+00:00
-- url     : https://prove2.me/theorems/4f38669e-d549-485e-9641-ae6acccbad11
-- title:
--   Definitions bundle OAIQ023F026 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 52 definitions, 14 instances and 54 theorems. The definitions and types are `OAI.LittleFinitistic.ConcreteChainRepresentatives.representative`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.augmentation`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.extendedArrow`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.extendedVertex`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionAugmentation`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionDifferential`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionIdeal`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionTerm`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.supportedIdealEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.complex`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.complexIso`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.differential`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.finiteModel`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.outsideEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.supportedEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.supportedIdealEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.FullTensorTerm.termEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentationHom`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentationMap`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleAugmentationHom`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleAugmentationMap`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleComplex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleDifferential`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleTerm`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleTerminal`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.bimoduleTerminalObject`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.complex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.differential`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetBimodule`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerComplex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.leftMultiply`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.regularEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.simpleCoordinates`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.termEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.termObject`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.terminalEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.bimoduleEquiv` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_EncodingGenerators`, `Finitistic_Localization_ConcreteChainRepresentatives`, `Finitistic_Localization_ConcreteFixedDiagram`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Localization_SourceLinear`, `Finitistic_Localization_SourceShiftLinear`, `Finitistic_Localization_SourceVerdier`, `Finitistic_Localization_UnderlyingRepresentatives`, `Finitistic_Ordinary_OrdinaryBimoduleAugmentation`, `Finitistic_Ordinary_OrdinaryChainResolution`, `Finitistic_Ordinary_OrdinaryFullTensorComplex`, `Finitistic_Ordinary_OrdinaryFullTensorTerms`, `Finitistic_Ordinary_OrdinaryIntegerResolution`, `Finitistic_Ordinary_OrdinaryResolutionComplex`, `Finitistic_Ordinary_OrdinaryResolutionExact`, `Finitistic_Ordinary_OrdinaryResolutionQuasiIso`, `Finitistic_Ordinary_OrdinarySimulationComparison`, `Finitistic_Ordinary_OrdinaryTensorAugmentation`, `Finitistic_Ordinary_OrdinaryTensorBimoduleComparison`, `Finitistic_Ordinary_OrdinaryTensorBimoduleResolution`, `Finitistic_Ordinary_OrdinaryTensorDifferential`, `Finitistic_Ordinary_OrdinaryTensorResolution`, `Finitistic_Ordinary_OrdinaryTensorResolutionComplex`, `Finitistic_Ordinary_OrdinaryTerminalResolution`, `Finitistic_Rectification_InducedRectification`, `Finitistic_Selection_SelectionEncoding`.
--
--   **Imports.** It imports the bundles `OAIQ023F021`, `OAIQ023F022`, `OAIQ023F023` and `OAIQ023F024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F028`, `OAIQ023F029` and `OAIQ023F030`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F021
import Definitions.Def_OAIQ023F022
import Definitions.Def_OAIQ023F023
import Definitions.Def_OAIQ023F024

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingGenerators
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
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

lemma first_mem (S : Subalgebra k (B P)) (h : ∀ a, arrow01 P a ∈ S)
    (x : Arrows k d) : first P x ∈ S := by
  have hx := congrArg (first P) ((Pi.basisFun k (Fin (d+1))).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  exact S.sum_mem fun a _ => by
    simpa only [map_smul, Pi.basisFun_apply, first, LinearMap.coe_mk,
      AddHom.coe_mk, arrow01, basis] using S.smul_mem (h a) (((Pi.basisFun k (Fin (d+1))).repr x) a)

lemma second_mem (S : Subalgebra k (B P)) (h : ∀ a, arrow12 P a ∈ S)
    (x : Arrows k d) : second P x ∈ S := by
  have hx := congrArg (second P) ((Pi.basisFun k (Fin (d+1))).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  exact S.sum_mem fun a _ => by
    simpa only [map_smul, Pi.basisFun_apply, second, LinearMap.coe_mk,
      AddHom.coe_mk, arrow12, basis] using S.smul_mem (h a) (((Pi.basisFun k (Fin (d+1))).repr x) a)

end LittleFinitistic.EncodingGenerators

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceVerdier
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
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

theorem target01 (i : Fin (d+1)) : vertex P 1 * QuadraticEncoding.arrow01 P i =
    QuadraticEncoding.arrow01 P i := by
  ext <;> simp [vertex, ThreeVertexAlgebra.vertex, QuadraticEncoding.arrow01,
    ThreeVertexAlgebra.mul]

theorem target12 (i : Fin (d+1)) : vertex P 2 * QuadraticEncoding.arrow12 P i =
    QuadraticEncoding.arrow12 P i := by
  ext <;> simp [vertex, ThreeVertexAlgebra.vertex, QuadraticEncoding.arrow12,
    ThreeVertexAlgebra.mul]

/-- The actual right-module arrow maps, given by left multiplication. -/
def arrow01 (i : Fin (d+1)) : E P 0 ⟶ E P 1 :=
  VertexProjectives.arrow (vertex_idem P 0) (vertex_idem P 1)
    (QuadraticEncoding.arrow01 P i) (target01 P i)
def arrow12 (i : Fin (d+1)) : E P 1 ⟶ E P 2 :=
  VertexProjectives.arrow (vertex_idem P 1) (vertex_idem P 2)
    (QuadraticEncoding.arrow12 P i) (target12 P i)

def s : (stalk P).obj (E P 0) ⟶ (stalk P).obj (E P 1) := (stalk P).map (arrow01 P 0)
def s' : (stalk P).obj (E P 1) ⟶ (stalk P).obj (E P 2) := (stalk P).map (arrow12 P 0)

/-- The cone choices are made once, in K, before any evaluation module is chosen. -/
def cones : TwoConeVerdier.ConePair (K P) := by
  let H := distinguished_cocone_triangle (s P)
  let H' := distinguished_cocone_triangle (s' P)
  exact ⟨Triangle.mk (s P) H.choose_spec.choose H.choose_spec.choose_spec.choose,
    Triangle.mk (s' P) H'.choose_spec.choose H'.choose_spec.choose_spec.choose,
    H.choose_spec.choose_spec.choose_spec, H'.choose_spec.choose_spec.choose_spec⟩

@[simp] theorem cones_first : (cones P).first.mor₁ = s P := rfl
@[simp] theorem cones_second : (cones P).second.mor₁ = s' P := rfl

abbrev Sigma : MorphismProperty (K P) := (cones P).Sigma
/-- Section 3's actual Verdier quotient K/S. -/
abbrev Q := (cones P).Q
abbrev q : K P ⥤ Q P := (cones P).q

instance s_inverted : IsIso ((q P).map (s P)) :=
  inferInstanceAs (IsIso ((cones P).q.map (cones P).first.mor₁))
instance s'_inverted : IsIso ((q P).map (s' P)) :=
  inferInstanceAs (IsIso ((cones P).q.map (cones P).second.mor₁))

end LittleFinitistic.SourceVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceLinear
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

open scoped ModuleCat.Algebra in
instance linearProj : Linear k (Proj P) := inferInstance
instance linearK : Linear k (K P) := inferInstance
instance linearQ : Linear k (Q P) := inferInstance
instance linearQuotient : (q P).Linear k := inferInstance

end LittleFinitistic.SourceVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ConcreteChainRepresentatives
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ConcreteChainRepresentatives
open SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

abbrev representative (X : K P) : CochainComplex (Proj P) ℤ := X.obj.as

theorem representative_bounded (X : K P) :
    BoundedHomotopy.boundedComplex (Proj P) (representative P X) :=
  (BoundedHomotopy.bounded_quotient_obj_iff _ _).1 X.property

/-- The lifted source diagram has genuine bounded projective chain representatives
and a specified null-homotopy for every relation; no chain representatives are assumed. -/
theorem quadratic_representatives (na nb nr : ℕ) (X₀ X₁ X₂ : K P)
    (a : Fin na → (X₀ ⟶ X₁)) (b : Fin nb → (X₁ ⟶ X₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ r, ∑ i, ∑ j, c r i j • (a i ≫ b j) = 0) :
    ∃ (f : Fin na → (representative P X₀ ⟶ representative P X₁))
      (g : Fin nb → (representative P X₁ ⟶ representative P X₂)),
      (∀ i, (HomotopyCategory.quotient (Proj P) (.up ℤ)).map (f i) = (a i).hom) ∧
      (∀ j, (HomotopyCategory.quotient (Proj P) (.up ℤ)).map (g j) = (b j).hom) ∧
      Nonempty (∀ r, Homotopy (∑ i, ∑ j, c r i j • (f i ≫ g j)) 0) := by
  let I := (BoundedHomotopy.bounded (Proj P)).ι
  apply ChainRepresentatives.quadratic_chain_representatives na nb nr
    (representative P X₀) (representative P X₁) (representative P X₂)
    (fun i => I.map (a i)) (fun j => I.map (b j)) c
  intro r
  have h := congrArg I.map (hc r)
  simp only [Functor.map_sum,Functor.map_smul,Functor.map_comp,Functor.map_zero] at h
  exact h
end LittleFinitistic.ConcreteChainRepresentatives

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.SelectionEncoding
open QuadraticPresentation QuadraticEncoding

universe u v w
variable {k : Type u} {R : Type v} [Field k] [Ring R] [Algebra k R] (E : Encoding k R)

noncomputable instance instRingDirectedAlgebra : Ring (directedAlgebra E) :=
  ThreeVertexAlgebra.instRing (composition E.relations)

end LittleFinitistic.SelectionEncoding

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceShiftLinear
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

/-- Scalar action commutes with shifts on bounded projective homotopy complexes. -/
instance shiftLinearK (n : ℤ) : (shiftFunctor (K P) n).Linear k := by
  let I := (BoundedHomotopy.bounded (Proj P)).ι
  have : (shiftFunctor (K P) n ⋙ I).Linear k :=
    Functor.linear_of_iso k (I.commShiftIso n).symm
  constructor
  intro X Y f a
  apply I.map_injective
  rw [I.map_smul]
  exact (shiftFunctor (K P) n ⋙ I).map_smul a f

/-- Scalar action commutes with shifts on the actual source Verdier quotient. -/
instance shiftLinearQ (n : ℤ) : (shiftFunctor (Q P) n).Linear k := by
  let : Localization.Lifting (q P) (Sigma P)
      (shiftFunctor (K P) n ⋙ q P) (shiftFunctor (Q P) n) :=
    ⟨((q P).commShiftIso n).symm⟩
  exact (Localization.functor_linear_iff (q P) (Sigma P) k
    (shiftFunctor (K P) n ⋙ q P) (shiftFunctor (Q P) n)).mp inferInstance

end LittleFinitistic.SourceVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ConcreteFixedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.ConcreteFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)
local instance instHasFiniteBiproductsKaroubiQRelations : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubiQRelations : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _

end LittleFinitistic.ConcreteFixedDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

instance instFiniteDimensionalEvaluation [FiniteDimensional k Y] : FiniteDimensional k X.Evaluation :=
  inferInstanceAs (FiniteDimensional k (Y × Y × Y))

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_UnderlyingRepresentatives
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.UnderlyingRepresentatives
open SourceVerdier ConcreteChainRepresentatives
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

abbrev forget : Proj P ⥤ ModuleCat.{u} (QuadraticEncoding.B P)ᵐᵒᵖ :=
  (ProjectiveComplexes.finiteProjective (QuadraticEncoding.B P)).ι

abbrev complex (X : K P) : CochainComplex (ModuleCat.{u} (QuadraticEncoding.B P)ᵐᵒᵖ) ℤ :=
  ((forget P).mapHomologicalComplex (.up ℤ)).obj (representative P X)

theorem projective (X : K P) (n : ℤ) :
    Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ ((complex P X).X n) :=
  ((representative P X).X n).property.2

attribute [local instance] ExternalTensor.Section4.rightModuleK

/-- Genuine boundedness after forgetting the projective subcategory. -/
theorem bounded (X : K P) :
    ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero ((complex P X).X n) := by
  obtain ⟨lo,hi,hlo,hhi⟩ := representative_bounded P X
  let := hlo
  let := hhi
  refine ⟨lo,hi,fun n hn => ?_⟩
  apply (forget P).map_isZero
  rcases hn with hn | hn
  · exact (representative P X).isZero_of_isStrictlyGE lo n hn
  · exact (representative P X).isZero_of_isStrictlyLE hi n hn

/-- The actual chain-representative relation homotopies survive the forgetful functor. -/
def relationHomotopy (na nb nr : ℕ) (X₀ X₁ X₂ : K P)
    (f : Fin na → (representative P X₀ ⟶ representative P X₁))
    (g : Fin nb → (representative P X₁ ⟶ representative P X₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (H : ∀ r, Homotopy (∑ i, ∑ j, c r i j • (f i ≫ g j)) 0) (r : Fin nr) :
    Homotopy
      (∑ i, ∑ j, c r i j •
        (((forget P).mapHomologicalComplex (.up ℤ)).map (f i) ≫
          ((forget P).mapHomologicalComplex (.up ℤ)).map (g j))) 0 := by
  simpa only [Functor.map_sum,Functor.map_smul,Functor.map_comp,Functor.map_zero]
    using (forget P).mapHomotopy (H r)
end LittleFinitistic.UnderlyingRepresentatives

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Exactness at every interior projective, with no assumed resolution predicate. -/
theorem resolution_exact (i : ℕ) (hi : i+1 < l)
    (x : rightTerm (k := k) (⟨i+1,by omega⟩ : Fin (l+1))) :
    resolutionMap (k := k) (⟨i+1,hi⟩ : Fin l) x = 0 ↔
      ∃ y : rightTerm (k := k) (⟨i,by omega⟩ : Fin (l+1)), resolutionMap (k := k) (⟨i,by omega⟩ : Fin l) y = x := by
  exact (resolutionMap_zero_iff (⟨i+1,hi⟩ : Fin l) x).trans
    (resolutionMap_range (⟨i,by omega⟩ : Fin l) x).symm

end ChainAlgebra
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTerminalResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_add _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_one _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_zero _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.right_action _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

namespace TerminalSimple
instance instModuleMulOppositeChainAlgebra : Module (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) :=
  Module.compHom k (ChainAlgebra.terminalCharacter k l).toRingHom.op
end TerminalSimple

namespace ChainAlgebra
/-- The augmentation of the terminal right projective. -/
def augmentation : rightTerm (k := k) (Fin.last l) →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] TerminalSimple k where
  toFun x := x.val.1 (Fin.last l)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem augmentation_zero_iff (x : rightTerm (k := k) (Fin.last l)) :
    augmentation k l x = 0 ↔ x.val.1 (Fin.last l) = 0 := Iff.rfl

/-- Exactness at the augmentation for every positive chain length. -/
theorem augmentation_exact (x : rightTerm (k := k) (Fin.last (l+1))) :
    augmentation k (l+1) x = 0 ↔
      ∃ y, resolutionMap (k := k) (Fin.last l) y = x := by
  rw [augmentation_zero_iff, resolutionMap_range]
  rfl

theorem augmentation_zero_injective : Function.Injective (augmentation k 0) := by
  intro x y hxy
  have hz : (x-y).val.1 0 = 0 := by
    have hz : augmentation k 0 (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    exact (augmentation_zero_iff k 0 _).mp hz
  have he := vertex_zero_mul (x-y).val
  have hp : vertex k 0 0 * (x-y).val = (x-y).val := (x-y).property
  rw [hp, hz, zero_smul] at he
  exact sub_eq_zero.mp (show x-y = 0 from Subtype.ext he)

end ChainAlgebra
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryResolutionComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- Extending the source idempotents by zero keeps all right ideals in the same C. -/
def extendedVertex (n : ℕ) : ChainAlgebra k l :=
  if h : n ≤ l then vertex k l ⟨n,by omega⟩ else 0

def extendedArrow (n : ℕ) : ChainAlgebra k l :=
  if h : n < l then arrow k l ⟨n,h⟩ else 0

theorem extendedVertex_idempotent (n : ℕ) :
    extendedVertex k l n * extendedVertex k l n = extendedVertex k l n := by
  unfold extendedVertex
  split
  · exact vertex_idempotent k l _
  · exact zero_mul _

theorem extendedArrow_target (n : ℕ) :
    extendedVertex k l (n+1) * extendedArrow k l n = extendedArrow k l n := by
  by_cases h : n < l
  · have h1 : n+1 ≤ l := by omega
    simp only [extendedVertex, extendedArrow, dite_eq_left h, dite_eq_left h1]
    exact vertex_target_arrow k l ⟨n,h⟩
  · rw [extendedArrow, dite_eq_right h, mul_zero]

theorem extendedArrow_square (n : ℕ) : extendedArrow k l (n+1) * extendedArrow k l n = 0 := by
  by_cases h1 : n+1 < l
  · have h0 : n < l := by omega
    simp only [extendedArrow, dite_eq_left h1, dite_eq_left h0, arrow_mul_arrow]
  · rw [extendedArrow, dite_eq_right h1, zero_mul]

abbrev resolutionIdeal (n : ℕ) := IdempotentTensor.rightIdeal (extendedVertex k l n)
abbrev resolutionTerm (n : ℕ) : ModuleCat.{u} (ChainAlgebra k l)ᵐᵒᵖ :=
  ModuleCat.of _ (resolutionIdeal k l n)

/-- Actual left-arrow differentials, with no transport of module types. -/
def resolutionDifferential (n : ℕ) : resolutionTerm k l n ⟶ resolutionTerm k l (n+1) :=
  ModuleCat.ofHom (((leftMultiply (extendedArrow k l n)).comp (resolutionIdeal k l n).subtype).codRestrict _
    (fun x => by
      change extendedVertex k l (n+1) * (extendedArrow k l n * x.val) = extendedArrow k l n * x.val
      rw [← mul_assoc, extendedArrow_target]))

theorem resolutionDifferential_square (n : ℕ) :
    resolutionDifferential k l n ≫ resolutionDifferential k l (n+1) = 0 := by
  ext x
  change extendedArrow k l (n+1) * (extendedArrow k l n * x.val) = 0
  rw [← mul_assoc, extendedArrow_square, zero_mul]

end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryResolutionExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_add _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_arrow _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_one _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_zero _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.right_action _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- In the supported range, the extended ideal is the source's actual right projective. -/
def supportedIdealEquiv (n : ℕ) (h : n ≤ l) :
    resolutionIdeal k l n ≃ₗ[(ChainAlgebra k l)ᵐᵒᵖ] rightTerm (k := k) (⟨n,by omega⟩ : Fin (l+1)) where
  toFun x := ⟨x.val, by
    have hp := x.property
    change extendedVertex k l n * x.val = x.val at hp
    change vertex k l ⟨n,by omega⟩ * x.val = x.val
    simpa only [extendedVertex, dite_eq_left h] using hp⟩
  invFun x := ⟨x.val, by
    change extendedVertex k l n * x.val = x.val
    rw [extendedVertex, dite_eq_left h]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem supportedIdealEquiv_d (n : ℕ) (h : n < l) (x : resolutionIdeal k l n) :
    supportedIdealEquiv k l (n+1) (by omega) ((resolutionDifferential k l n).hom x) =
      resolutionMap (k := k) ⟨n,h⟩ (supportedIdealEquiv k l n (by omega) x) := by
  apply Subtype.ext
  change extendedArrow k l n * x.val = arrow k l ⟨n,h⟩ * x.val
  rw [extendedArrow, dite_eq_left h]

/-- The actual bundled complex is exact at every interior degree. -/
theorem supported_complex_exact (n : ℕ) (h : n+1 < l) :
    (ShortComplex.mk (resolutionDifferential k l n) (resolutionDifferential k l (n+1))
      (resolutionDifferential_square k l n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (supportedIdealEquiv k l (n+2) (by omega)) hx
  rw [supportedIdealEquiv_d k l (n+1) h, map_zero] at hx'
  obtain ⟨y,hy⟩ := (resolution_exact (k := k) n h (supportedIdealEquiv k l (n+1) (by omega) x)).mp hx'
  refine ⟨(supportedIdealEquiv k l n (by omega)).symm y, ?_⟩
  apply (supportedIdealEquiv k l (n+1) (by omega)).injective
  rw [supportedIdealEquiv_d k l n (by omega), LinearEquiv.apply_symm_apply, hy]

/-- The actual augmentation of the bundled complex in its last degree. -/
def resolutionAugmentation : resolutionTerm k l l ⟶ ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) :=
  ModuleCat.ofHom ((augmentation k l).comp (supportedIdealEquiv k l l le_rfl).toLinearMap)

end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryResolutionQuasiIso
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

theorem resolutionInitial_injective (h : 0 < l) :
    Function.Injective (resolutionDifferential k l 0).hom := by
  intro x y hxy
  apply (supportedIdealEquiv k l 0 (by omega)).injective
  apply resolution_first_injective (k := k) h
  rw [← supportedIdealEquiv_d k l 0 h, ← supportedIdealEquiv_d k l 0 h, hxy]

theorem resolutionAugmentation_comp (n : ℕ) :
    resolutionDifferential k (n+1) n ≫ resolutionAugmentation k (n+1) = 0 := by
  ext x
  change (extendedArrow k (n+1) n * x.val).1 (Fin.last (n+1)) = (0:k)
  rw [extendedArrow, dite_eq_left (by omega), mul_diagonal, arrow_diagonal, zero_mul]

theorem resolutionAugmentation_exact (n : ℕ) :
    (ShortComplex.mk (resolutionDifferential k (n+1) n) (resolutionAugmentation k (n+1))
      (resolutionAugmentation_comp k n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : augmentation k (n+1) (supportedIdealEquiv k (n+1) (n+1) le_rfl x) = 0 := hx
  obtain ⟨y,hy⟩ := (augmentation_exact k n _).mp hx'
  refine ⟨(supportedIdealEquiv k (n+1) n (by omega)).symm y, ?_⟩
  apply (supportedIdealEquiv k (n+1) (n+1) le_rfl).injective
  rw [supportedIdealEquiv_d k (n+1) n (by omega), LinearEquiv.apply_symm_apply]
  exact hy

theorem resolutionAugmentation_zero_injective :
    Function.Injective (resolutionAugmentation k 0).hom :=
  (augmentation_zero_injective k).comp (supportedIdealEquiv k 0 0 le_rfl).injective

end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)
namespace TensorResolution
open ChainAlgebra

abbrev term (n : ℕ) := IdempotentTensor.rightIdeal
  (TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n))

def termEquiv (n : ℕ) : B ⊗[k] resolutionIdeal k l n ≃ₗ[k] term k B l n :=
  TensorIdeal.equivalence _ (extendedVertex_idempotent k l n)

def regularEquiv : (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
    B ⊗[k] ChainAlgebra k l where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leftMultiply (x : B ⊗[k] ChainAlgebra k l) :
    B ⊗[k] ChainAlgebra k l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] B ⊗[k] ChainAlgebra k l where
  toFun y := x*y
  map_add' := mul_add x
  map_smul' r y := (mul_assoc x y r.unop).symm

/-- The B-extended resolution differential is left multiplication by 1 tensor c. -/
def differential (n : ℕ) : term k B l n →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] term k B l (n+1) :=
  ((leftMultiply k B l ((1:B) ⊗ₜ[k] extendedArrow k l n)).comp (term k B l n).subtype).codRestrict _ (fun x => by
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l (n+1)) *
      (((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val) = ((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val
    rw [← mul_assoc]
    congr 1
    simp only [TensorIdeal.vertex,Algebra.TensorProduct.tmul_mul_tmul,one_mul,extendedArrow_target])

theorem differential_square (n : ℕ) : (differential k B l (n+1)).comp (differential k B l n) = 0 := by
  ext x
  change ((1:B) ⊗ₜ[k] extendedArrow k l (n+1)) * (((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val) = 0
  rw [← mul_assoc,Algebra.TensorProduct.tmul_mul_tmul,extendedArrow_square,TensorProduct.tmul_zero,zero_mul]

theorem termEquiv_d (n : ℕ) (z : B ⊗[k] resolutionIdeal k l n) :
    termEquiv k B l (n+1) (((resolutionDifferential k l n).hom.restrictScalars k).lTensor B z) =
      differential k B l n (termEquiv k B l n z) := by
  induction z using OAI.tensorInductionOn with
  | tmul b c =>
    apply Subtype.ext
    change b ⊗ₜ[k] (extendedArrow k l n * c.val) =
      ((1:B) ⊗ₜ[k] extendedArrow k l n) * (b ⊗ₜ[k] c.val)
    rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Every interior exact sequence stays exact after the actual B-extension over k. -/
theorem differential_exact (n : ℕ) (hn : n+1 < l) :
    Function.Exact (differential k B l n) (differential k B l (n+1)) := by
  have hc : Function.Exact ((resolutionDifferential k l n).hom.restrictScalars k)
      ((resolutionDifferential k l (n+1)).hom.restrictScalars k) := by
    intro x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp (supported_complex_exact k l n hn) x hx
    · rintro ⟨y,rfl⟩
      have h := congrArg (fun f => f.hom y) (resolutionDifferential_square k l n)
      exact h
  have ht := Module.Flat.lTensor_exact B hc
  intro x
  constructor
  · intro hx
    have hzero : (((resolutionDifferential k l (n+1)).hom.restrictScalars k).lTensor B)
        ((termEquiv k B l (n+1)).symm x) = 0 := by
      apply (termEquiv k B l (n+2)).injective
      rw [termEquiv_d,LinearEquiv.apply_symm_apply,hx,map_zero]
    obtain ⟨y,hy⟩ := (ht _).mp hzero
    refine ⟨termEquiv k B l n y, ?_⟩
    rw [← termEquiv_d,hy,LinearEquiv.apply_symm_apply]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (differential_square k B l n)
end TensorResolution
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorAugmentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

instance TerminalSimple.tower : IsScalarTower k (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) where
  smul_assoc r x w := by
    change (show k from w) * (r * (ChainAlgebra.terminalCharacter k l x.unop)) =
      r * ((show k from w) * ChainAlgebra.terminalCharacter k l x.unop)
    ring

namespace TensorResolution
open ChainAlgebra

def simpleCoordinates : TerminalSimple k ≃ₗ[k] k where
  toFun w := w
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def terminalEquiv : B ⊗[k] TerminalSimple k ≃ₗ[k] TerminalTensor B :=
  (TensorProduct.congr (LinearEquiv.refl k B) (simpleCoordinates k)).trans (TerminalTensor.tensorModel k B)

/-- The augmentation retains the actual right BC-action. -/
def augmentation : term k B l l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] TerminalTensor B where
  toFun x := terminalAugmentation k B l x.val
  map_add' x y := map_add _ x.val y.val
  map_smul' r x := map_mul (terminalAugmentation k B l) x.val r.unop

/-- The ordinary augmentation is exactly B tensor the terminal C-augmentation. -/
theorem augmentation_tensor (z : B ⊗[k] resolutionIdeal k l l) :
    augmentation k B l (termEquiv k B l l z) =
      terminalEquiv k B (((resolutionAugmentation k l).hom.restrictScalars k).lTensor B z) := by
  induction z using OAI.tensorInductionOn with
  | tmul b c =>
    change b * algebraMap k B (c.val.1 (Fin.last l)) = (c.val.1 (Fin.last l)) • b
    rw [Algebra.smul_def,Algebra.commutes]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The augmentation preserves the regular left B-action as well. -/
theorem augmentation_left (b : B) (x : term k B l l) :
    augmentation k B l (b • x) = b • augmentation k B l x := by
  change terminalAugmentation k B l (TensorIdeal.coefficient b * x.val) =
    b * terminalAugmentation k B l x.val
  rw [map_mul]
  congr 1
  change b * algebraMap k B (ChainAlgebra.terminalCharacter k l 1) = b
  rw [map_one,map_one,mul_one]

theorem augmentation_comp (n : ℕ) :
    (augmentation k B (n+1)).comp (differential k B (n+1) n) = 0 := by
  ext x
  change terminalAugmentation k B (n+1) (((1:B) ⊗ₜ[k] extendedArrow k (n+1) n) * x.val) = 0
  rw [map_mul]
  have hz : terminalAugmentation k B (n+1) ((1:B) ⊗ₜ[k] extendedArrow k (n+1) n) = 0 := by
    rw [extendedArrow,dite_eq_left (by omega)]
    change 1 * algebraMap k B ((arrow k (n+1) ⟨n,by omega⟩).1 (Fin.last (n+1))) = 0
    rw [arrow_diagonal,map_zero,mul_zero]
  rw [hz,zero_mul]

theorem augmentation_exact (n : ℕ) :
    Function.Exact (differential k B (n+1) n) (augmentation k B (n+1)) := by
  have hc : Function.Exact ((resolutionDifferential k (n+1) n).hom.restrictScalars k)
      ((resolutionAugmentation k (n+1)).hom.restrictScalars k) := by
    intro x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp (resolutionAugmentation_exact k n) x hx
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f => f.hom y) (resolutionAugmentation_comp k n)
  have ht := Module.Flat.lTensor_exact B hc
  intro x
  constructor
  · intro hx
    have hz : (((resolutionAugmentation k (n+1)).hom.restrictScalars k).lTensor B)
        ((termEquiv k B (n+1) (n+1)).symm x) = 0 := by
      apply (terminalEquiv k B).injective
      rw [← augmentation_tensor,LinearEquiv.apply_symm_apply,hx,map_zero]
    obtain ⟨y,hy⟩ := (ht _).mp hz
    refine ⟨termEquiv k B (n+1) n y, ?_⟩
    rw [← termEquiv_d,hy,LinearEquiv.apply_symm_apply]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (augmentation_comp k B n)

/-- Surjectivity is explicit: the terminal vertex lifts every coefficient b. -/
theorem augmentation_surjective : Function.Surjective (augmentation k B l) := by
  intro b
  let x : term k B l l := ⟨(show B from b) ⊗ₜ[k] vertex k l (Fin.last l), by
    change ((1:B) ⊗ₜ[k] extendedVertex k l l) * _ = _
    rw [extendedVertex,dite_eq_left le_rfl]
    have hi : (⟨l,by omega⟩ : Fin (l+1)) = Fin.last l := rfl
    rw [hi,Algebra.TensorProduct.tmul_mul_tmul,one_mul,vertex_idempotent]⟩
  refine ⟨x, ?_⟩
  change (show B from b) * algebraMap k B ((vertex k l (Fin.last l)).1 (Fin.last l)) = (show B from b)
  rw [vertex_diagonal,Pi.single_eq_same,map_one,mul_one]

theorem initial_injective (h : 0 < l) : Function.Injective (differential k B l 0) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    ((resolutionDifferential k l 0).hom.restrictScalars k) (resolutionInitial_injective k l h) (M := B)
  intro x y hxy
  apply (termEquiv k B l 0).symm.injective
  apply hi
  apply (termEquiv k B l 1).injective
  rw [termEquiv_d,termEquiv_d,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hxy]

theorem augmentation_zero_injective : Function.Injective (augmentation k B 0) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    ((resolutionAugmentation k 0).hom.restrictScalars k) (resolutionAugmentation_zero_injective k) (M := B)
  intro x y hxy
  apply (termEquiv k B 0 0).symm.injective
  apply hi
  apply (terminalEquiv k B).injective
  rw [← augmentation_tensor,← augmentation_tensor,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hxy]
end TensorResolution
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorResolutionComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev termObject (n : ℕ) : ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ := ModuleCat.of _ (term k B l n)

def complex : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ℕ :=
  CochainComplex.of (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n))
    (fun n => by apply ModuleCat.hom_ext; exact differential_square k B l n)

theorem term_vanishes (n : ℕ) (h : l < n) : IsZero (termObject k B l n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (x : term k B l n) : x = 0 := by
    apply Subtype.ext
    have hp := x.property
    change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedVertex k l n) * x.val = x.val at hp
    rw [ChainAlgebra.extendedVertex,dite_eq_right (Nat.not_le.mpr h),TensorProduct.tmul_zero,zero_mul] at hp
    exact hp.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Every differential preserves the regular left B-action. -/
theorem differential_left (n : ℕ) (b : B) (x : term k B l n) :
    differential k B l n (b • x) = b • differential k B l n x := by
  apply Subtype.ext
  change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * (TensorIdeal.coefficient b * x.val) =
    TensorIdeal.coefficient b * (((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * x.val)
  rw [← mul_assoc,← mul_assoc]
  congr 1
  simp only [TensorIdeal.coefficient,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

theorem complex_exactAt (n : ℕ) (hn : n ≠ l) : (complex k B l).ExactAt n := by
  by_cases h : l < n
  · exact HomologicalComplex.ExactAt.of_isZero (term_vanishes k B l n h)
  have hnl : n < l := by omega
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : differential k B l 0 x = 0 := by
      change ((complex k B l).d 0 ((ComplexShape.up ℕ).next 0)).hom x = 0 at hx
      rw [show (ComplexShape.up ℕ).next 0 = 1 by simp] at hx
      change (CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) 0 (0+1)).hom x = 0 at hx
      rw [CochainComplex.of_d] at hx
      exact hx
    have hx0 : x = 0 := initial_injective k B l hnl (hx'.trans (map_zero _).symm)
    exact ⟨0, by simp only [hx0,map_zero]⟩
  | succ n =>
    apply (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).2
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : differential k B l (n+1) x = 0 := by
      change (CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) (n+1) ((n+1)+1)).hom x = 0 at hx
      rw [CochainComplex.of_d] at hx
      exact hx
    obtain ⟨y,hy⟩ := (differential_exact k B l n hnl x).mp hx'
    refine ⟨y, ?_⟩
    change (CochainComplex.of.d (termObject k B l)
      (fun j => ModuleCat.ofHom (differential k B l j)) n (n+1)).hom y = x
    rw [CochainComplex.of_d]
    exact hy

abbrev augmentationHom : termObject k B l l ⟶ ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) :=
  ModuleCat.ofHom (augmentation k B l)

instance augmentation_epi : Epi (augmentationHom k B l) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k B l)

/-- The actual B-extended resolution augmentation as a chain map. -/
def augmentationMap : complex k B l ⟶
    (HomologicalComplex.single _ (.up ℕ) l).obj (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) :=
  HomologicalComplex.mkHomToSingle (augmentationHom k B l) (by
    intro i hi
    change i+1=l at hi
    subst l
    change CochainComplex.of.d _ _ i (i+1) ≫ augmentationHom k B (i+1) = 0
    rw [CochainComplex.of_d]
    ext x
    exact congrArg (fun f => f x) (augmentation_comp k B i))

theorem differential_last_zero : differential k B l l = 0 := by
  ext x
  change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l l) * x.val = 0
  rw [ChainAlgebra.extendedArrow,dite_eq_right (lt_irrefl l),TensorProduct.tmul_zero,zero_mul]

theorem augmentationMap_quasiIsoAt_last : QuasiIsoAt (augmentationMap k B l) l := by
  rw [quasiIsoAt_iff]
  refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ?_
  · change (complex k B l).d l ((ComplexShape.up ℕ).next l) = 0
    rw [show (ComplexShape.up ℕ).next l = l+1 by simp]
    change CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) l (l+1) = 0
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact differential_last_zero k B l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) ((ComplexShape.up ℕ).prev l) l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) l ((ComplexShape.up ℕ).next l)
  · change (ShortComplex.mk ((complex k B l).d ((ComplexShape.up ℕ).prev l) l)
      ((augmentationMap k B l).f l) _).Exact ∧ Epi ((augmentationMap k B l).f l)
    have hf : (augmentationMap k B l).f l = augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv := by
      unfold augmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    simp only [hf]
    constructor
    · refine ChainAlgebra.exact_post_iso _ _ ?_
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).symm ?_
      · cases l with
        | zero =>
          have hz := (complex k B 0).shape ((ComplexShape.up ℕ).prev 0) 0 (by simp)
          erw [hz,zero_comp]
        | succ n =>
          rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
          change CochainComplex.of.d _ _ n (n+1) ≫ augmentationHom k B (n+1) = 0
          rw [CochainComplex.of_d]
          ext x
          exact congrArg (fun f => f x) (augmentation_comp k B n)
      cases l with
      | zero =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx0 : x = 0 := augmentation_zero_injective k B (hx.trans (map_zero _).symm)
        exact ⟨0, by simp only [hx0,map_zero]⟩
      | succ n =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨y,hy⟩ := (augmentation_exact k B n x).mp hx
        change ∃ z : termObject k B (n+1) ((ComplexShape.up ℕ).prev (n+1)),
          (CochainComplex.of.d (termObject k B (n+1))
            (fun j => ModuleCat.ofHom (differential k B (n+1) j))
            ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom z = x
        rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
        exact ⟨y, by rw [CochainComplex.of_d]; exact hy⟩
    · erw [ModuleCat.epi_iff_surjective]
      exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv)).comp
        (augmentation_surjective k B l)

/-- Actual augmentation quasi-isomorphism for the finite right-BC-projective resolution. -/
theorem augmentationMap_quasiIso : QuasiIso (augmentationMap k B l) := by
  constructor
  intro n
  by_cases hn : n = l
  · subst n; exact augmentationMap_quasiIsoAt_last k B l
  · apply (quasiIsoAt_iff_exactAt' _ n ?_).2 (complex_exactAt k B l n hn)
    exact HomologicalComplex.ExactAt.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryIntegerResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- Q_T in the manuscript's cohomological degrees -l,...,0. -/
def integerComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ℤ :=
  (complex k B l).extend (degreeEmbedding l)

theorem integerTerm_lower (n : ℤ) (h : n < -(l:ℤ)) : IsZero ((integerComplex k B l).X n) := by
  apply (complex k B l).isZero_extend_X (degreeEmbedding l) n
  intro j hj
  simp only [degreeEmbedding_apply] at hj
  omega

theorem integerTerm_upper (n : ℤ) (h : 0 < n) : IsZero ((integerComplex k B l).X n) := by
  let j := (n+(l:ℤ)).toNat
  have hj : (degreeEmbedding l).f j = n := by
    simp only [degreeEmbedding_apply]
    dsimp [j]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hjl : l < j := by
    have hc : (j:ℤ) = n+(l:ℤ) := Int.toNat_of_nonneg (by omega)
    omega
  exact (term_vanishes k B l j hjl).of_iso ((complex k B l).extendXIso (degreeEmbedding l) hj)

end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimoduleResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev bimoduleTerm (n : ℕ) := RetainedBimodule k B (B ⊗[k] ChainAlgebra k l) (term k B l n)

def bimoduleDifferential (n : ℕ) :=
  RetainedBimodule.map (k := k) (S := B) (A := B ⊗[k] ChainAlgebra k l) (differential k B l n) (differential_left k B l n)

theorem bimoduleDifferential_square (n : ℕ) :
    (bimoduleDifferential k B l (n+1)).comp (bimoduleDifferential k B l n) = 0 := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun f => f x) (differential_square k B l n)

/-- The actual finite resolution retains the left B-action as a genuine tensor-algebra complex. -/
def bimoduleComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of _ (bimoduleTerm k B l n))
    (fun n => ModuleCat.ofHom (bimoduleDifferential k B l n))
    (fun n => ModuleCat.hom_ext (bimoduleDifferential_square k B l n))

abbrev forgetBimodule : ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ⥤
    ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ :=
  ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)).toRingHom

end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAugmentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev bimoduleTerminal := RetainedBimodule k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B)
abbrev bimoduleTerminalObject : ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) :=
  ModuleCat.of _ (bimoduleTerminal k B l)

def bimoduleAugmentationHom : (bimoduleComplex k B l).X l ⟶ bimoduleTerminalObject k B l :=
  ModuleCat.ofHom (RetainedBimodule.map (k := k) (S := B) (A := B ⊗[k] ChainAlgebra k l)
    (augmentation k B l) (augmentation_left k B l))

/-- The actual augmentation of the genuine finite bimodule resolution. -/
def bimoduleAugmentationMap : bimoduleComplex k B l ⟶
    (HomologicalComplex.single _ (.up ℕ) l).obj (bimoduleTerminalObject k B l) :=
  HomologicalComplex.mkHomToSingle (bimoduleAugmentationHom k B l) (by
    intro i hi
    change i+1=l at hi
    subst l
    change CochainComplex.of.d _ _ i (i+1) ≫ bimoduleAugmentationHom k B (i+1) = 0
    erw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f x) (augmentation_comp k B i))

end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimoduleComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

namespace VertexTensor
variable (i : Fin (l+1))

attribute [local instance] OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.termScalar
attribute [local instance] OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.termTower
/-- The original enveloping-algebra action is the two original B-actions. -/
theorem enveloping_smul (b : B) (r : Bᵐᵒᵖ) (v : BimoduleO P a l) :
    (b ⊗ₜ[k] r : Enveloping k B) • v = b • (r • v) := by
  change (b ⊗ₜ[k] r : Enveloping k B) • (v : Compression P a l) =
    (b ⊗ₜ[k] (1:Bᵐᵒᵖ)) • (((1:B) ⊗ₜ[k] r) • (v : Compression P a l))
  rw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

theorem evaluation_tmul_smul (b : B) (r : Bᵐᵒᵖ) (z : VertexTensor P a l i) :
    evaluation P a l i ((b ⊗ₜ[k] r) • z) =
      (b ⊗ₜ[k] r : Enveloping k B) • (evaluation P a l i z : P.X (a+(i.val:ℤ))) := by
  have h : (evaluation P a l i).toLinearMap.comp (action P a l i (b ⊗ₜ[k] r)) =
      (Algebra.lsmul k k (P.X (a+(i.val:ℤ))) (b ⊗ₜ[k] r : Enveloping k B)).comp
        (evaluation P a l i).toLinearMap := by
    apply BalancedTensor.ext
    intro m v
    change evaluation P a l i ((b ⊗ₜ[k] r) • mk P a l i m v) =
      (b ⊗ₜ[k] r : Enveloping k B) • evaluation P a l i (mk P a l i m v)
    rw [action_tmul_mk, evaluation_mk, evaluation_mk]
    change (((TensorIdeal.coefficient b * m.val) • (r • v)) : BimoduleO P a l) i = _
    have hv : (TensorIdeal.coefficient b * m.val) • (r • v) =
        (b ⊗ₜ[k] r : Enveloping k B) • (m.val • v) := by
      rw [mul_smul, smul_comm m.val r]
      change (b ⊗ₜ[k] (1:ChainAlgebra k l)) • (r • (m.val • v)) = _
      rw [BimoduleO.tensor_smul, one_smul, ← enveloping_smul]
    exact congrArg (fun w : BimoduleO P a l => w i) hv
  exact congrArg (fun f => f z) h

theorem evaluation_smul (x : Enveloping k B) (z : VertexTensor P a l i) :
    evaluation P a l i (x • z) = x • (evaluation P a l i z : P.X (a+(i.val:ℤ))) := by
  induction x using OAI.tensorInductionOn with
  | tmul b r => exact evaluation_tmul_smul P a l i b r z
  | add x y hx hy => simp only [add_smul,map_add,hx,hy]

/-- Degreewise comparison as a genuine B-bimodule equivalence. -/
def bimoduleEquiv : VertexTensor P a l i ≃ₗ[Enveloping k B] P.X (a+(i.val:ℤ)) where
  __ := (evaluation P a l i).toAddEquiv
  map_smul' x z := evaluation_smul P a l i x z
end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
namespace VertexTensor

attribute [local instance] termScalar termTower

theorem arrow_coordinate (i : Fin l) (v : BimoduleO P a l) :
    (ChainAlgebra.arrow k l i • v : BimoduleO P a l) i.succ =
      (P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom (v i.castSucc) := by
  have h := OrdinaryTerms.action_arrow
    (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) i v
  have h' := congrArg (fun w => w i.succ) h
  change OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) (ChainAlgebra.arrow k l i) v i.succ =
      intervalDifferential (underlyingComplex (k := k) P) a l i.castSucc i.succ (v i.castSucc)
  simpa only [Pi.single_eq_same] using h'

end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFullTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

instance BimoduleO.commuteRightTensor : SMulCommClass Bᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
  ⟨fun r x v => (smul_comm x r v).symm⟩

/-- Every degree of Q_T tensor_BC O, carrying the actual outside B-actions. -/
abbrev FullTensorTerm (n : ℕ) := TwoSidedTensor k (B ⊗[k] ChainAlgebra k l) B Bᵐᵒᵖ
  (TensorResolution.term k B l n) (BimoduleO P a l)

namespace FullTensorTerm
open ChainAlgebra

/-- Supported extended ideals are the same right ideals as the finite vertex terms. -/
def supportedIdealEquiv (n : ℕ) (hn : n ≤ l) :
    TensorResolution.term k B l n ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (vertex k l ⟨n,by omega⟩)) where
  toFun x := ⟨x.val, by
    have hx := x.property
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n) * x.val = x.val at hx
    rw [extendedVertex,dite_eq_left hn] at hx
    exact hx⟩
  invFun x := ⟨x.val, by
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n) * x.val = x.val
    rw [extendedVertex,dite_eq_left hn]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteModel (i : Fin (l+1)) :
    TwoSidedTensor k (B ⊗[k] ChainAlgebra k l) B Bᵐᵒᵖ
      (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (vertex k l i)))
      (BimoduleO P a l) ≃ₗ[Enveloping k B] VertexTensor P a l i where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual degreewise B-bimodule comparison throughout the supported range. -/
def supportedEquiv (n : ℕ) (hn : n ≤ l) : FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) :=
  (TwoSidedTensor.congrLeft (k := k) (S := B) (T := Bᵐᵒᵖ) (N := BimoduleO P a l)
    (supportedIdealEquiv (k := k) (B := B) l n hn) (fun _ _ => rfl)).trans
      ((finiteModel P a l ⟨n,by omega⟩).trans (VertexTensor.bimoduleEquiv P a l ⟨n,by omega⟩))

theorem subsingleton_above (n : ℕ) (hn : l < n) : Subsingleton (FullTensorTerm P a l n) := by
  let : Subsingleton (TensorResolution.term k B l n) :=
    (ModuleCat.isZero_iff_subsingleton).mp (TensorResolution.term_vanishes k B l n hn)
  exact inferInstanceAs (Subsingleton (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
    (TensorResolution.term k B l n) (BimoduleO P a l)))

/-- Use precisely the source's upper support bound for all remaining degrees. -/
def outsideEquiv (n : ℕ) (hn : l < n) (hP : IsZero (P.X (a+(n:ℤ)))) :
    FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) := by
  letI := subsingleton_above P a l n hn
  letI : Subsingleton (P.X (a+(n:ℤ))) := ModuleCat.isZero_iff_subsingleton.mp hP
  exact { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _
          map_add' := fun _ _ => Subsingleton.elim _ _
          map_smul' := fun _ _ => Subsingleton.elim _ _ }

/-- No extra support assumptions: P is required to vanish only above a+l here. -/
def termEquiv (hP : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ)))) (n : ℕ) :
    FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) :=
  if hn : n ≤ l then supportedEquiv P a l n hn else outsideEquiv P a l n (by omega) (hP n (by omega))
end FullTensorTerm
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFullTensorComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.FullTensorTerm
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
attribute [local instance] VertexTensor.termScalar VertexTensor.termTower

def differential (n : ℕ) : FullTensorTerm P a l n →ₗ[Enveloping k B] FullTensorTerm P a l (n+1) :=
  TwoSidedTensor.map (T := Bᵐᵒᵖ) (N := BimoduleO P a l)
    (TensorResolution.differential k B l n) (TensorResolution.differential_left k B l n)

theorem differential_square (n : ℕ) : (differential P a l (n+1)).comp (differential P a l n) = 0 := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro m v
  change BalancedTensor.mk k (B ⊗[k] ChainAlgebra k l) (TensorResolution.term k B l (n+2))
    (BimoduleO P a l) (TensorResolution.differential k B l (n+1)
      (TensorResolution.differential k B l n m)) v = 0
  have h := congrArg (fun f => f m) (TensorResolution.differential_square k B l n)
  change TensorResolution.differential k B l (n+1) (TensorResolution.differential k B l n m) = 0 at h
  rw [h,map_zero,LinearMap.zero_apply]

/-- Actual tensor complex, with both B-actions and the actual extended arrow maps. -/
def complex : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of _ (FullTensorTerm P a l n))
    (fun n => ModuleCat.ofHom (differential P a l n))
    (fun n => ModuleCat.hom_ext (differential_square P a l n))

theorem supported_differential (n : ℕ) (hn : n+1 ≤ l) (z : FullTensorTerm P a l n) :
    supportedEquiv P a l (n+1) hn (differential P a l n z) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom (supportedEquiv P a l n (by omega) z) := by
  have h : (supportedEquiv P a l (n+1) hn).toLinearMap.comp (differential P a l n) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom.comp
        (supportedEquiv P a l n (by omega)).toLinearMap := by
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m v
    change ((((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * m.val) • v : BimoduleO P a l) ⟨n+1,by omega⟩ =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom ((m.val • v : BimoduleO P a l) ⟨n,by omega⟩)
    have hv : (((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * m.val) • v =
        ChainAlgebra.arrow k l ⟨n,by omega⟩ • (m.val • v) := by
      rw [mul_smul,BimoduleO.tensor_smul,one_smul,ChainAlgebra.extendedArrow,dite_eq_left (by omega)]
    exact (congrArg (fun w : BimoduleO P a l => w ⟨n+1,by omega⟩) hv).trans
      (VertexTensor.arrow_coordinate P a l ⟨n,by omega⟩ (m.val • v))
  exact congrArg (fun f => f z) h

variable (hP : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ))))

theorem termEquiv_differential (n : ℕ) (z : FullTensorTerm P a l n) :
    termEquiv P a l hP (n+1) (differential P a l n z) =
      (P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ))).hom (termEquiv P a l hP n z) := by
  by_cases hn : n+1 ≤ l
  · simp only [termEquiv,dite_eq_left hn,dite_eq_left (show n ≤ l by omega)]
    exact supported_differential P a l n hn z
  · let : Subsingleton (P.X (a+((n+1:ℕ):ℤ))) :=
      ModuleCat.isZero_iff_subsingleton.mp (hP (n+1) (by omega))
    exact Subsingleton.elim _ _

/-- The entire actual tensor complex identifies with P on degrees a,a+1,... . -/
def complexIso : complex P a l ≅ P.restriction (ComplexShape.embeddingUpIntGE a) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (termEquiv P a l hP n).toModuleIso) (by
    intro n m hnm
    change n+1=m at hnm
    subst m
    change (termEquiv P a l hP n).toModuleIso.hom ≫ P.d (a+(n:ℤ)) (a+((n+1:ℕ):ℤ)) =
      CochainComplex.of.d (fun j => ModuleCat.of (Enveloping k B) (FullTensorTerm P a l j))
        (fun j => ModuleCat.ofHom (differential P a l j)) n (n+1) ≫ (termEquiv P a l hP (n+1)).toModuleIso.hom
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (termEquiv_differential P a l hP n z).symm)
end LittleFinitistic.OrdinarySimulation.FullTensorTerm

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySimulationComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The computed BC-balanced tensor complex in degrees -l,...,0 with both B-actions. -/
def computedTensorComplex : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ :=
  (FullTensorTerm.complex P a l).extend (TensorResolution.degreeEmbedding l)

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedRectification
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Termwise projectivity holds for the actual right restriction of the total. -/
theorem rightTotal_projective
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) :
    ∀ n, Projective ((rightTotal s D₀ D₁ D₂ f g H).X n) := by
  have hc := columns_right_projective s D₀ D₁ D₂ f g h₀ h₁ h₂
  exact RectificationTotal.total_projective_after _ _ _ (forgetRight k B)
    (fun n => (hc n).1) (fun n => (hc n).2.1) (fun n => (hc n).2.2)

end LittleFinitistic.InducedRectification

end

end OAI
end


