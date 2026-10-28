-- Prove2me | Definitions.Def_OAIQ031A164
-- name    : OAIQ031A164
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:12:40.395614+00:00
-- url     : https://prove2.me/theorems/510d38e2-7363-4869-accf-f53b132306eb
-- title:
--   Definitions bundle OAIQ031A164 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 6 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.T.endpointCoordinates`, `OAI.ArExplicit.T.endpointEvaluation`, `OAI.ArExplicit.T.finiteSourceTop`, `OAI.ArExplicit.T.finiteTargetTop`, `OAI.ArExplicit.T.normalizedSourceTop`, `OAI.ArExplicit.T.topFourShiftIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_TensorFiniteTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteTop.lean), [`AuslanderReiten_Coordinates_TensorNormalizedTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorNormalizedTop.lean), [`AuslanderReiten_Evaluation_ConcreteEndpointCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEndpointCoordinates.lean), [`AuslanderReiten_Evaluation_ConcreteEndpointInsertion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEndpointInsertion.lean), [`AuslanderReiten_Evaluation_TensorTwistEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorTwistEvaluation.lean), [`AuslanderReiten_Resolutions_EvaluatedResolutionTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/EvaluatedResolutionTerms.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A159` and `OAIQ031A160` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A168`, `OAIQ031A169` and `OAIQ031A170`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A159
import Definitions.Def_OAIQ031A160

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteTop
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "τ" => AEnvelopingFrobeniusTrace k q
local notation "hD" => bimodule_term_finite_k q

def topFourShiftIso := iteratedShiftIso (fun n => TwoCone.baseResolution D hD τ (n+1))
  (fun n => TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q)
    (bimodule_term_projective q) (n+1)) 4

theorem sourceFourthToTail_top :
    (TwoCone.topCokernelMap D 1).comp (sourceFourthToTail q H) = bimoduleTopCokernel q H 4 := by
  apply LinearMap.ext
  intro x
  change TwoCone.topCokernelMap D 1 (tailMap q H ((sourceFourthEquiv q H).symm x)) = _
  calc
    _ = topSyzygyMap q H ((sourceFourthEquiv q H).symm x) :=
      LinearMap.congr_fun (tailMap_top q H) _
    _ = bimoduleTopCokernel q H 4
        ((sourceFourthEquiv q H) ((sourceFourthEquiv q H).symm x)) :=
      (LinearMap.congr_fun (bimoduleTopCokernel_four q H) _).symm
    _ = bimoduleTopCokernel q H 4 x := by rw [LinearEquiv.apply_symm_apply]

def finiteTargetTop :
    (HomotopyCategory.quotient _ _).obj
      (((firstTailModule q).canonicalCosyzygies 4).completeCochain τ) ⟶
    TwoCone.baseResolution D hD τ 1 :=
  (FiniteLeftModule.canonicalCosyzygiesShiftIso τ (firstTailModule q) 4).hom ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (4 : ℤ)).map
      ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (M := firstTailModule q) (N := TwoCone.baseCokernelModule D hD 5)
        (TwoCone.topCokernelMap D 1))) ≫ (topFourShiftIso q).inv

def finiteSourceTop : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    (TwoCone.baseCokernelModule D hD 1).carrier :=
  (bimoduleTopCokernel q H 0).comp (sourceAugmentationEquiv q H).toLinearMap

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorNormalizedTop
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "hD" => bimodule_term_finite_k q
local notation "P₀" => AbsoluteBar.complex k R

theorem sourceAugmentationEquiv_unit :
    sourceAugmentationEquiv q H (sourceUnit q H) = Submodule.Quotient.mk (show (sourceData q H).term 0 from tensorBarUnit q H) := by
  change (sourceBaseEquiv q H).symm (sourceUnit q H) = _
  apply (sourceBaseEquiv q H).injective
  erw [LinearEquiv.apply_symm_apply, sourceBaseEquiv_barUnit]
  rfl

theorem finiteSourceTop_unit :
    TwoCone.baseStepInclusion D (bimodule_exact q) 0 (finiteSourceTop q H (sourceUnit q H)) =
      bimoduleEndpoint q H (tensorBarUnit q H) := by
  change TwoCone.baseStepInclusion D (bimodule_exact q) 0
    (bimoduleTopCokernel q H 0 (sourceAugmentationEquiv q H (sourceUnit q H))) = _
  rw [sourceAugmentationEquiv_unit]
  have h := bimoduleTopCokernel_mk q H 0 (show (sourceData q H).term 0 from tensorBarUnit q H)
  erw [h]
  exact (TwoCone.baseStepInclusion_mk D (bimodule_exact q) 0
    (bimoduleTopComparison q H 0 (tensorBarUnit q H))).trans
    (LinearMap.congr_fun (bimoduleTopComparison_zero q H) (tensorBarUnit q H))

def normalizedSourceTop : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    (TwoCone.baseCokernelModule D hD 1).carrier :=
  ((H : k)^2)⁻¹ • finiteSourceTop q H

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def endpointEvaluation (s t : Resolution.Simple q) : (D).term 0 →ₗ[k] A k q :=
  (A.barZeroCoordinate q).comp ((squareEvaluation q s t).comp
    ((barPairCoordinates q).toLinearMap.comp
      ((ExternalTensor.moduleScalarCoordinates k Te Te ((P₀).X 0) ((P₀).X 0)).toLinearMap.comp
      (((ExternalTensor.bottomProjection k Te Te P₀ P₀ 0).restrictScalars k).comp
        (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).toLinearMap))))

theorem endpointEvaluation_unit (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    endpointEvaluation q s t (bimoduleEndpoint q H (tensorBarUnit q H)) =
      (H : k)^2 • A.socleMap q (s ⊗ₜ[k] t) := by
  change A.barZeroCoordinate q (squareEvaluation q s t
    (barPairCoordinates q (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0
      (tensorEndpoint q H (tensorBarUnit q H))))) = _
  exact tensorEndpoint_evaluated q H hq1 s t

theorem normalizedSourceTop_evaluated (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    endpointEvaluation q s t
      (TwoCone.baseStepInclusion D (bimodule_exact q) 0
        (normalizedSourceTop q H (sourceUnit q H))) = A.socleMap q (s ⊗ₜ[k] t) := by
  simp only [normalizedSourceTop, LinearMap.smul_apply, LinearMap.map_smul_of_tower, map_smul]
  rw [finiteSourceTop_unit, endpointEvaluation_unit q H hq1, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 H.ne_zero), one_smul]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEndpointCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P" => AbsoluteBar.complex k R
local notation "D" => bimoduleTwoConeData q

def endpointCoordinates : (D).term 0 ≃ₗ[k] ((R ⊗[k] R) ⊗[k] (R ⊗[k] R)) :=
  (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).trans
    (((ExternalTensor.zeroEquiv k Te Te P P).restrictScalars k).trans
      ((ExternalTensor.moduleScalarCoordinates k Te Te ((P).X 0) ((P).X 0)).trans
        (barPairCoordinates q)))

theorem endpointEvaluation_eq (s t : Resolution.Simple q) (z : (D).term 0) :
    endpointEvaluation q s t z = A.barZeroCoordinate q (squareEvaluation q s t (endpointCoordinates q z)) := rfl

theorem endpointCoordinates_symm (z : (R ⊗[k] R) ⊗[k] (R ⊗[k] R)) :
    (endpointCoordinates q).symm z =
    (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).symm
      (ExternalTensor.inclusion k Te Te P P 0 0 0 rfl
        ((ExternalTensor.moduleScalarCoordinates k Te Te ((P).X 0) ((P).X 0)).symm
          ((barPairCoordinates q).symm z))) := by
  exact congrArg (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).symm
    (ExternalTensor.zeroEquiv_symm k Te Te P P _)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEndpointInsertion
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "S" => Resolution.Simple q
local notation "X" => ModuleCat.of R S
local notation "P" => AbsoluteBar.complex k R

theorem endpointCoordinates_insert (a b c d : R) (s t : S) :
    BalancedTensor.tmul
      (⟨(endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))⟩ :
        EnvelopingBimodule k (A k q) ((shuffledBarComplex q).X 0))
      (ExternalTensor.canonicalTmul k R R S S s t) =
    (ExternalBalanced.productEvaluation k R R X X).map
      (ExternalTensor.inclusion k Te Te P P 0 0 0 rfl)
      (BalancedTensor.tmul
        ((ExternalBalanced.bimoduleCoordinates k R R ((P).X 0) ((P).X 0)).symm
          ((⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R ((P).X 0)) ⊗ₜ[k]
           (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k R ((P).X 0))))
        (ExternalTensor.canonicalTmul k R R S S s t)) := by
  rw [endpointCoordinates_symm]
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorTwistEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)
local notation "X" => A.simpleFiniteModule q

theorem evaluatedTwistEquiv_unit (x : (X).carrier) :
    evaluatedTwistEquiv q H (BalancedTensor.tmul
      (⟨⟨1⟩⟩ : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier) x) = x := by
  rw [evaluatedTwistEquiv_tmul, map_one, one_smul]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_EvaluatedResolutionTerms
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))

theorem evaluatedResolutionTermIso_augmentation :
    (evaluatedResolutionTermIso D hf X hex hr hp 0).inv ≫
      (evaluatedOrdinaryResolution D hf X hex hr hp).π.f 0 =
        ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0) := by
  change 𝟙 _ ≫ (evaluatedOrdinaryAugmentation D hf X).f 0 = _
  rw [Category.id_comp, evaluatedOrdinaryAugmentation_zero]

end ArExplicit.TwoCone

end

end OAI
end


