-- Prove2me | Definitions.Def_OAIQ031A150
-- name    : OAIQ031A150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:30:15.817781+00:00
-- url     : https://prove2.me/theorems/9cb37bd9-a140-4e44-bce8-20b7212282a9
-- title:
--   Definitions bundle OAIQ031A150 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 6 definitions and 4 theorems. The definitions and types are `OAI.ArExplicit.Resolution.ASelfExt`, `OAI.ArExplicit.Resolution.aCanonicalFirst`, `OAI.ArExplicit.Resolution.aCanonicalSecond`, `OAI.ArExplicit.T.sourceBaseEquiv`, `OAI.ArExplicit.T.sourceProductBaseRestricted`, `OAI.ArExplicit.T.sourceToTwistedRegular`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Evaluation_TensorSourceUnit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorSourceUnit.lean), [`AuslanderReiten_Ext_AExtActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/AExtActions.lean), [`AuslanderReiten_Ext_AExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/AExtPolynomial.lean), [`AuslanderReiten_Ext_TExplicitPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitPolynomial.lean), [`AuslanderReiten_Modules_TwistedFiniteEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedFiniteEndpoint.lean), [`AuslanderReiten_Tensor_TwistedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A137`, `OAIQ031A139`, `OAIQ031A142`, `OAIQ031A143` and `OAIQ031A144` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A156`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A137
import Definitions.Def_OAIQ031A139
import Definitions.Def_OAIQ031A142
import Definitions.Def_OAIQ031A143
import Definitions.Def_OAIQ031A144

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q

def sourceProductBaseRestricted := Iso.toLinearEquiv
  ((ExternalTensor.envelopingFunctor k R R).mapIso (sourceProductBaseTyped q H).toModuleIso)

def sourceToTwistedRegular :=
  (sourceQuotientRestriction q H).trans (sourceProductBaseRestricted q H)

def sourceBaseEquiv : TwoCone.BaseCokernel (sourceData q H) 0 ≃ₗ[
    ExternalTensor.EnvelopingProduct k R R]
    bimoduleEnvelopingObject k (R ⊗[k] R) (TwistedBimodule k (R ⊗[k] R) (sourceTwist q H)) :=
  (sourceToTwistedRegular q H).trans
    (twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorSourceUnit
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Te" => AbsoluteBar.Enveloping k R

theorem sourceBaseEquiv_barUnit :
    sourceBaseEquiv q H (Submodule.Quotient.mk (tensorBarUnit q H)) =
      (⟨1⟩ : TwistedBimodule k (A k q) (sourceTwist q H)) := by
  change twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H)
    ((ExternalTensor.augmentation k Te Te
      (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
      (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))).f 0
        (tensorBarUnit q H)) = _
  unfold tensorBarUnit
  erw [ExternalTensor.augmentation_insert k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))]
  change twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H)
    (ExternalTensor.map k Te Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      (twistedBarUnit q H ⊗ₜ[k] twistedBarUnit q H)) = _
  erw [ExternalTensor.map_tmul]
  have hu : ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      (twistedBarUnit q H) = (show AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0 from (1 : R)) := by
    change ((AbsoluteBar.twistedAugmentation k R (TrivialExtension.twist H)).f 0).hom _ = _
    rw [AbsoluteBar.twistedAugmentation_zero]
    change (1 : R) * 1 = 1
    exact one_mul 1
  simp only [hu]
  apply TwistedBimodule.ext
  change (1 : R) ⊗ₜ[k] (1 : R) = (1 : A k q)
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

theorem tExplicit_coefficient (n : ℕ) (x : TSelfExt q (3 * n)) :
    ∃! a : k, a • tExplicitPower q hq hq1 h n = x := by
  let e := tExplicitCoefficientEquiv q hq hq1 h n
  refine ⟨e.symm x, ?_, ?_⟩
  · change e.symm x • e 1 = x
    rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    have he : e a = a • e 1 := by simpa using e.map_smul a (1 : k)
    exact he.trans ha

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_AExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev ASelfExt (n : ℕ) := Ext (ArExplicit.A.Simple q) (ArExplicit.A.Simple q) n

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_AExtActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]

abbrev aCanonicalFirst :=
  ModuleBar.nativeTensorFirst k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

abbrev aCanonicalSecond :=
  ModuleBar.nativeTensorSecond k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedFiniteEndpoint
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R
  (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) M.carrier ≃ₗ[R] M.carrier)
variable (E : M.carrier ≅ (ModuleCat.restrictScalars σ.symm.toRingHom).obj M.carrier)

theorem twistedFiniteEndpoint_eq
    (h : ∀ (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M.carrier),
      E.inv.hom (σ.symm a.value.value • m) = e (BalancedTensor.tmul a m)) :
    (twistedEnvelopingRestrictionIso σ).app M.carrier ≪≫ E.symm =
      BalancedTensor.nativeEvaluationIso M e := by
  apply BalancedTensor.functorIso_ext M.carrier M.carrier
  intro a m
  exact (twistedEnvelopingEndpoint_tmul σ M.carrier M.carrier E.symm a m).trans
    ((h a m).trans (BalancedTensor.nativeEvaluationIso_tmul M e a m).symm)

theorem twistedFiniteEndpoint_symm_eq
    (h : ∀ (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M.carrier),
      E.inv.hom (σ.symm a.value.value • m) = e (BalancedTensor.tmul a m)) :
    (BalancedTensor.nativeEvaluationIso M e).symm =
      E ≪≫ ((twistedEnvelopingRestrictionIso σ).app M.carrier).symm := by
  rw [← twistedFiniteEndpoint_eq σ M e E h]
  rfl

end ArExplicit

end

end OAI
end


