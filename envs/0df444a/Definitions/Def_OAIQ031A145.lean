-- Prove2me | Definitions.Def_OAIQ031A145
-- name    : OAIQ031A145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:22:40.113353+00:00
-- url     : https://prove2.me/theorems/f4f83f98-76df-4059-a365-37529e2e4310
-- title:
--   Definitions bundle OAIQ031A145 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 3 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.T.bimoduleEndpoint`, `OAI.ArExplicit.T.bimoduleTopCokernel`, `OAI.ArExplicit.T.bimoduleTopComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarScalarClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarScalarClass.lean), [`AuslanderReiten_Coordinates_TensorComparisonZeroTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonZeroTransport.lean), [`AuslanderReiten_Coordinates_TensorTopNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopNaturality.lean), [`AuslanderReiten_Evaluation_TensorEndpointEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorEndpointEvaluation.lean), [`AuslanderReiten_Tensor_TwistedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A130`, `OAIQ031A135`, `OAIQ031A136` and `OAIQ031A137` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A159` and `OAIQ031A161`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A130
import Definitions.Def_OAIQ031A135
import Definitions.Def_OAIQ031A136
import Definitions.Def_OAIQ031A137

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarScalarClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]

theorem tensorSecond_eq_of_conjugate
    (p : AbsoluteBar.Cochain3 k S) (hp : AbsoluteBar.IsCocycle3 k S p)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) 3)
    (hx : selfExtIso (k := k) (ExternalTensor.canonicalTensorIso k R S M N).symm 3 x =
      nativeTensorSecond k R S M N p hp) :
    x = tensorSecond k R S M N p hp := by
  apply (ExternalTensor.selfExtScalarEquiv k R S M N 3).injective
  rw [tensorSecond, LinearEquiv.apply_symm_apply, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact hx

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonZeroTransport
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)
variable {V : Type u} [AddCommGroup V] [Module k V]

theorem tensorComparison_zero_surjective_of_equiv
    (E : CohomologyClass P (tensorCochain (k := k) (F := F) P) 0 ≃ₗ[k] V)
    (g : V) (he : E (CohomologyClass.mk (Cocycle.ofHom v)) = g)
    (hg : ∀ z, ∃ a : k, a • g = z) :
    Function.Surjective (tensorComparison v 0) := by
  apply tensorComparison_zero_surjective
  intro z
  obtain ⟨a,ha⟩ := hg (E z)
  refine ⟨a,E.injective ?_⟩
  rw [map_smul, he, ha]

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Te" => AbsoluteBar.Enveloping k R

theorem source_product_projective (n : ℕ) :
    Module.Projective (Te ⊗[k] Te) ((productSourceData q H).term n) := by
  let (i : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) i
  let (i : ℕ) : Module.Projective Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedProjective k R (TrivialExtension.twist H) i
  exact ExternalTensor.term_projective k Te Te
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)) n

theorem source_projective (n : ℕ) :
    Module.Projective (ExternalTensor.EnvelopingProduct k R R) ((sourceData q H).term n) := by
  let := source_product_projective q H n
  exact ExternalTensor.enveloping_projective k R R ((productSourceData q H).term n)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Q" => sourceData q H

def bimoduleTopComparison (n : ℕ) : (Q).term n →ₗ[Ae] (D).term (n+1) :=
  ((ExternalTensor.envelopingFunctor k R R).map
    (ModuleCat.ofHom (tensorTopComparison q H n))).hom

def bimoduleEndpoint : (Q).term 0 →ₗ[Ae] (D).term 0 :=
  ((ExternalTensor.envelopingFunctor k R R).map
    (ModuleCat.ofHom (tensorEndpoint q H))).hom

theorem bimoduleTopComparison_chain (n : ℕ) :
    ((D).d (n+1)).comp (bimoduleTopComparison q H (n+1)) =
      (bimoduleTopComparison q H n).comp ((Q).d n) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (tensorTopComparison_chain q H n) x

theorem bimoduleTopComparison_zero :
    ((D).d 0).comp (bimoduleTopComparison q H 0) = bimoduleEndpoint q H := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (tensorTopComparison_zero q H) x

def bimoduleTopCokernel (n : ℕ) : TwoCone.BaseCokernel Q n →ₗ[Ae]
    TwoCone.BaseCokernel D (n+1) :=
  (LinearMap.range ((Q).d n)).liftQ
    ((LinearMap.range ((D).d (n+1))).mkQ.comp (bimoduleTopComparison q H n)) (by
      rintro x ⟨y,rfl⟩
      change (LinearMap.range ((D).d (n+1))).mkQ
        (bimoduleTopComparison q H n ((Q).d n y)) = 0
      have h := LinearMap.congr_fun (bimoduleTopComparison_chain q H n) y
      change (D).d (n+1) (bimoduleTopComparison q H (n+1) y) =
        bimoduleTopComparison q H n ((Q).d n y) at h
      rw [← h]
      exact LinearMap.congr_fun (LinearMap.range_mkQ_comp ((D).d (n+1))) _)

@[simp] theorem bimoduleTopCokernel_mk (n : ℕ) (x : (Q).term n) :
    bimoduleTopCokernel q H n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (bimoduleTopComparison q H n x) := rfl

theorem bimoduleTopCokernel_four :
    (bimoduleTopCokernel q H 4).comp (sourceFourthEquiv q H).toLinearMap =
      topSyzygyMap q H := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorEndpointEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

theorem tensorEndpoint_unit :
    barPairCoordinates q
      (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0 (tensorEndpoint q H (tensorBarUnit q H))) =
      twistedCasimir q H ⊗ₜ[k] twistedCasimir q H := by
  unfold tensorBarUnit tensorEndpoint
  rw [ExternalTensor.bottomMap_bottom k Te Te P₀ P₀ Q₀ Q₀ 0 0 (barDb q H) (barDb q H)
    (twistedBarUnit q H ⊗ₜ[k] twistedBarUnit q H), ExternalTensor.bottomProjection_bottom]
  rw [ExternalTensor.map_tmul, barDb_unit]
  rfl

theorem tensorEndpoint_evaluated (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    A.barZeroCoordinate q (squareEvaluation q s t
      (barPairCoordinates q (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0
        (tensorEndpoint q H (tensorBarUnit q H))))) =
      (H : k)^2 • A.socleMap q (s ⊗ₜ[k] t) := by
  rw [tensorEndpoint_unit]
  exact A.squareEvaluation_eq_beta q H hq1 s t

end ArExplicit.T

end

end OAI
end


