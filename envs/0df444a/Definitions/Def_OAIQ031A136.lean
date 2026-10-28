-- Prove2me | Definitions.Def_OAIQ031A136
-- name    : OAIQ031A136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:11:14.045464+00:00
-- url     : https://prove2.me/theorems/2619847a-625b-42ff-863f-7b1bdf718fc3
-- title:
--   Definitions bundle OAIQ031A136 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 5 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.T.canonicalSimpleScalar`, `OAI.ArExplicit.T.canonicalTensorSimple`, `OAI.ArExplicit.T.shuffledBarComplex`, `OAI.ArExplicit.T.simpleBarFreeCoordinate`, `OAI.ArExplicit.T.simpleNativeFirst`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ConcreteBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteBarFreeAugmentation.lean), [`AuslanderReiten_Bar_ConcreteNativeBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteNativeBar.lean), [`AuslanderReiten_Bar_ModuleBarCubicConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCubicConjugate.lean), [`AuslanderReiten_Bar_ModuleBarScalarClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarScalarClass.lean), [`AuslanderReiten_Bar_ModuleBarTensorEndpointCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorEndpointCoordinates.lean), [`AuslanderReiten_Coordinates_TensorTopComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopComparison.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluatedBase`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluatedBase.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluationCoefficient.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A118`, `OAIQ031A119` and `OAIQ031A125` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A145` and `OAIQ031A160`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A118
import Definitions.Def_OAIQ031A119
import Definitions.Def_OAIQ031A125

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluatedBase
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q

abbrev shuffledBarComplex :=
  ((ExternalTensor.envelopingFunctor k R R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (ExternalTensor.complex k (AbsoluteBar.Enveloping k R) (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.complex k R) (AbsoluteBar.complex k R))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q

abbrev canonicalTensorSimple := ExternalTensor.canonicalTensorObject k T₀ T₀ S S

local instance canonicalSimpleScalar : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance canonicalSimpleTower : IsScalarTower k A₀ (canonicalTensorSimple q) :=
  moduleCatBaseTower (k := k) (R := A₀) (canonicalTensorSimple q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteNativeBar
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "S" => Resolution.Simple q

def simpleNativeFirst (n : ℕ) :=
  ModuleCat.ofHom (ExternalTensor.firstCubic k T₀ T₀
    (ModuleBar.complex k T₀ S) (ModuleBar.complex k T₀ S)
    (ModuleBar.cubicMap k T₀ S (CocycleData.p q)) n)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

omit [CharP k 2] in
theorem coordinate_generator :
    (Resolution.simpleCoordinateEquiv q hq).symm 1 = CocycleData.simpleGenerator q := by
  apply (Resolution.simpleCoordinateEquiv q hq).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (CocycleData.simpleGenerator_coordinate q).symm

omit [CharP k 2] in
theorem tensorCyclicCover_eq_augmentation :
    ExternalTensor.tensorCyclicCover k (T k q) (T k q)
      (Resolution.Simple q) (Resolution.Simple q)
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq) =
      A.augmentation q := by
  apply LinearMap.ext
  intro a
  change a • (show A.Simple q from (Resolution.simpleCoordinateEquiv q hq).symm 1 ⊗ₜ[k]
    (Resolution.simpleCoordinateEquiv q hq).symm 1) = a • A.simpleGenerator q
  rw [coordinate_generator q hq]
  rfl

def simpleBarFreeCoordinate :=
  ExternalTensor.barTotalFreeCoordinate k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCubicConjugate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable {B X : ModuleCat.{u} (R ⊗[k] S)}

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat S)] in
theorem resolutionExt_nativeFirst
    (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
    (P : ProjectiveResolution B) (e : B ≅ X)
    (j : X ≅ ExternalTensor.canonicalTensorObject k R S M N)
    (φ : ProjectiveResolution.Hom P
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (e.hom ≫ j.hom))
    (p₀ : P.complex.X 3 ⟶ P.complex.X 0)
    (f : P.complex.X 3 ⟶ X) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p₀ ≫ P.π.f 0 ≫ e.hom)
    (hc : p₀ ≫ φ.hom.f 0 = φ.hom.f 3 ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k R S (complex k R M) (complex k S N)
        (cubicMap k R M p) 0)) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp (P.extMk f 4 rfl hf) (zero_add _)) =
      nativeTensorFirst k R S M N p hp :=
  resolutionExt_cubic_conjugate (k := k) P
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    e j φ p₀
    (ExternalTensor.firstComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p))
    (ExternalTensor.firstComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp))
    f hf hfc hc

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat S)] in
theorem resolutionExt_nativeSecond
    (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
    (P : ProjectiveResolution B) (e : B ≅ X)
    (j : X ≅ ExternalTensor.canonicalTensorObject k R S M N)
    (φ : ProjectiveResolution.Hom P
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (e.hom ≫ j.hom))
    (p₀ : P.complex.X 3 ⟶ P.complex.X 0)
    (f : P.complex.X 3 ⟶ X) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p₀ ≫ P.π.f 0 ≫ e.hom)
    (hc : p₀ ≫ φ.hom.f 0 = φ.hom.f 3 ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k R S (complex k R M) (complex k S N)
        (cubicMap k S N r) 0)) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp (P.extMk f 4 rfl hf) (zero_add _)) =
      nativeTensorSecond k R S M N r hr :=
  resolutionExt_cubic_conjugate (k := k) P
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    e j φ p₀
    (ExternalTensor.secondComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r))
    (ExternalTensor.secondComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr))
    f hf hfc hc

end ArExplicit.ModuleBar

end

end OAI
end

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

theorem tensorFirst_eq_of_conjugate
    (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) 3)
    (hx : selfExtIso (k := k) (ExternalTensor.canonicalTensorIso k R S M N).symm 3 x =
      nativeTensorFirst k R S M N p hp) :
    x = tensorFirst k R S M N p hp := by
  apply (ExternalTensor.selfExtScalarEquiv k R S M N 3).injective
  rw [tensorFirst, LinearEquiv.apply_symm_apply, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact hx

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorEndpointCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [mM : Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [mN : Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)

omit [CharP k 2] [Module.Finite k R] [Module.Finite k S] in
theorem tensorEndpointIso_apply (x : M ⊗[k] N) :
    (tensorEndpointIso k R S M N h j e f he hf).hom.hom x =
      TensorProduct.map e.toLinearMap f.toLinearMap x := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  cases ExternalTensor.canonicalScalar_eq k S N (mM := mN)
  rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q

theorem barDb_unit : barDb q H (twistedBarUnit q H) = twistedCasimir q H := by
  change AbsoluteBar.casimirMap k R (twistedCasimir q H) (1*1) = _
  rw [one_mul, AbsoluteBar.casimirMap_apply, map_one]
  rfl

end ArExplicit.T

end

end OAI
end


