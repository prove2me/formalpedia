-- Prove2me | Definitions.Def_OAIQ031A178
-- name    : OAIQ031A178
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:45:05.092652+00:00
-- url     : https://prove2.me/theorems/5a0449a2-0352-41f9-b0e2-3c5dbc892b04
-- title:
--   Definitions bundle OAIQ031A178 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 9 definitions and 11 theorems. The definitions and types are `OAI.ArExplicit.T.explicitLeftModule`, `OAI.ArExplicit.T.fiberFullHomEquiv`, `OAI.ArExplicit.T.fiberFullRhoPair`, `OAI.ArExplicit.T.fiberProductMiddleEquiv`, `OAI.ArExplicit.T.fiberProductTriangle`, `OAI.ArExplicit.T.tensorFiberFullEquiv`, `OAI.ArExplicit.T.tensorFiberMap`, `OAI.ArExplicit.T.tensorFiberRhoEquiv`, `OAI.ArExplicit.T.tensorFiberRhoPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_ConcreteMainCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteMainCriterion.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiber.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiberMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiberMaps.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiberProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiberProjection.lean), [`AuslanderReiten_Fibers_ConcreteFiberComponentMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberComponentMaps.lean), [`AuslanderReiten_Fibers_ConcreteFiberComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberComponents.lean), [`AuslanderReiten_Fibers_ConcreteFiberRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberRow.lean), [`AuslanderReiten_Fibers_ConcreteFiberTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberTriangle.lean), [`AuslanderReiten_Fibers_FiberBranchConsequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberBranchConsequences.lean), [`AuslanderReiten_Fibers_FiberFullHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberFullHomCoordinates.lean), [`AuslanderReiten_Fibers_TensorFiberCoordinateIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/TensorFiberCoordinateIso.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A168`, `OAIQ031A169`, `OAIQ031A171` and `OAIQ031A172` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A181` and `OAIQ031A182`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A168
import Definitions.Def_OAIQ031A169
import Definitions.Def_OAIQ031A171
import Definitions.Def_OAIQ031A172

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberFullHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "τ₀" => AFrobeniusTrace k q
local notation "P₀" => A.simpleComplete q

def fiberFullHomEquiv (n : ℤ) :
    CohomologyClass P₀ (fiberComplete q H₁ H₂) n ≃ₗ[k] FiberHom q H₁ H₂ n :=
  fullHomShiftedHomotopyEquiv k P₀ (fiberComplete q H₁ H₂) n

def fiberFullRhoPair (n : ℤ) :
    CohomologyClass P₀ (fiberComplete q H₁ H₂) n →ₗ[k]
      (CohomologyClass P₀ P₀ n × CohomologyClass P₀ P₀ n) :=
  (((simpleFullHomEquiv q n).symm.prodCongr (simpleFullHomEquiv q n).symm).toLinearMap.comp
    (fiberHomRhoPair q H₁ H₂ n)).comp (fiberFullHomEquiv q H₁ H₂ n).toLinearMap

theorem fiberFullRhoPair_apply (n : ℤ)
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) n) :
    fiberFullRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)) n x,
       fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)) n x) := by
  apply ((simpleFullHomEquiv q n).prodCongr (simpleFullHomEquiv q n)).injective
  simp only [fiberFullRhoPair, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · exact (fullHomShiftedHomotopyEquiv_postcomp k n
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)) x).symm
  · exact (fullHomShiftedHomotopyEquiv_postcomp k n
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)) x).symm

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiber
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

attribute [local instance] OAI.ArExplicit.T.instFiniteAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber
attribute [local instance] OAI.ArExplicit.T.instProjectiveAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber
attribute [local instance] OAI.ArExplicit.T.instFiniteMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber
attribute [local instance] OAI.ArExplicit.T.instProjectiveMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber
def tensorFiberFullEquiv (n : ℤ) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n ≃ₗ[k]
      CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) n :=
  FiniteLeftModule.evaluatedResolutionFullEquiv (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂) (A.simpleComplete q) n

theorem tensorFiberFullEquiv_apply (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberFullEquiv q H₁ H₂ n x = fullHomPostcomp (tensorFiberOut q H₁ H₂) n x :=
  FiniteLeftModule.evaluatedResolutionFullEquiv_apply (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂) (A.simpleComplete q) n x

def tensorFiberRhoPair (n : ℤ) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n →ₗ[k]
      (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n) :=
  (fiberFullRhoPair q H₁ H₂ n).comp (tensorFiberFullEquiv q H₁ H₂ n).toLinearMap

theorem tensorFiberRhoPair_apply (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (evaluatedRho₁ q H₁ H₂)) n (fullHomPostcomp (tensorFiberOut q H₁ H₂) n x),
       fullHomPostcomp (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (evaluatedRho₂ q H₁ H₂)) n (fullHomPostcomp (tensorFiberOut q H₁ H₂) n x)) :=
  by
    simpa only [tensorFiberRhoPair, LinearMap.comp_apply, LinearEquiv.coe_coe,
      tensorFiberFullEquiv_apply] using
      (fiberFullRhoPair_apply q H₁ H₂ n (tensorFiberFullEquiv q H₁ H₂ n x))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiberMaps
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def tensorFiberMap
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    A.simpleComplete q ⟶ tensorFiberComplete q H₁ H₂ :=
  fullHomZeroRepresentative ((tensorFiberFullEquiv q H₁ H₂ 0).symm g)

theorem tensorFiberMap_class
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    (tensorFiberFullEquiv q H₁ H₂ 0)
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g))) = g := by
  rw [tensorFiberMap, fullHomZeroRepresentative_class, LinearEquiv.apply_symm_apply]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiberProjection
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)

theorem tensorFiberMap_pair_image :
    tensorFiberRhoPair q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g))) =
        fiberFullRhoPair q H₁ H₂ 0 g :=
  congrArg (fiberFullRhoPair q H₁ H₂ 0) (tensorFiberMap_class q H₁ H₂ g)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_TensorFiberCoordinateIso
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)

def tensorFiberRhoEquiv (n : ℤ) (h : Function.Bijective (fiberFullRhoPair q H₁ H₂ n)) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n ≃ₗ[k]
      (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n) :=
  (tensorFiberFullEquiv q H₁ H₂ n).trans
    (LinearEquiv.ofBijective (fiberFullRhoPair q H₁ H₂ n) h)

theorem tensorFiberRhoEquiv_apply (n : ℤ)
    (h : Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoEquiv q H₁ H₂ n h x = tensorFiberRhoPair q H₁ H₂ n x := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteMainCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)

abbrev explicitLeftModule := ConeModule
  (TriangularInduction.crossChainMap (tensorFiberMap q H₁ H₂ g))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberComponents
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

variable (H₁ H₂ : kˣ)

theorem evaluatedFiberSecond_inl : (evaluatedFiberSecond q H₁ H₂).comp
    (evaluatedMiddleInl q H₁ H₂) = evaluatedBranchMap q H₁ := by
  dsimp only [evaluatedFiberSecond, evaluatedMiddleInl, evaluatedBranchMap]
  rw [← LinearMap.comp_assoc, FiniteLeftModule.evaluatedFiberMap_inl]

theorem evaluatedFiberSecond_inr : (evaluatedFiberSecond q H₁ H₂).comp
    (evaluatedMiddleInr q H₁ H₂) = evaluatedBranchMap q H₂ := by
  dsimp only [evaluatedFiberSecond, evaluatedMiddleInr, evaluatedBranchMap]
  rw [← LinearMap.comp_assoc, FiniteLeftModule.evaluatedFiberMap_inr]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberTriangle
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)

def fiberProductTriangle : Triangle HC :=
  triangleReplaceMiddle (fiberEvaluationTriangle q H₁ H₂) (middleProductResolutionIso q H₁ H₂)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberComponentMaps
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

variable (H₁ H₂ : kˣ)

theorem evaluatedMiddleInl_product :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedMiddleInl q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom = biprod.inl := by
  simp only [middleProductResolutionIso, Iso.trans_hom, ← Category.assoc,
    middlePairResolutionIso_hom]
  erw [← FiniteLeftModule.resolutionMap_comp, middleToSimplePair_inl]
  exact FiniteLeftModule.resolutionPairInl τ₀ X₀ X₀

theorem evaluatedMiddleInr_product :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedMiddleInr q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom = biprod.inr := by
  simp only [middleProductResolutionIso, Iso.trans_hom, ← Category.assoc,
    middlePairResolutionIso_hom]
  erw [← FiniteLeftModule.resolutionMap_comp, middleToSimplePair_inr]
  exact FiniteLeftModule.resolutionPairInr τ₀ X₀ X₀

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberRow
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)
local notation "X₀" => simpleHomotopyObject q
local notation "T₀" => fiberProductTriangle q H₁ H₂

def fiberProductMiddleEquiv (n : ℤ) :
    TriangleGradedSequence.Middle T₀ X₀ n ≃ₗ[k] (SimpleHom q n × SimpleHom q n) :=
  mappedBiproductHomEquiv k (CategoryTheory.shiftFunctor HC n) X₀ X₀ X₀

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberBranchConsequences
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "X₀" => simpleHomotopyObject q

variable (hq1 : 1+q ≠ 0) (e : BranchHom q 0 ≃ₗ[k] k)

include hq1 e

variable [Subsingleton (BranchHom q (-1))]
local instance instSubsingletonTopHomotopyCategoryIntModuleCatAUpFiberProductTriangleSimpleHomotopyObjectNegOfNat : Subsingleton (TriangleGradedSequence.Top T₀ X₀ (-1)) :=
  inferInstanceAs (Subsingleton (BranchHom q (-1)))

end ArExplicit.T

end

end OAI
end


