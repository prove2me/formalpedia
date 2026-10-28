-- Prove2me | Definitions.Def_OAIQ031A179
-- name    : OAIQ031A179
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:41:37.005075+00:00
-- url     : https://prove2.me/theorems/7706d2d1-35df-4933-8bdf-743dd6415bc2
-- title:
--   Definitions bundle OAIQ031A179 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 2 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.instHasDerivedCategoryModuleCatABaseFieldQ`, `OAI.ArExplicit.instHasDerivedCategoryModuleCatTBaseFieldQ`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleHomScalars`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleHomScalars.lean), [`AuslanderReiten_Fibers_ConcreteFiberComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberComponents.lean), [`AuslanderReiten_Fibers_ConcreteFiberEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberEvaluation.lean), [`AuslanderReiten_Fibers_ConcreteFiberHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberHomotopy.lean), [`AuslanderReiten_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Main.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A168` and `OAIQ031A172` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A182`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A168
import Definitions.Def_OAIQ031A172

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)
local notation "Y" => fiberTarget q

theorem middleToSimplePair_fiberInclusion :
    (middleToSimplePair q H₁ H₂).comp (evaluatedFiberInclusion q H₁ H₂) =
    (evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂) := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  rfl

 theorem fiberEvaluationTriangle_distinguished : fiberEvaluationTriangle q H₁ H₂ ∈
    distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := fiberTarget_right_projective q
  exact FiniteLeftModule.evaluatedFiberTriangle_distinguished X U₁ U₂ Y
    (normalizedLift q H₁) (normalizedLift q H₂) (AFrobeniusTrace k q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberHomotopy
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

 theorem fiberInclusion_pairResolution :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middlePairResolutionIso q H₁ H₂).hom =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := FiniteLeftModule.pairModule X X) τ
      ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))) := by
  erw [middlePairResolutionIso_hom, ← FiniteLeftModule.resolutionMap_comp,
    middleToSimplePair_fiberInclusion]

theorem fiberInclusion_product_fst :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom ≫ biprod.fst =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₁ q H₁ H₂)) := by
  simp only [middleProductResolutionIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_fst]
  rw [← Category.assoc]
  erw [fiberInclusion_pairResolution q H₁ H₂]
  exact (FiniteLeftModule.resolutionMap_comp (M := evaluatedFiber q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) (L := X) τ
    ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))
    (FiniteLeftModule.pairFst X X)).symm

theorem fiberInclusion_product_snd :
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂)) ≫
      (middleProductResolutionIso q H₁ H₂).hom ≫ biprod.snd =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₂ q H₁ H₂)) := by
  simp only [middleProductResolutionIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_snd]
  rw [← Category.assoc]
  erw [fiberInclusion_pairResolution q H₁ H₂]
  exact (FiniteLeftModule.resolutionMap_comp (M := evaluatedFiber q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) (L := X) τ
    ((evaluatedRho₁ q H₁ H₂).prod (evaluatedRho₂ q H₁ H₂))
    (FiniteLeftModule.pairSnd X X)).symm

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleHomScalars
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)

theorem simpleZeroScalarEquiv_unit (hq1 : 1+q ≠ 0) :
    simpleZeroScalarEquiv q hq1 (simpleZeroUnit q) = 1 := by
  have h := fullHomShiftedHomotopyEquiv_identity k (A.simpleComplete q)
  change simpleFullHomEquiv q 0 (fullHomIdentity (A.simpleComplete q)) = simpleZeroUnit q at h
  change A.fullHomZeroScalarEquiv q hq1 ((simpleFullHomEquiv q 0).symm (simpleZeroUnit q)) = 1
  rw [← h, LinearEquiv.symm_apply_apply]
  exact A.fullHomZeroScalarEquiv_identity q hq1

theorem simpleHom_eq_scalar_unit (hq1 : 1+q ≠ 0) (v : SimpleHom q 0) :
    v = simpleZeroScalarEquiv q hq1 v • simpleZeroUnit q := by
  apply (simpleZeroScalarEquiv q hq1).injective
  rw [map_smul, simpleZeroScalarEquiv_unit]
  exact (mul_one _).symm

omit [CharP k 2] in
theorem simpleZeroUnit_postcomp {Y : HC} (g : simpleHomotopyObject q ⟶ Y) :
    simpleZeroUnit q ≫ g⟦(0 : ℤ)⟧' = g ≫ (shiftFunctorZero HC ℤ).inv.app Y :=
  ((shiftFunctorZero HC ℤ).inv.naturality g).symm

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
local notation "X₀" => A.simpleFiniteModule q
local notation "Y₀" => fiberTarget q
local notation "τ₀" => AFrobeniusTrace k q

variable (H₁ H₂ : kˣ)
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)

theorem fiberEvaluationTriangle_second : (fiberEvaluationTriangle q H₁ H₂).mor₂ =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedFiberSecond q H₁ H₂)) := by
  let := fiberTarget_right_projective q
  exact FiniteLeftModule.evaluationTriangle_second X₀
    (FiniteLeftModule.fiberInclusion U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)).hom
    (FiniteLeftModule.fiberMap U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)).hom
    Subtype.val_injective
    (FiniteLeftModule.fiberMap_surjective U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂))
    (FiniteLeftModule.fiberFunctionExact U₁ U₂ Y₀ (normalizedLift q H₁) (normalizedLift q H₂)) τ₀

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance instHasDerivedCategoryModuleCatTBaseFieldQ : HasDerivedCategory (ModuleCat (T BaseField q)) :=
  HasDerivedCategory.standard (ModuleCat (T BaseField q))
local instance instHasDerivedCategoryModuleCatABaseFieldQ : HasDerivedCategory (ModuleCat (A BaseField q)) :=
  HasDerivedCategory.standard (ModuleCat (A BaseField q))

end ArExplicit

end

end OAI
end


