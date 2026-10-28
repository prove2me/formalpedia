-- Prove2me | Definitions.Def_OAIQ031A183
-- name    : OAIQ031A183
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:02:44.168154+00:00
-- url     : https://prove2.me/theorems/411ea386-3888-458f-8da5-d12d17975c98
-- title:
--   Definitions bundle OAIQ031A183 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 4 definitions and 5 theorems. The definitions and types are `OAI.ArExplicit.T.branchPlainHomEquiv`, `OAI.ArExplicit.T.concreteKoszulCoordinates`, `OAI.ArExplicit.T.twoConeTopEquiv`, `OAI.ArExplicit.T.twoConeTopScalarEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConcreteTwoConeProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeProfile.lean), [`AuslanderReiten_Coordinates_BranchHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/BranchHomCoordinates.lean), [`AuslanderReiten_Coordinates_BranchHomProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/BranchHomProfile.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulCoordinateLaws`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulCoordinateLaws.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulCoordinates.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulRow.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A180` and `OAIQ031A181` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A187`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A180
import Definitions.Def_OAIQ031A181

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulRow
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q

theorem simpleSkeletonRow_fullHom (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedSingletonResolution q 0)⟦a⟧) :
    evaluatedBaseFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.connecting k (simpleSkeletonTriangle q 0)
        (evaluatedSimpleObject q) a v) =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=(a+1)-((0:ℕ):ℤ))
      (fullHomProduct (evaluatedSingletonFullHomEquiv q 0 a v).1 (firstCoverClass q) +
       fullHomProduct (evaluatedSingletonFullHomEquiv q 0 a v).2 (secondCoverClass q)) := by
  have hr := connectingRow (k := k) (simpleSkeletonTriangle q 0)
    (evaluatedSimpleObject q) (evaluatedBaseResolution q 2) (evaluatedBaseResolution q 3)
    a v
    ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q 0)))
    ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q 0)))
    (evaluatedBaseStepIso q 2).hom
    (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ 0)
    (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ 0)
    (simpleSkeletonConnecting_components q 0)
  have h₁ := evaluatedFirstCokernel_step_action q 0 a
    (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q 0)))⟦a⟧')
  have h₂ := evaluatedSecondCokernel_step_action q 0 a
    (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q 0)))⟦a⟧')
  exact additiveRowCoordinates (evaluatedBaseFullHomEquiv q 0 (a+1)).toAddMonoidHom
    (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=(a+1)-((0:ℕ):ℤ))).toAddMonoidHom
    (fun z => fullHomProduct z (firstCoverClass q))
    (fun z => fullHomProduct z (secondCoverClass q)) hr h₁ h₂
    (evaluatedSingletonFullHomEquiv_fst q 0 a v)
    (evaluatedSingletonFullHomEquiv_snd q 0 a v)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulCoordinateLaws
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem concreteRowCoordinate (a : ℤ) (v : twoConeMiddleHom q a) :
    twoConeBottomCoordinate q (a+1) ((concreteTwoConeFiltration q).row a v) =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=a+1)
        (TateKoszul.row (x := firstCoverOperator q) (y := secondCoverOperator q)
          (a-2) (twoConeMiddleCoordinate q a v)) := by
  have h := congrArg (TateKoszul.degreeEquiv (k := k) H₀
    (by omega : (a+1)-((0:ℕ):ℤ)=a+1)) (simpleSkeletonRow_fullHom q a v)
  exact h.trans (degreeEquiv_trans_apply _ _ _)

theorem concreteColumnCoordinate (a : ℤ) (v : twoConeTopHom q a) :
    twoConeMiddleCoordinate q (a+1) ((concreteTwoConeFiltration q).column a v) =
      ((TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=a+1-2)).prodCongr
        (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=a+1-2)))
        (TateKoszul.column (x := firstCoverOperator q) (y := secondCoverOperator q)
          (a-4) (twoConeTopCoordinate q a v)) := by
  apply Prod.ext
  · exact simpleTopColumn_fst q a v
  · exact simpleTopColumn_snd q a v

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def concreteKoszulCoordinates : TwoConeKoszulCoordinates (concreteTwoConeFiltration q)
    (fun a => fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (firstCoverClass q))
    (fun a => fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (secondCoverClass q)) where
  bottom := twoConeBottomCoordinate q
  middle := twoConeMiddleCoordinate q
  top := twoConeTopCoordinate q
  row_eq := concreteRowCoordinate q
  column_eq := concreteColumnCoordinate q

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d
include hq hq1 h

theorem twoConeHom_subsingleton (a : ℤ) (h0 : a ≠ 0) (h3 : a ≠ 3) :
    Subsingleton (twoConeHom q a) :=
  (concreteKoszulCoordinates q).subsingleton_of_ne (coverTateModel q hq hq1 h) a h0 h3

def twoConeTopEquiv : twoConeHom q 3 ≃ₗ[k] H₀ (-1) :=
  (concreteKoszulCoordinates q).topCoordinateEquiv (coverTateModel q hq hq1 h)

def twoConeTopScalarEquiv : twoConeHom q 3 ≃ₗ[k] k :=
  ((twoConeTopEquiv q hq hq1 h).trans ((coverTateModel q hq hq1 h).negative 0)).trans
    (BinaryKoszul.zeroDualPieceScalarEquiv k)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_BranchHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def branchPlainHomEquiv :
    (evaluatedSimpleObject q ⟶ branchTargetObject q) ≃ₗ[k] twoConeHom q 3 :=
  Linear.homCongr k (Iso.refl _) (evaluatedBranchTargetShiftIso q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_BranchHomProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
include hq hq1 h

theorem branchHom_subsingleton (a : ℤ) (h0 : a ≠ 0) (h3 : a ≠ -3) :
    Subsingleton (BranchHom q a) := by
  let := twoConeHom_subsingleton q hq hq1 h (a+3) (by omega) (by omega)
  exact (branchHomEquiv q a).injective.subsingleton

end ArExplicit.T

end

end OAI
end


