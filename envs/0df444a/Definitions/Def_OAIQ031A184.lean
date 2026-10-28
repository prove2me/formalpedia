-- Prove2me | Definitions.Def_OAIQ031A184
-- name    : OAIQ031A184
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:14:50.381993+00:00
-- url     : https://prove2.me/theorems/03e296d9-e3f0-483f-957c-e4a3f3fb7b8e
-- title:
--   Definitions bundle OAIQ031A184 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConcreteTwoTwistRows`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoTwistRows.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiberProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiberProjection.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A181` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A187`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A181

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

variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))

include hg

theorem tensorFiberMap_rho₁_inverse :
    (HomotopyCategory.quotient _ _).map (tensorFiberMap q H₁ H₂ g ≫ tensorRho₁ q H₁ H₂) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)).inv := by
  let b := BalancedTensor.comparisonOut (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)
  apply fullHomZero_projection_inverse k _ b _
    (BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
      (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁))
  have h := congrArg Prod.fst
    ((tensorFiberRhoPair_comparison q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g)))).symm.trans
        ((tensorFiberMap_pair_image q H₁ H₂ g).trans hg))
  exact (congrArg (fullHomPostcomp b 0)
    (fullHomPostcomp_ofHom (tensorFiberMap q H₁ H₂ g) (tensorRho₁ q H₁ H₂))).symm.trans h

theorem tensorFiberMap_rho₂_inverse :
    (HomotopyCategory.quotient _ _).map (tensorFiberMap q H₁ H₂ g ≫ tensorRho₂ q H₁ H₂) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)).inv := by
  let b := BalancedTensor.comparisonOut (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)
  apply fullHomZero_projection_inverse k _ b _
    (BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
      (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂))
  have h := congrArg Prod.snd
    ((tensorFiberRhoPair_comparison q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g)))).symm.trans
        ((tensorFiberMap_pair_image q H₁ H₂ g).trans hg))
  exact (congrArg (fullHomPostcomp b 0)
    (fullHomPostcomp_ofHom (tensorFiberMap q H₁ H₂ g) (tensorRho₂ q H₁ H₂))).symm.trans h

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoTwistRows
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
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : Resolution.NoPositivePowerOne q)
variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)
variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))
include hq hq1 hp hg

theorem tensorFiberComparison_first (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H₁) _
      (fullHomPostcomp (tensorRho₁ q H₁ H₂) _
        (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x)) =
      (((H₁⁻¹ : kˣ) : k)^m) • x.1 + x.2 :=
  TriangularInduction.tensorComparison_projected_row
    (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
    (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂))
    (tensorFiberMap q H₁ H₂ g) (completeTwistIn q H₁) (completeTwistOut q H₁)
    ((tensorFiberMap_rho₁_inverse q H₁ H₂ g hg).trans (completeTwistIn_quotient q H₁).symm)
    (completeTwist_inverse q H₁) _ _ (completeTwist_scalar q H₁ hq hq1 hp m hm) x

theorem tensorFiberComparison_second (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H₂) _
      (fullHomPostcomp (tensorRho₂ q H₁ H₂) _
        (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x)) =
      (((H₂⁻¹ : kˣ) : k)^m) • x.1 + x.2 :=
  TriangularInduction.tensorComparison_projected_row
    (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
    (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂))
    (tensorFiberMap q H₁ H₂ g) (completeTwistIn q H₂) (completeTwistOut q H₂)
    ((tensorFiberMap_rho₂_inverse q H₁ H₂ g hg).trans (completeTwistIn_quotient q H₂).symm)
    (completeTwist_inverse q H₂) _ _ (completeTwist_scalar q H₂ hq hq1 hp m hm) x

theorem tensorFiberComparison_rows (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    tensorFiberRhoPair q H₁ H₂ _
      (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x) =
        twoTwistLinear (((H₁⁻¹ : kˣ) : k)^m) (((H₂⁻¹ : kˣ) : k)^m) x := by
  refine (tensorFiberRhoPair_comparison q H₁ H₂ _ _).trans (Prod.ext ?_ ?_)
  · exact (fullHomPostcomp_congr k _
      ((BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)).trans
          (completeTwistOut_quotient q H₁).symm) _).trans
      (tensorFiberComparison_first q H₁ H₂ hq hq1 hp g hg m hm x)
  · exact (fullHomPostcomp_congr k _
      ((BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)).trans
          (completeTwistOut_quotient q H₂).symm) _).trans
      (tensorFiberComparison_second q H₁ H₂ hq hq1 hp g hg m hm x)

end ArExplicit.T

end

end OAI
end


