-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsUnbranched
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsUnbranched
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:41.93761+00:00
-- url     : https://prove2.me/theorems/8884073c-acc4-4383-9048-4103925de020
-- title:
--   Statements Unbranched
-- statement:
--   Definitions and structural lemmas for Statements Unbranched, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StatementsUnbranched.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
def UnbranchedPartConnected.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        IsPreconnected {x : Fin n → ℂ | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) (P * R) ≠ 0}
end GroundTheory.Heights₂.Heights.HilbertSamuel


