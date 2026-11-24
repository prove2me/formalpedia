-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:58.818497+00:00
-- url     : https://prove2.me/theorems/dc5e9c60-4494-4c56-9775-28eee5d6916a
-- title:
--   Statements Eventual Polynomial
-- statement:
--   Definitions and structural lemmas for Statements Eventual Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsEventualPolynomial.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
def EventualPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ), DegLT f (n + 1) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ n ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (f (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


