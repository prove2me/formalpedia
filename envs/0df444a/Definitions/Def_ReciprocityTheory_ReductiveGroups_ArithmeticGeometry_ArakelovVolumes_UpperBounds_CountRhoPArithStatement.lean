-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountRhoPArithStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountRhoPArithStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:55.019259+00:00
-- url     : https://prove2.me/theorems/02cbfe0a-65eb-4f3f-aff7-c8e5bb610d10
-- title:
--   Count Rho PArith Statement
-- statement:
--   Definitions and structural lemmas for Count Rho PArith Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CountRhoPArithStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
def CountRhoPArithStatement : Prop :=
  ∀ (n T δ dV dW : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T → dW ≤ dV →
    δ * (T + n).choose n ≤ dW → dV ≤ δ * (T + 2 * n + 6).choose n →
    ((dV : ℝ) - dW) ≤ (n : ℝ) * (n + 6) * dV / T
def CountRhoArithStatement : Prop :=
  ∀ (n T δ dV ρ : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T →
    δ * (T - 1).choose n + ρ ≤ dV → dV ≤ δ * (T + 2 * n + 6).choose n →
    (ρ : ℝ) ≤ 22 * (n : ℝ) ^ 2 * dV / T
end ReciprocityTheory.ChartRestriction.G.AR.Up


