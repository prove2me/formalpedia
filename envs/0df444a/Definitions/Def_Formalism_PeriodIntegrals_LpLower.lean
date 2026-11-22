-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LpLower
-- name    : Formalism_PeriodIntegrals_LpLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:27.8808+00:00
-- url     : https://prove2.me/theorems/cfe773e1-8ea7-4081-bcce-40af173b9655
-- title:
--   Lp Lower
-- statement:
--   Definitions and structural lemmas for Lp Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LpLower.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
def lpFeasible (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : Set ℝ :=
  {y | ∃ xs : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, (¬ Odd i ∨ d ≤ i) → xs s i = 0) ∧
    (∀ s, (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ Ds s) ∧
    y = ∑ s, ∑ i ∈ Finset.range d, xs s i}
def lpF (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : ℝ :=
  (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - sSup (lpFeasible l d Ds)
def LpLower : Prop :=
  ∀ (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) →
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds
end PI


