-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
-- name    : Development_AutomorphicArithmetic_ShortNorms_ShortNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:32.741866+00:00
-- url     : https://prove2.me/theorems/8390ba6e-8aac-405f-abe7-d0cf32a7642e
-- title:
--   Short Norm
-- statement:
--   Definitions and structural lemmas for Short Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.T3
def ShortNorm : Prop :=
  ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X →
    Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 →
    c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ)
def SmallOne : Prop := ∃ A : ℝ, 1 ≤ A ∧ ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A
def ModAt (x eps : ℝ) (N d : ℕ) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 100 ≤ d ∧ 0 < N ∧ d ∣ N ∧ Real.log N ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2
end UpperTheory.T3
end


