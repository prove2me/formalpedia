-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_LogBounds
-- name    : CK_GeneralCK_Certificates_LogBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:15.616207+00:00
-- url     : https://prove2.me/theorems/a67b22b3-a769-4294-bc1e-0eeb4acde5d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.LogBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.LogBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.LogBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.LogBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/LogBounds.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_LogBounds

namespace GeneralCK.Certificates
open scoped BigOperators













/-- Soundness connects the executable rational checker to the real logarithm. -/
theorem checkLog_sound {w lo hi : ℚ} {n : ℕ}
    (hc : checkLog w n lo hi = true) :
    (lo : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
    Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤ (hi : ℝ) := by
  have hh : 0 ≤ w ∧ w < 1 ∧ lo ≤ logLower w n ∧ logUpper w n ≤ hi :=
    of_decide_eq_true hc
  obtain ⟨hw₀, hw₁, hl, hu⟩ := hh
  have hw₀' : (0 : ℝ) ≤ w := by exact_mod_cast hw₀
  have hw₁' : (w : ℝ) < 1 := by exact_mod_cast hw₁
  have lower := Real.sum_range_le_log_div hw₀' hw₁' n
  have upper := Real.log_div_le_sum_range_add hw₀' hw₁' n
  dsimp [logLower, logUpper] at hl hu
  have hl' : (lo : ℝ) ≤
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    exact_mod_cast hl
  have hu' :
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) +
      2 * (w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2) ≤ (hi : ℝ) := by
    exact_mod_cast hu
  rw [mul_div_assoc] at hu'
  constructor <;> linarith

end GeneralCK.Certificates


