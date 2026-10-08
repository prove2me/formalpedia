-- Prove2me | Definitions.Def_CK_CKLaneA3V_Owners
-- name    : CK_CKLaneA3V_Owners
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T03:24:51.705602+00:00
-- url     : https://prove2.me/theorems/cc481a52-4e94-4ca5-89b6-fab907c0f76b
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Owners` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Owners` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Owners` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Owners (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Owners.lean)

import Definitions.Def_CK_CKLaneA3V_FinalPos

/-!
# CKLaneA3V.Owners — direct chart slot `directC4` (Lane A3)

TM certificate with `Tq = 1/5` (order 14), positivity checked on the rectangle
`t = 1/2 - u ∈ [7/50, 1/5]`, `ρ ∈ [1/5, 1)` ⊇ the directC4 range `ρ ∈ [11/50, 1)`
(`FinalPos.coef_pos_region`, `m11_pos_region`).
-/

set_option linter.unusedVariables false

namespace CKLaneA3V

open GeneralCK GeneralCK.Correction

theorem dom_of {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 5) (h2 : 0 < ρ) (h3 : ρ < 1) : Dom t ρ := by
  refine ⟨h0, ?_, h2, h3⟩
  have : ((Tq : ℚ) : ℝ) = 1 / 5 := by norm_num [Tq]
  rw [this]; exact h1

/-- actual ratio minors on `u ∈ [3/10, 9/25]`, `ρ ∈ [11/50, 1)` -/
theorem actualRatioMinors_c4 {u ρ : ℝ} (hu0 : 3 / 10 ≤ u) (hu1 : u ≤ 9 / 25) (hr0 : 11 / 50 ≤ ρ)
    (hr1 : ρ < 1) : ActualRatioMinorsPositive u ρ := by
  have ht0 : 0 < 1 / 2 - u := by linarith
  have ht1 : 1 / 2 - u ≤ 1 / 5 := by linarith
  have hd := dom_of ht0 ht1 (by linarith) hr1
  have hT0 : (((7 / 50 : ℚ)) : ℝ) ≤ 1 / 2 - u := by push_cast; linarith
  have hS0 : (((-3 / 10 : ℚ)) : ℝ) ≤ ρ - 1 / 2 := by push_cast; linarith
  have hc := coef_pos_region (1 / 2 - u) ρ hd hT0 hS0
  have hm := m11_pos_region (1 / 2 - u) ρ hd hT0 hS0
  have hk : 0 < Natural.kdet (1 / 2 - (1 / 2 - u)) (1 / 2 - (1 - ρ) * (1 / 2 - u)) := by
    rw [HighU.kdet_eq_gap_sq_mul_coefficient (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)]
    have hg : 0 < (1 / 2 - (1 - ρ) * (1 / 2 - u)) - (1 / 2 - (1 / 2 - u)) := sub_pos.mpr (dom_u_lt_w hd)
    positivity
  have e1 : 1 / 2 - (1 / 2 - u) = u := by ring
  have e2 : 1 / 2 - (1 - ρ) * (1 / 2 - u) = u + ρ * (1 / 2 - u) := by ring
  rw [e1, e2] at hm hk
  exact minors_of_pos (by linarith) (by linarith) (by linarith) hr1 hm hk

/-- `ChartOwners.directC4` -/
theorem directC4 : Complement.SignsOnBox (3 / 10) (9 / 25) (11 / 50) 1 := by
  intro u ρ _ _ _ hr' huB hrB
  exact Complement.ratioSigns_of_positive (actualRatioMinors_c4 huB.1 huB.2 hrB.1 hr')

end CKLaneA3V


