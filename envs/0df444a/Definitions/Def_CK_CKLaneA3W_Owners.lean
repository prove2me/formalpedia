-- Prove2me | Definitions.Def_CK_CKLaneA3W_Owners
-- name    : CK_CKLaneA3W_Owners
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:46:24.530776+00:00
-- url     : https://prove2.me/theorems/d7ef1105-bfcf-49d5-b11f-e0df9cc89bc8
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.Owners` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.Owners` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.Owners` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.Owners (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/Owners.lean)

import Definitions.Def_CK_CKLaneA3W_FinalPos

/-!
# CKLaneA3W.Owners — extended high-u owners (t ≤ 7/50, i.e. u ≥ 9/25) and ChartOwners slots (Lane A3)

Unconditional consequences of the TM certificate (`FinalPos`):
* `highU_coef_pos`, `highU_m11_pos`, `highU_kdet_pos` on `0 < t ≤ 3/25`, `0 < ρ < 1`;
* `scaledHighUOwner : HighU.ScaledHighUOwner`, `actualHighUOwner : HighU.ActualHighUOwner`;
* `actualRatioMinors_high` for `19/50 ≤ u < 1/2` (includes the edge `u = 19/50`);
* slots with the exact `ChartOwners` field types: `corner0..corner3`, `diagonal7..diagonal9`,
  and the staircase boxes `stair1..stair3` (stair0 has the type of corner0).
-/

set_option linter.unusedVariables false

namespace CKLaneA3W

open GeneralCK GeneralCK.Correction

theorem dom_of {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 7 / 50) (h2 : 0 < ρ) (h3 : ρ < 1) : Dom t ρ := by
  refine ⟨h0, ?_, h2, h3⟩
  have : ((Tq : ℚ) : ℝ) = 7 / 50 := by norm_num [Tq]
  rw [this]; exact h1

theorem highU_coef_pos {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 7 / 50) (h2 : 0 < ρ) (h3 : ρ < 1) :
    0 < HighU.actualDetGapCoefficient (1 / 2 - t) (1 / 2 - (1 - ρ) * t) :=
  coef_pos_dom t ρ (dom_of h0 h1 h2 h3)

theorem highU_m11_pos {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 7 / 50) (h2 : 0 < ρ) (h3 : ρ < 1) :
    0 < Natural.m11 (1 / 2 - t) (1 / 2 - (1 - ρ) * t) :=
  m11_pos_dom t ρ (dom_of h0 h1 h2 h3)

theorem highU_kdet_pos {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 7 / 50) (h2 : 0 < ρ) (h3 : ρ < 1) :
    0 < Natural.kdet (1 / 2 - t) (1 / 2 - (1 - ρ) * t) := by
  have hd := dom_of h0 h1 h2 h3
  rw [HighU.kdet_eq_gap_sq_mul_coefficient (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)]
  have hc := highU_coef_pos h0 h1 h2 h3
  have hg : 0 < (1 / 2 - (1 - ρ) * t) - (1 / 2 - t) := sub_pos.mpr (dom_u_lt_w hd)
  positivity

theorem scaledHighUOwner : HighU.ScaledHighUOwner := by
  intro t ρ h0 h1 h2 h3
  have hm := highU_m11_pos h0 (by linarith) h2 h3
  have hk := highU_kdet_pos h0 (by linarith) h2 h3
  exact ⟨div_pos hm (by positivity), div_pos hk (by positivity)⟩

theorem actualHighUOwner : HighU.ActualHighUOwner :=
  HighU.actualHighU_of_scaledOwner scaledHighUOwner

theorem actualRatioMinors_high {u ρ : ℝ} (hu : 9 / 25 ≤ u) (hu' : u < 1 / 2) (h2 : 0 < ρ)
    (h3 : ρ < 1) : ActualRatioMinorsPositive u ρ := by
  have ht0 : 0 < 1 / 2 - u := by linarith
  have ht1 : 1 / 2 - u ≤ 7 / 50 := by linarith
  have e1 : 1 / 2 - (1 / 2 - u) = u := by ring
  have e2 : 1 / 2 - (1 - ρ) * (1 / 2 - u) = u + ρ * (1 / 2 - u) := by ring
  have hm := highU_m11_pos ht0 ht1 h2 h3
  have hk := highU_kdet_pos ht0 ht1 h2 h3
  rw [e1, e2] at hm hk
  exact minors_of_pos (by linarith) hu' h2 h3 hm hk

theorem actualRatioMinors_edge {ρ : ℝ} (h2 : 0 < ρ) (h3 : ρ < 1) :
    ActualRatioMinorsPositive (9 / 25) ρ :=
  actualRatioMinors_high (le_refl _) (by norm_num) h2 h3

theorem signsOnBox_high {u0 u1 r0 r1 : ℝ} (h : (9 : ℝ) / 25 ≤ u0) :
    Complement.SignsOnBox u0 u1 r0 r1 := by
  intro u ρ _ hu' hr hr' huB _
  exact Complement.ratioSigns_of_positive (actualRatioMinors_high (le_trans h huB.1) hu' hr hr')

theorem corner0 : Complement.SignsOnBox (41 / 100) (1 / 2) 0 1 := signsOnBox_high (by norm_num)
theorem corner1 : Complement.SignsOnBox (2 / 5) (1 / 2) (1 / 20) 1 := signsOnBox_high (by norm_num)
theorem corner2 : Complement.SignsOnBox (39 / 100) (1 / 2) (1 / 5) 1 := signsOnBox_high (by norm_num)
theorem corner3 : Complement.SignsOnBox (19 / 50) (1 / 2) (2 / 5) 1 := signsOnBox_high (by norm_num)
theorem diagonal7 : Complement.SignsOnBox (19 / 50) (39 / 100) 0 (2 / 5) := signsOnBox_high (by norm_num)
theorem diagonal8 : Complement.SignsOnBox (39 / 100) (2 / 5) 0 (1 / 5) := signsOnBox_high (by norm_num)
theorem diagonal9 : Complement.SignsOnBox (2 / 5) (41 / 100) 0 (1 / 20) := signsOnBox_high (by norm_num)
theorem stair1 : Complement.SignsOnBox (2 / 5) (41 / 100) (1 / 20) 1 := signsOnBox_high (by norm_num)
theorem stair2 : Complement.SignsOnBox (39 / 100) (2 / 5) (1 / 5) 1 := signsOnBox_high (by norm_num)
theorem stair3 : Complement.SignsOnBox (19 / 50) (39 / 100) (2 / 5) 1 := signsOnBox_high (by norm_num)
theorem corner4 : Complement.SignsOnBox (37 / 100) (1 / 2) (7 / 10) 1 := signsOnBox_high (by norm_num)
theorem corner5 : Complement.SignsOnBox (9 / 25) (1 / 2) (9 / 10) 1 := signsOnBox_high (by norm_num)
theorem diagonal5 : Complement.SignsOnBox (9 / 25) (37 / 100) 0 (1 / 10) := signsOnBox_high (by norm_num)
theorem diagonal6 : Complement.SignsOnBox (37 / 100) (19 / 50) 0 (3 / 10) := signsOnBox_high (by norm_num)
theorem directC5 : Complement.SignsOnBox (9 / 25) (37 / 100) (1 / 10) (9 / 10) := signsOnBox_high (by norm_num)
theorem directC6 : Complement.SignsOnBox (37 / 100) (19 / 50) (3 / 10) (7 / 10) := signsOnBox_high (by norm_num)

end CKLaneA3W


