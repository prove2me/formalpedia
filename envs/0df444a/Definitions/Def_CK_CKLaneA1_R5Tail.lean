-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Tail
-- name    : CK_CKLaneA1_R5Tail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T05:29:38.546985+00:00
-- url     : https://prove2.me/theorems/a28cf6ef-4760-46ea-83d6-8eefcd218142
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Tail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Tail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Tail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Tail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Tail.lean)

import Definitions.Def_CK_CKLaneA1_R5Cell

-- ===== source module CKLaneA1.R5Tail =====
section

/-!
# CKLaneA1.R5Tail — the large-`A` tail of CE-stat row 5

For `A ≥ 4` (and `t ≥ 1/100`): `W = X(t) ≤ 61/10`, `Θ(W) ≥ W·Θ(61/10)/(61/10)`, and the log-increment
bound `Θ(A+2W) − Θ(A) ≤ (13/6)·log(1 + 2W/A) ≤ 13W/(3A) ≤ 13W/12` give `D(A,W,λ) > 0`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

/-- Contact point for `Θ(61/10) ≥ Slo`. -/
def tailN : ℕ := 10919866974

theorem tail_data : thLoOK (61 / 10) tailN = true ∧ okN T0N = true ∧ 0 < (vd T0N).Hlo ∧
    (98 / 100 : ℚ) / (2 * (vd T0N).Hlo) ≤ 61 / 10 ∧ (13 / 12 : ℚ) < (vd tailN).Slo * 10 / 61 := by
  decide +kernel

theorem tail_sound {a t A W lam : ℝ} (P : PtFacts a t A W lam) (ht : (1 : ℝ) / 100 ≤ t)
    (hA4 : 4 ≤ A) : 0 < Dst A W lam := by
  obtain ⟨hth, hok, hHl, hW61, hS⟩ := tail_data
  have hW0 := P.W0
  have hA0 := P.hA
  have hT0 : ((dyq T0N : ℚ) : ℝ) ≤ 1 / 100 := by
    unfold dyq T0N; push_cast; norm_num
  have hHlo : (((vd T0N).Hlo : ℚ) : ℝ) ≤ H t := by
    have h1 := VD.Hlo_le (vd_sound hok)
    rw [vd_v] at h1
    exact h1.trans (H_mono (dyq_pos hok).le (hT0.trans ht) P.ht2.le)
  have hHl0 : (0 : ℝ) < (((vd T0N).Hlo : ℚ) : ℝ) := by exact_mod_cast hHl
  have hW61R : (98 / 100 : ℝ) / (2 * (((vd T0N).Hlo : ℚ) : ℝ)) ≤ 61 / 10 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hW61
    push_cast at h'
    exact h'
  have hWle : W ≤ 61 / 10 := by
    rw [P.hW]; unfold Xf
    calc (1 - 2 * t) / (2 * H t) ≤ (98 / 100) / (2 * (((vd T0N).Hlo : ℚ) : ℝ)) :=
          div_le_div₀ (by norm_num) (by linarith) (by linarith) (by linarith)
      _ ≤ 61 / 10 := hW61R
  -- Θ(W) ≥ W · Slo · 10/61
  have h61 : ((61 / 10 : ℚ) : ℝ) = 61 / 10 := by norm_num
  have hth' := thLoOK_sound hth (x := ((61 / 10 : ℚ) : ℝ)) le_rfl
  rw [h61] at hth'
  have hratio := theta_ge_ratio hW0 hWle
  have hTW : W * ((((vd tailN).Slo : ℚ) : ℝ) * 10 / 61) ≤ e8Theta W := by
    refine le_trans ?_ hratio
    apply mul_le_mul_of_nonneg_left _ hW0.le
    have : (((vd tailN).Slo : ℚ) : ℝ) * 10 / 61 = (((vd tailN).Slo : ℚ) : ℝ) / (61 / 10) := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hth' (by norm_num)
  -- Θ(A + 2λW) ≤ Θ(A + 2W)
  have hle1 : A + 2 * lam * W ≤ A + 2 * W := by
    have := mul_le_mul_of_nonneg_right P.hlam1.le hW0.le
    linarith
  have hpos1 : 0 < A + 2 * lam * W := by
    have := mul_pos (mul_pos two_pos P.hlam0) hW0; linarith
  have hmono : e8Theta (A + 2 * lam * W) ≤ e8Theta (A + 2 * W) :=
    strictMonoOn_e8Theta_pos.monotoneOn hpos1 (show 0 < A + 2 * W by linarith) hle1
  -- log increment
  have hinc := ZeroCapLeftStationaryLogIncrementTail.theta_increment_log_bound hA0
    (show A ≤ A + 2 * W by linarith)
  have hlog : Real.log ((A + 2 * W) / A) ≤ 2 * W / A := by
    have := Real.log_le_sub_one_of_pos (show 0 < (A + 2 * W) / A by positivity)
    have e : (A + 2 * W) / A - 1 = 2 * W / A := by field_simp; ring
    linarith
  have hWA : 2 * W / A ≤ W / 2 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]
    nlinarith
  have hSR : (13 / 12 : ℝ) < (((vd tailN).Slo : ℚ) : ℝ) * 10 / 61 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hS
    push_cast at h'
    exact h'
  have hprod : 0 < W * ((((vd tailN).Slo : ℚ) : ℝ) * 10 / 61 - 13 / 12) :=
    mul_pos hW0 (by linarith)
  unfold Dst
  nlinarith [hTW, hmono, hinc, hlog, hWA, hprod]

#print axioms tail_sound

end CKLaneA1.R5

end


