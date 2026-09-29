-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSignedSplit
-- name    : CK_GeneralCK_PsiSignedSplit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:40.548389+00:00
-- url     : https://prove2.me/theorems/c504b977-6450-435e-9ed6-5c824e20ce9c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSignedSplit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSignedSplit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSignedSplit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSignedSplit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSignedSplit.lean)

import Definitions.Def_CK_GeneralCK_LogSum

-- ===== source module GeneralCK.PsiSignedSplit =====
section

/-!
# Exact control of the signed entropy split

The factor-eight argument retains the two child phi values. Its remaining
split term is `c * barrier t - k * tilt t`, with `|t| < 1`. This module
proves its exact minimum by an identity with two nonnegative relative
entropies. No interval or endpoint-support-plane premise is used here.
-/

namespace GeneralCK.PsiSignedSplit

noncomputable def capacity (z : ℝ) : ℝ :=
  ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / 2

noncomputable def barrier (t : ℝ) : ℝ := -Real.log (1 - t ^ 2)

noncomputable def tilt (t : ℝ) : ℝ :=
  (Real.log (1 + t) - Real.log (1 - t)) / 2

noncomputable def objective (c k t : ℝ) : ℝ := c * barrier t - k * tilt t

theorem log_one_sub_sq {t : ℝ} (ht : |t| < 1) :
    Real.log (1 - t ^ 2) = Real.log (1 + t) + Real.log (1 - t) := by
  have h := abs_lt.mp ht
  rw [show 1 - t ^ 2 = (1 + t) * (1 - t) by ring]
  exact Real.log_mul (by linarith) (by linarith)

/-- The exact remainder is a scaled Bernoulli relative entropy. -/
theorem objective_add_capacity_eq (c z t : ℝ) (hz : |z| < 1) (ht : |t| < 1) :
    objective c (2 * c * z) t + 2 * c * capacity z =
      c * (LogSum.massD (1 + z) (1 + t) +
        LogSum.massD (1 - z) (1 - t)) := by
  have hz' := abs_lt.mp hz
  have ht' := abs_lt.mp ht
  unfold objective barrier tilt capacity LogSum.massD
  rw [log_one_sub_sq ht,
    Real.log_div (by linarith : 1 + z ≠ 0) (by linarith : 1 + t ≠ 0),
    Real.log_div (by linarith : 1 - z ≠ 0) (by linarith : 1 - t ≠ 0)]
  ring

theorem objective_lower {c z t : ℝ} (hc : 0 ≤ c)
    (hz : |z| < 1) (ht : |t| < 1) :
    -(2 * c * capacity z) ≤ objective c (2 * c * z) t := by
  have hz' := abs_lt.mp hz
  have ht' := abs_lt.mp ht
  have h₁ := LogSum.massD_nonneg (x := 1 + z) (y := 1 + t)
    (by linarith) (by linarith)
  have h₂ := LogSum.massD_nonneg (x := 1 - z) (y := 1 - t)
    (by linarith) (by linarith)
  have h := mul_nonneg hc (add_nonneg h₁ h₂)
  rw [← objective_add_capacity_eq c z t hz ht] at h
  linarith

theorem objective_at_minimizer (c z : ℝ) (hz : |z| < 1) :
    objective c (2 * c * z) z = -(2 * c * capacity z) := by
  have hz' := abs_lt.mp hz
  have hp : 1 + z ≠ 0 := by linarith
  have hm : 1 - z ≠ 0 := by linarith
  have h := objective_add_capacity_eq c z z hz hz
  simp [LogSum.massD, hp, hm] at h
  linarith

/-- This supplies an attained minimum over the whole open split interval. -/
theorem objective_minimum {c k : ℝ} (hc : 0 < c) (hk : |k| < 2 * c) :
    |k / (2 * c)| < 1 ∧
      objective c k (k / (2 * c)) = -(2 * c * capacity (k / (2 * c))) ∧
      ∀ t : ℝ, |t| < 1 →
        objective c k (k / (2 * c)) ≤ objective c k t := by
  have hd : 0 < 2 * c := by positivity
  have hz : |k / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos hd]
    exact (div_lt_one hd).mpr hk
  have he : 2 * c * (k / (2 * c)) = k := mul_div_cancel₀ k hd.ne'
  have hv := objective_at_minimizer c (k / (2 * c)) hz
  rw [he] at hv
  refine ⟨hz, hv, ?_⟩
  intro t ht
  rw [hv]
  have h := objective_lower hc.le hz ht
  rwa [he] at h

theorem capacity_nonneg {z : ℝ} (hz : |z| < 1) : 0 ≤ capacity z := by
  have h := objective_lower (c := 1) (t := 0) (by norm_num) hz (by norm_num)
  norm_num [objective, barrier, tilt] at h
  linarith

theorem barrier_nonneg {t : ℝ} (ht : |t| < 1) : 0 ≤ barrier t := by
  have hh := abs_lt.mp ht
  have hp : 0 < (1 + t) * (1 - t) := mul_pos (by linarith) (by linarith)
  have hp' : 0 < 1 - t ^ 2 := by nlinarith
  exact neg_nonneg.mpr (Real.log_nonpos hp'.le (by nlinarith [sq_nonneg t]))

/-- Increasing the coefficient of the barrier reduces the worst possible loss.
This is proved from the attained minimum, without differentiating an inverse. -/
theorem loss_antitone {c₁ c₂ k : ℝ} (hc₁ : 0 < c₁) (hcc : c₁ ≤ c₂)
    (hk : |k| < 2 * c₁) :
    2 * c₂ * capacity (k / (2 * c₂)) ≤
      2 * c₁ * capacity (k / (2 * c₁)) := by
  have hc₂ : 0 < c₂ := hc₁.trans_le hcc
  obtain ⟨hz₁, hv₁, hmin₁⟩ := objective_minimum hc₁ hk
  obtain ⟨hz₂, hv₂, _⟩ := objective_minimum (k := k) hc₂ (by linarith)
  have hmin := hmin₁ (k / (2 * c₂)) hz₂
  have hb := mul_le_mul_of_nonneg_right hcc (barrier_nonneg hz₂)
  have hm : objective c₁ k (k / (2 * c₂)) ≤
      objective c₂ k (k / (2 * c₂)) := by
    unfold objective
    linarith
  rw [hv₁] at hmin
  rw [hv₂] at hm
  linarith

end GeneralCK.PsiSignedSplit

#print axioms GeneralCK.PsiSignedSplit.objective_add_capacity_eq
#print axioms GeneralCK.PsiSignedSplit.objective_minimum
#print axioms GeneralCK.PsiSignedSplit.loss_antitone

end


