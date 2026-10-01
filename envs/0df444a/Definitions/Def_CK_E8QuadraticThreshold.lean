-- Prove2me | Definitions.Def_CK_E8QuadraticThreshold
-- name    : CK_E8QuadraticThreshold
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:11:42.242002+00:00
-- url     : https://prove2.me/theorems/9fbe645d-d88b-4b34-9590-691a0d820c5a
-- title:
--   Courtade–Kumar proof module `E8QuadraticThreshold` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8QuadraticThreshold` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8QuadraticThreshold` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8QuadraticThreshold (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8QuadraticThreshold.lean)

import Definitions.Def_CK_E8EntropyQuotientBound

-- ===== source module E8QuadraticThreshold =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set
open Certificates.E8TAxisStableScalar

theorem ell_ge_half_one_add_sq {a : ℝ} (ha : 0 < a) :
    (1 + r a ^ 2) / 2 ≤ ell a := by
  have hlog := Real.log_le_sub_one_of_pos (q_pos a)
  rw [← one_sub_r_sq] at hlog
  have htwo := Certificates.PilotData.log_two.1
  norm_num only [div_one] at htwo
  rw [← biasB_r]
  unfold Certificates.Reflection.biasB
  rw [← pow_two]
  linarith

theorem stable_vertex_bound {a : ℝ} (ha : 0 < a) :
    2 * (r a ^ 2 / (2 * ell a - r a ^ 2)) ≤ 3 / ell a := by
  have ht0 : 0 ≤ r a ^ 2 := sq_nonneg _
  have ht1 : r a ^ 2 ≤ 1 := by nlinarith [r_pos ha, r_lt_one a]
  have hk := ell_ge_half_one_add_sq ha
  have hden := stable_gap_pos ha
  rw [← mul_div_assoc, div_le_div_iff₀ hden (ell_pos ha)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ ell a - (1 + r a ^ 2) / 2)
    (by linarith : 0 ≤ 3 - r a ^ 2)]

theorem compactFactor_mono_on_branch {k t : ℝ} (ht : 0 ≤ t)
    (hbranch : 2 * (t / (2 * k - t)) ≤ 3 / k) :
    MonotoneOn (compactFactor k t) (Ici (1 / 3)) := by
  intro d hd e he hde
  have hcoeff : 0 ≤ 6 * (d + e) - 4 * (1 + 2 * (t / (2 * k - t)) - 3 / k) := by
    change (1 / 3 : ℝ) ≤ d at hd
    change (1 / 3 : ℝ) ≤ e at he
    linarith
  have hmul := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hde)) hcoeff
  have hid : compactFactor k t e - compactFactor k t d =
      t * (e - d) * (6 * (d + e) - 4 * (1 + 2 * (t / (2 * k - t)) - 3 / k)) := by
    unfold compactFactor
    ring
  linarith

theorem actual_compactFactor_mono {a : ℝ} (ha : 0 < a) :
    MonotoneOn (compactFactor (ell a) (r a ^ 2)) (Ici (1 / 3)) :=
  compactFactor_mono_on_branch (sq_nonneg _) (stable_vertex_bound ha)

noncomputable def quadraticVertex (k t : ℝ) : ℝ :=
  (1 + 2 * (t / (2 * k - t)) - 3 / k) / 3

noncomputable def quadraticMinimum (k t : ℝ) : ℝ :=
  compactFactor k t (quadraticVertex k t)

theorem compactFactor_completed_square (k t d : ℝ) :
    compactFactor k t d =
      6 * t * (d - quadraticVertex k t) ^ 2 + quadraticMinimum k t := by
  simp only [quadraticMinimum, compactFactor, quadraticVertex]
  ring

noncomputable def quadraticThreshold (k t : ℝ) : ℝ :=
  quadraticVertex k t + Real.sqrt (-quadraticMinimum k t / (6 * t))

theorem compactFactor_nonneg_iff_threshold {k t d : ℝ}
    (ht : 0 < t) (hd : quadraticVertex k t ≤ d) :
    0 ≤ compactFactor k t d ↔ quadraticThreshold k t ≤ d := by
  have ht6 : 0 < 6 * t := by positivity
  have hdiff : 0 ≤ d - quadraticVertex k t := sub_nonneg.mpr hd
  rw [compactFactor_completed_square]
  constructor
  · intro hf
    have hs : -quadraticMinimum k t / (6 * t) ≤ (d - quadraticVertex k t) ^ 2 := by
      apply (div_le_iff₀ ht6).2
      nlinarith
    have hh := (Real.sqrt_le_left hdiff).mpr hs
    unfold quadraticThreshold
    linarith
  · intro hh
    have hs : Real.sqrt (-quadraticMinimum k t / (6 * t)) ≤ d - quadraticVertex k t := by
      unfold quadraticThreshold at hh
      linarith
    have hh := (div_le_iff₀ ht6).mp ((Real.sqrt_le_left hdiff).mp hs)
    nlinarith

theorem actual_compactFactor_nonneg_iff_threshold {a : ℝ} (ha : 0 < a) :
    0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a) ↔
      quadraticThreshold (ell a) (r a ^ 2) ≤ entropyQuotient a := by
  apply compactFactor_nonneg_iff_threshold (pow_pos (r_pos ha) 2)
  have hv := stable_vertex_bound ha
  have hd := entropyQuotient_ge_third ha
  unfold quadraticVertex
  linarith

/-- The one residual scalar inequality, with its quadratic branch already proved. -/
theorem ratio_monotone_iff_entropy_threshold :
    MonotoneOn ratio (Ioi 0) ↔ ∀ a : ℝ, 0 < a →
      quadraticThreshold (ell a) (r a ^ 2) ≤ entropyQuotient a := by
  rw [ratio_monotone_iff_compactFactor_nonneg]
  exact forall_congr' (fun a => forall_congr' (fun ha =>
    actual_compactFactor_nonneg_iff_threshold ha))

#print axioms ell_ge_half_one_add_sq
#print axioms stable_vertex_bound
#print axioms actual_compactFactor_mono
#print axioms compactFactor_completed_square
#print axioms actual_compactFactor_nonneg_iff_threshold
#print axioms ratio_monotone_iff_entropy_threshold

end GeneralCK.E8RatioMonotonicity

end


