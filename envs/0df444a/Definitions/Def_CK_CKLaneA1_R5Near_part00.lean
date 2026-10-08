-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Near_part00
-- name    : CK_CKLaneA1_R5Near_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T07:14:23.138001+00:00
-- url     : https://prove2.me/theorems/146a9d25-2dcb-43a3-a064-d352d140c309
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Near (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Near (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Near (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Near (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Near (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneA1_R5Cell

/-!
# CKLaneA1.R5Near — `Psi = Θ'(contact)` near `v = 1/2` (analytic)

With `y = 1 − 2v`, `z = y²`, `L = log 2`, `η = L − hn v`, `μ = kap v − L`:
* Taylor: `|2η − y² − (2/3)y⁴| ≤ 2y⁴/(1−y)` (`eta_bounds`), `z/2 ≤ μ ≤ z/(2(1−z))` (`mu_bounds`);
* `Psi v = 4 hn³ (2 kap − z) / (L² (1−z)² kap³)` (`psi_eq`);
* for `y ≤ 201/10000`: `θ₀(1 − 2.43 z) ≤ Psi v ≤ θ₀(1 − 1.78 z)`, `θ₀ = 8/L` (`psi_near`).
The core estimate (`near_core`) is a univariate polynomial inequality in `u = z/L` after normalizing
`p = hn/L`, `q = kap/L`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

theorem log_taylor3 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    |Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y) ∧
      |Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y) := by
  have h1 := Real.abs_log_sub_add_sum_range_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1) 3
  have h2 := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1) 3
  rw [abs_of_nonneg hy0] at h1
  rw [abs_neg, abs_of_nonneg hy0, sub_neg_eq_add] at h2
  have e1 : ∑ i ∈ Finset.range 3, y ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 - y) =
      Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  have e2 : ∑ i ∈ Finset.range 3, (-y) ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 + y) =
      Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem two_eta_eq {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    2 * (Real.log 2 - hn v) = (1 + (1 - 2 * v)) * Real.log (1 + (1 - 2 * v)) +
      (1 - (1 - 2 * v)) * Real.log (1 - (1 - 2 * v)) := by
  have e1 : 1 + (1 - 2 * v) = 2 * (1 - v) := by ring
  have e2 : 1 - (1 - 2 * v) = 2 * v := by ring
  rw [e1, e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) hv0.ne']
  unfold hn
  ring

theorem eta_bounds {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    (1 - 2 * v) ^ 2 / 2 + (1 - 2 * v) ^ 4 / 3 - (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) ≤
        Real.log 2 - hn v ∧
      Real.log 2 - hn v ≤
        (1 - 2 * v) ^ 2 / 2 + (1 - 2 * v) ^ 4 / 3 + (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) := by
  have hy0 : 0 ≤ 1 - 2 * v := by linarith
  have hy1 : 1 - 2 * v < 1 := by linarith
  obtain ⟨h1, h2⟩ := log_taylor3 hy0 hy1
  have he := two_eta_eq hv0 (by linarith)
  generalize 1 - 2 * v = y at *
  rw [abs_le] at h1 h2
  have key : 2 * (Real.log 2 - hn v) - y ^ 2 - 2 / 3 * y ^ 4 =
      (1 + y) * (Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3)) +
        (1 - y) * (Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3)) := by
    rw [he]; ring
  have a1 := mul_le_mul_of_nonneg_left h2.2 (show (0 : ℝ) ≤ 1 + y by linarith)
  have a2 := mul_le_mul_of_nonneg_left h1.2 (show (0 : ℝ) ≤ 1 - y by linarith)
  have b1 := mul_le_mul_of_nonneg_left h2.1 (show (0 : ℝ) ≤ 1 + y by linarith)
  have b2 := mul_le_mul_of_nonneg_left h1.1 (show (0 : ℝ) ≤ 1 - y by linarith)
  have e3 : (1 + y) * (y ^ 4 / (1 - y)) + (1 - y) * (y ^ 4 / (1 - y)) = 2 * (y ^ 4 / (1 - y)) := by
    ring
  have e4 : (1 + y) * -(y ^ 4 / (1 - y)) + (1 - y) * -(y ^ 4 / (1 - y)) =
      -(2 * (y ^ 4 / (1 - y))) := by ring
  constructor <;> linarith

theorem mu_bounds {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    (1 - 2 * v) ^ 2 / 2 ≤ kap v - Real.log 2 ∧
      kap v - Real.log 2 ≤ (1 - 2 * v) ^ 2 / (2 * (1 - (1 - 2 * v) ^ 2)) := by
  have hq : 0 < 1 - (1 - 2 * v) ^ 2 := by nlinarith
  have e : kap v - Real.log 2 = -Real.log (1 - (1 - 2 * v) ^ 2) / 2 := by
    unfold kap
    have h4 : v * (1 - v) = (1 - (1 - 2 * v) ^ 2) / 4 := by ring
    rw [h4, Real.log_div hq.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [e]
  generalize (1 - 2 * v) ^ 2 = z at *
  have hq' : 1 - z ≠ 0 := hq.ne'
  have l1 := Real.log_le_sub_one_of_pos hq
  have l2 := Real.one_sub_inv_le_log_of_pos hq
  constructor
  · linarith
  · have e2 : 1 + z / (1 - z) = (1 - z)⁻¹ := by
      rw [inv_eq_one_div, eq_div_iff hq', add_mul, div_mul_cancel₀ _ hq']; ring
    rw [← e2] at l2
    have e3 : z / (2 * (1 - z)) = z / (1 - z) / 2 := by rw [div_div, mul_comm (1 - z) 2]
    rw [e3]
    linarith

theorem psi_eq {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    Psi v = 4 * hn v ^ 3 * (2 * kap v - (1 - 2 * v) ^ 2) /
      (Real.log 2 ^ 2 * (1 - (1 - 2 * v) ^ 2) ^ 2 * kap v ^ 3) := by
  unfold Psi
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hHv : H v = hn v / Real.log 2 := by rw [hn_eq_H_mul_log]; field_simp
  rw [hHv]
  have hk : kap v ≠ 0 := (kap_pos hv0 hv).ne'
  have hq : 1 - (1 - 2 * v) ^ 2 ≠ 0 := by nlinarith
  have e : 4 * v * (1 - v) = 1 - (1 - 2 * v) ^ 2 := by ring
  rw [e]
  first | (field_simp; done) | (field_simp; ring)


end CKLaneA1.R5


