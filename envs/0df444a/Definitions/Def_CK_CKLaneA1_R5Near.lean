-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Near
-- name    : CK_CKLaneA1_R5Near
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:24:10.646903+00:00
-- url     : https://prove2.me/theorems/8d8ec79e-8e7c-4989-a4e9-70e869a7843b
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Near` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Near` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Near` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Near (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Near.lean)

import Definitions.Def_CK_CKLaneA1_R5Near_part00

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

/-- Powers of a small nonnegative number. -/
theorem pow_succ_le_small {u ε : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ ε) :
    ∀ n : ℕ, u ^ (n + 1) ≤ ε ^ n * u
  | 0 => by simp
  | n + 1 => by
    have ih := pow_succ_le_small hu0 hu n
    have hε : 0 ≤ ε := hu0.trans hu
    calc u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
      _ ≤ (ε ^ n * u) * ε := mul_le_mul ih hu hu0 (by positivity)
      _ = ε ^ (n + 1) * u := by ring

set_option maxHeartbeats 1000000 in
/-- The core polynomial estimate. -/
theorem near_core {L h k z : ℝ} (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808)
    (hz0 : 0 < z) (hz1 : z ≤ 1 / 2400)
    (he1 : z / 2 - 3 / 4 * z ^ 2 ≤ L - h) (he2 : L - h ≤ z / 2 + 7 / 5 * z ^ 2)
    (hm1 : z / 2 ≤ k - L) (hm2 : k - L ≤ z / 2 + z ^ 2) :
    8 / L * (1 - 243 / 100 * z) ≤ 4 * h ^ 3 * (2 * k - z) / (L ^ 2 * (1 - z) ^ 2 * k ^ 3) ∧
      4 * h ^ 3 * (2 * k - z) / (L ^ 2 * (1 - z) ^ 2 * k ^ 3) ≤ 8 / L * (1 - 178 / 100 * z) := by
  have hL0 : 0 < L := by linarith
  have hL7 : L ≤ 7 / 10 := by linarith
  obtain ⟨u, rfl⟩ : ∃ u, z = L * u := ⟨z / L, by field_simp⟩
  obtain ⟨p, rfl⟩ : ∃ p, h = L * p := ⟨h / L, by field_simp⟩
  obtain ⟨q, rfl⟩ : ∃ q, k = L * q := ⟨k / L, by field_simp⟩
  have hu0 : 0 < u := by
    by_contra hn; push Not at hn; nlinarith
  have hu1 : u ≤ 1 / 1600 := by
    by_contra hn; push Not at hn
    have : L * (1 / 1600) < L * u := mul_lt_mul_of_pos_left hn hL0
    linarith
  -- normalized bounds
  have hLu2 : L * u ^ 2 ≤ 7 / 10 * u ^ 2 := mul_le_mul_of_nonneg_right hL7 (sq_nonneg u)
  have hp_lo : 1 - u / 2 - 49 / 50 * u ^ 2 ≤ p := by
    have h' : L * (1 - p) ≤ L * (u / 2 + 7 / 5 * (L * u ^ 2)) := by
      have e1 : L * (1 - p) = L - L * p := by ring
      have e2 : L * (u / 2 + 7 / 5 * (L * u ^ 2)) = L * u / 2 + 7 / 5 * (L * u) ^ 2 := by ring
      rw [e1, e2]; exact he2
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hp_hi : p ≤ 1 - u / 2 + 53 / 100 * u ^ 2 := by
    have h' : L * (u / 2 - 3 / 4 * (L * u ^ 2)) ≤ L * (1 - p) := by
      have e1 : L * (1 - p) = L - L * p := by ring
      have e2 : L * (u / 2 - 3 / 4 * (L * u ^ 2)) = L * u / 2 - 3 / 4 * (L * u) ^ 2 := by ring
      rw [e1, e2]; exact he1
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hq_lo : 1 + u / 2 ≤ q := by
    have h' : L * (u / 2) ≤ L * (q - 1) := by
      have e1 : L * (q - 1) = L * q - L := by ring
      have e2 : L * (u / 2) = L * u / 2 := by ring
      rw [e1, e2]; exact hm1
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hq_hi : q ≤ 1 + u / 2 + 7 / 10 * u ^ 2 := by
    have h' : L * (q - 1) ≤ L * (u / 2 + L * u ^ 2) := by
      have e1 : L * (q - 1) = L * q - L := by ring
      have e2 : L * (u / 2 + L * u ^ 2) = L * u / 2 + (L * u) ^ 2 := by ring
      rw [e1, e2]; exact hm2
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hp0 : 0 < p := by nlinarith
  have hq0 : 0 < q := by linarith
  have hz1' : 0 < 1 - L * u := by nlinarith
  -- normalization
  have key : 4 * (L * p) ^ 3 * (2 * (L * q) - L * u) / (L ^ 2 * (1 - L * u) ^ 2 * (L * q) ^ 3) =
      8 / L * (p ^ 3 * (q - u / 2) / ((1 - L * u) ^ 2 * q ^ 3)) := by
    field_simp
    ring
  rw [key]
  -- small powers
  have hpw := pow_succ_le_small hu0.le hu1
  have w1 := hpw 1
  have w2 := hpw 2
  have w3 := hpw 3
  have w4 := hpw 4
  have w5 := hpw 5
  have w6 := hpw 6
  have w7 := hpw 7
  have w8 := hpw 8
  norm_num at w1 w2 w3 w4 w5 w6 w7 w8
  have g2 : 0 ≤ u ^ 2 := by positivity
  have g3 : 0 ≤ u ^ 3 := by positivity
  have g4 : 0 ≤ u ^ 4 := by positivity
  have g5 : 0 ≤ u ^ 5 := by positivity
  have g6 : 0 ≤ u ^ 6 := by positivity
  have g7 : 0 ≤ u ^ 7 := by positivity
  have g8 : 0 ≤ u ^ 8 := by positivity
  have g9 : 0 ≤ u ^ 9 := by positivity
  have hden : 0 < (1 - L * u) ^ 2 * q ^ 3 := by positivity
  have hLlo : (0.6931471803 : ℝ) * u ≤ L * u := mul_le_mul_of_nonneg_right hL1.le hu0.le
  have hLhi : L * u ≤ (0.6931471808 : ℝ) * u := mul_le_mul_of_nonneg_right hL2.le hu0.le
  constructor
  · -- lower bound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ hden]
    have poly : (1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2 *
        (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 ≤ (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 := by
      ring_nf
      ring_nf at w1 w2 w3 w4 w5 w6 w7 w8
      linarith
    have m1 : (1 - 243 / 100 * (L * u)) * (1 - L * u) ^ 2 ≤
        (1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2 := by
      apply mul_le_mul (by linarith) _ (by positivity) (by nlinarith)
      exact pow_le_pow_left₀ hz1'.le (by linarith) 2
    have m2 : q ^ 3 ≤ (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 := pow_le_pow_left₀ hq0.le hq_hi 3
    have m3 : (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by nlinarith) hp_lo 3
    have m4 : p ^ 3 ≤ p ^ 3 * (q - u / 2) := by
      have : 1 ≤ q - u / 2 := by linarith
      nlinarith [pow_pos hp0 3]
    have hA : 0 ≤ 1 - 243 / 100 * (L * u) := by nlinarith
    calc (1 - 243 / 100 * (L * u)) * ((1 - L * u) ^ 2 * q ^ 3)
        = ((1 - 243 / 100 * (L * u)) * (1 - L * u) ^ 2) * q ^ 3 := by ring
      _ ≤ ((1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2) *
            (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 :=
          mul_le_mul m1 m2 (by positivity) (by nlinarith)
      _ ≤ (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 := poly
      _ ≤ p ^ 3 := m3
      _ ≤ p ^ 3 * (q - u / 2) := m4
  · -- upper bound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hden]
    have poly : (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 * (1 + 7 / 10 * u ^ 2) ≤
        (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 * (1 + u / 2) ^ 3 := by
      ring_nf
      ring_nf at w1 w2 w3 w4 w5 w6 w7 w8
      linarith
    have m1 : (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 ≤
        (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 := by
      apply mul_le_mul (by linarith) _ (by nlinarith) (by nlinarith)
      exact pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    have m2 : (1 + u / 2) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hq_lo 3
    have m3 : p ^ 3 ≤ (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 := pow_le_pow_left₀ hp0.le hp_hi 3
    have m4 : q - u / 2 ≤ 1 + 7 / 10 * u ^ 2 := by linarith
    have hB : 0 ≤ (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 := by
      apply mul_nonneg (by nlinarith) (by positivity)
    calc p ^ 3 * (q - u / 2) ≤ (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 * (1 + 7 / 10 * u ^ 2) :=
          mul_le_mul m3 m4 (by linarith) (pow_nonneg (by nlinarith [sq_nonneg u]) 3)
      _ ≤ (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 * (1 + u / 2) ^ 3 := poly
      _ ≤ (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 * q ^ 3 :=
          mul_le_mul m1 m2 (by positivity) hB
      _ = (1 - 178 / 100 * (L * u)) * ((1 - L * u) ^ 2 * q ^ 3) := by ring

/-- **Near-`1/2` bounds for `Psi`.** -/
theorem psi_near {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) (hy : 1 - 2 * v ≤ 201 / 10000) :
    8 / Real.log 2 * (1 - 243 / 100 * (1 - 2 * v) ^ 2) ≤ Psi v ∧
      Psi v ≤ 8 / Real.log 2 * (1 - 178 / 100 * (1 - 2 * v) ^ 2) := by
  obtain ⟨he1, he2⟩ := eta_bounds hv0 hv
  obtain ⟨hm1, hm2⟩ := mu_bounds hv0 hv
  rw [psi_eq hv0 hv]
  have hy0 : 0 < 1 - 2 * v := by linarith
  have hz1 : (1 - 2 * v) ^ 2 ≤ 1 / 2400 := by nlinarith
  have hq4 : (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) ≤ 16 / 15 * (1 - 2 * v) ^ 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hy0 4]
  have e4 : (1 - 2 * v) ^ 4 = ((1 - 2 * v) ^ 2) ^ 2 := by ring
  have hq5 : (1 - 2 * v) ^ 2 / (2 * (1 - (1 - 2 * v) ^ 2)) ≤
      (1 - 2 * v) ^ 2 / 2 + ((1 - 2 * v) ^ 2) ^ 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith [pow_pos hy0 2]
  have hg4 : 0 ≤ (1 - 2 * v) ^ 4 := by positivity
  refine near_core Real.log_two_gt_d9 Real.log_two_lt_d9 (by positivity) hz1 ?_ ?_ hm1 (hm2.trans hq5)
  · rw [← e4]; linarith
  · rw [← e4]; linarith

#print axioms psi_near

end CKLaneA1.R5


