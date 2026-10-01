-- Prove2me | Definitions.Def_CK_CKLaneM06_CapBonus
-- name    : CK_CKLaneM06_CapBonus
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:04:56.152287+00:00
-- url     : https://prove2.me/theorems/afcd08ba-39a9-4f4d-b4e9-6116e0d82b47
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapBonus` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapBonus` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapBonus` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapBonus (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapBonus.lean)

import Definitions.Def_CK_CKLaneE_EntropyDropSharp

-- ===== source module CKLaneM06.CapBonus =====
section

/-!
# Lane M06: sextic mean-cost bonus `j - 4Δ`

`g(z) = -(2+z) log(1+z) - (2-z) log(1-z) = Σ_{k even ≥ 4} 2(k-2)/(k(k-1)) z^k ≥ z⁴/3 + 4z⁶/15` on `[0,1)`,
and (with `j - 4Δ = [m g(ρ) + (1-m) g(κ)] / ln 2`, `d = 2mρ = 2(1-m)κ`)

  `j - 4Δ ≥ (b-a)²/(12 ln 2) · ((ρ² + ⅘ρ⁴)/m + (κ² + ⅘κ⁴)/(1-m))`,

strengthening `CKLaneE.interiorCost_sub_four_drop` (quartic term only) by the next exact series term
(the archive's positive-series refinement `j ≥ (4 + W_N) Δ`, RESTORED_CAP_PROOF.md §5, truncated).
The proof follows `CKLaneE.g_ge_quartic` / `CKLaneE.interiorCost_sub_four_drop` verbatim with one more
term of the atanh series (`Real.log_div_le_sum_range_add` with `n = 3`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK Set

/-- `g(z) = -(2+z) log(1+z) - (2-z) log(1-z) ≥ z⁴/3 + 4z⁶/15` on `[0,1)`. -/
theorem g_ge_sextic {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    z ^ 4 / 3 + 4 * z ^ 6 / 15 ≤ -(2 + z) * Real.log (1 + z) - (2 - z) * Real.log (1 - z) := by
  have key : MonotoneOn
      (fun t : ℝ => -(2 + t) * Real.log (1 + t) - (2 - t) * Real.log (1 - t) - t ^ 4 / 3 -
        4 * t ^ 6 / 15) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun t => 2 * t / (1 - t ^ 2) - (Real.log (1 + t) - Real.log (1 - t)) - 4 / 3 * t ^ 3 -
        8 / 5 * t ^ 5)
    · intro t ht
      have h1 : (1 + t) ≠ 0 := by have := ht.1; linarith
      have h2 : (1 - t) ≠ 0 := by have := ht.2; linarith
      exact ((((((continuousAt_const.add continuousAt_id).neg).mul
        ((continuousAt_const.add continuousAt_id).log h1)).sub
        ((continuousAt_const.sub continuousAt_id).mul
        ((continuousAt_const.sub continuousAt_id).log h2))).sub
        ((continuousAt_id.pow 4).div_const 3)).sub
        ((continuousAt_const.mul (continuousAt_id.pow 6)).div_const 15)).continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h1 : (0 : ℝ) < 1 + t := by linarith [ht.1]
      have h2 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hA := (((hasDerivAt_id' t).const_add 2).neg).mul (((hasDerivAt_id' t).const_add 1).log h1.ne')
      have hB := ((hasDerivAt_id' t).const_sub 2).mul (((hasDerivAt_id' t).const_sub 1).log h2.ne')
      have hC := ((hasDerivAt_pow 6 t).const_mul (4 : ℝ)).div_const 15
      have hd := ((hA.sub hB).sub ((hasDerivAt_pow 4 t).div_const 3)).sub hC
      have h1' : (1 + t) ≠ 0 := h1.ne'
      have h2' : (1 - t) ≠ 0 := h2.ne'
      have h3 : (1 - t ^ 2) ≠ 0 := by
        have : 0 < 1 - t ^ 2 := by nlinarith
        exact this.ne'
      exact (hd.congr_deriv (by
        rw [show (4:ℕ) - 1 = 3 from rfl, show (6:ℕ) - 1 = 5 from rfl]
        simp only [Pi.neg_apply]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h0 : (0 : ℝ) ≤ t := ht.1.le
      have h1 : t < 1 := ht.2
      have hs := Real.log_div_le_sum_range_add h0 h1 3
      rw [Real.log_div (by linarith) (by linarith)] at hs
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
      norm_num at hs
      have hden : 0 < 1 - t ^ 2 := by nlinarith
      have e : 2 * t / (1 - t ^ 2) = 2 * t + 2 * t ^ 3 + 2 * t ^ 5 + 2 * (t ^ 7 / (1 - t ^ 2)) := by
        field_simp; ring
      rw [e]
      set X := t ^ 7 / (1 - t ^ 2) with hX
      linarith [hs]
  have h := key (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_refl 0, by norm_num⟩)
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hz, hz1⟩) hz
  simp only [add_zero, sub_zero, Real.log_one, mul_zero] at h
  norm_num at h
  linarith

/-- The sextic log-sum bonus: `j - 4Δ ≥ (b-a)²/(12 ln2)·((ρ²+⅘ρ⁴)/m + (κ²+⅘κ⁴)/(1-m))`. -/
theorem interiorCost_sub_four_drop6 {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (b - a) ^ 2 / (12 * Real.log 2) *
        ((((b - a) / (a + b)) ^ 2 + 4 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
          (((b - a) / (2 - a - b)) ^ 2 + 4 / 5 * ((b - a) / (2 - a - b)) ^ 4) / (1 - (a + b) / 2)) ≤
      interiorCost a b - 4 * (H ((a + b) / 2) - (H a + H b) / 2) := by
  have hL := log_two_pos
  have hb0 : 0 < b := ha.trans hab
  have ha1 : a < 1 := hab.trans hb
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hchain := deterministic_entropy_chain ha ha1 hb0 hb
  set ρ := (b - a) / (a + b) with hρ
  set κ := (b - a) / (2 - a - b) with hκ
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hs.le
  have hρ1 : ρ < 1 := (div_lt_one hs).mpr (by linarith)
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) ht.le
  have hκ1 : κ < 1 := (div_lt_one ht).mpr (by linarith)
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  have hpa : a / (a + b) = (1 - ρ) / 2 := by rw [hρ]; field_simp; ring
  have hpb : (1 - b) / (2 - a - b) = (1 - κ) / 2 := by rw [hκ]; field_simp; ring
  rw [hchain, hpa, hpb, CKLaneE.biasDeficit_eq_logs (by linarith) (by linarith),
    CKLaneE.biasDeficit_eq_logs (by linarith) (by linarith)]
  have hane : a ≠ 0 := ha.ne'
  have h1a : 1 - a ≠ 0 := by intro h; linarith
  have h1b : 1 - b ≠ 0 := by intro h; linarith
  have hj : interiorCost a b = (b - a) *
      ((Real.log (1 + ρ) - Real.log (1 - ρ)) + (Real.log (1 + κ) - Real.log (1 - κ))) /
        (2 * Real.log 2) := by
    unfold interiorCost J
    have hp1 : 1 + ρ = 2 * b / (a + b) := by rw [hρ]; field_simp; ring
    have hm1' : 1 - ρ = 2 * a / (a + b) := by rw [hρ]; field_simp; ring
    have hp2 : 1 + κ = 2 * (1 - a) / (2 - a - b) := by rw [hκ]; field_simp; ring
    have hm2 : 1 - κ = 2 * (1 - b) / (2 - a - b) := by rw [hκ]; field_simp; ring
    have l1 : Real.log (1 + ρ) - Real.log (1 - ρ) = Real.log b - Real.log a := by
      rw [hp1, hm1', Real.log_div (by positivity) hsne, Real.log_div (by positivity) hsne,
        Real.log_mul (by norm_num) hb0.ne', Real.log_mul (by norm_num) hane]
      ring
    have l2 : Real.log (1 + κ) - Real.log (1 - κ) = Real.log (1 - a) - Real.log (1 - b) := by
      rw [hp2, hm2, Real.log_div (by positivity) htne, Real.log_div (by positivity) htne,
        Real.log_mul (by norm_num) h1a, Real.log_mul (by norm_num) h1b]
      ring
    rw [l1, l2, Real.log_div h1a hane, Real.log_div h1b hb0.ne']
    field_simp
    ring
  rw [hj]
  have g1 := g_ge_sextic hρ0 hρ1
  have g2 := g_ge_sextic hκ0 hκ1
  have hm : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hd1 : b - a = 2 * ((a + b) / 2) * ρ := by rw [hρ]; field_simp
  have hd2 : b - a = 2 * (1 - (a + b) / 2) * κ := by rw [hκ]; field_simp; ring
  set m := (a + b) / 2 with hmdef
  have lhs_eq : (b - a) ^ 2 / (12 * Real.log 2) *
      ((ρ ^ 2 + 4 / 5 * ρ ^ 4) / m + (κ ^ 2 + 4 / 5 * κ ^ 4) / (1 - m)) =
      (m * (ρ ^ 4 / 3 + 4 * ρ ^ 6 / 15) + (1 - m) * (κ ^ 4 / 3 + 4 * κ ^ 6 / 15)) / Real.log 2 := by
    have e1 : (b - a) ^ 2 * ((ρ ^ 2 + 4 / 5 * ρ ^ 4) / m) = 4 * m * (ρ ^ 4 + 4 / 5 * ρ ^ 6) := by
      rw [hd1]; field_simp; ring
    have e2 : (b - a) ^ 2 * ((κ ^ 2 + 4 / 5 * κ ^ 4) / (1 - m)) =
        4 * (1 - m) * (κ ^ 4 + 4 / 5 * κ ^ 6) := by
      rw [hd2]; field_simp; ring
    have : (b - a) ^ 2 / (12 * Real.log 2) *
        ((ρ ^ 2 + 4 / 5 * ρ ^ 4) / m + (κ ^ 2 + 4 / 5 * κ ^ 4) / (1 - m)) =
        ((b - a) ^ 2 * ((ρ ^ 2 + 4 / 5 * ρ ^ 4) / m) +
          (b - a) ^ 2 * ((κ ^ 2 + 4 / 5 * κ ^ 4) / (1 - m))) / (12 * Real.log 2) := by ring
    rw [this, e1, e2]
    field_simp
    ring
  have rhs_eq : (b - a) * ((Real.log (1 + ρ) - Real.log (1 - ρ)) +
        (Real.log (1 + κ) - Real.log (1 - κ))) / (2 * Real.log 2) -
      4 * (m * (((1 + ρ) * Real.log (1 + ρ) + (1 - ρ) * Real.log (1 - ρ)) / (2 * Real.log 2)) +
        (1 - m) * (((1 + κ) * Real.log (1 + κ) + (1 - κ) * Real.log (1 - κ)) / (2 * Real.log 2))) =
      (m * (-(2 + ρ) * Real.log (1 + ρ) - (2 - ρ) * Real.log (1 - ρ)) +
        (1 - m) * (-(2 + κ) * Real.log (1 + κ) - (2 - κ) * Real.log (1 - κ))) / Real.log 2 := by
    have e : (b - a) * ((Real.log (1 + ρ) - Real.log (1 - ρ)) + (Real.log (1 + κ) - Real.log (1 - κ))) =
        2 * m * ρ * (Real.log (1 + ρ) - Real.log (1 - ρ)) +
          2 * (1 - m) * κ * (Real.log (1 + κ) - Real.log (1 - κ)) := by
      have : (b - a) * (Real.log (1 + ρ) - Real.log (1 - ρ)) =
          2 * m * ρ * (Real.log (1 + ρ) - Real.log (1 - ρ)) := by rw [← hd1]
      have h2' : (b - a) * (Real.log (1 + κ) - Real.log (1 - κ)) =
          2 * (1 - m) * κ * (Real.log (1 + κ) - Real.log (1 - κ)) := by rw [← hd2]
      linear_combination this + h2'
    rw [e]
    field_simp
    ring
  rw [lhs_eq, rhs_eq]
  apply div_le_div_of_nonneg_right _ hL.le
  have := mul_le_mul_of_nonneg_left g1 hm.le
  have := mul_le_mul_of_nonneg_left g2 hm1.le
  linarith

end CKLaneM06.Cap

end


