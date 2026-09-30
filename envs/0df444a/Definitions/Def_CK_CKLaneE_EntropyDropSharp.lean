-- Prove2me | Definitions.Def_CK_CKLaneE_EntropyDropSharp
-- name    : CK_CKLaneE_EntropyDropSharp
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:01:19.743859+00:00
-- url     : https://prove2.me/theorems/19f3f5f5-4484-4c04-9bd7-fd00b4f11504
-- title:
--   Courtade–Kumar proof module `CKLaneE.EntropyDropSharp` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.EntropyDropSharp` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.EntropyDropSharp` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.EntropyDropSharp (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/EntropyDropSharp.lean)

import Definitions.Def_CK_CKLaneE_EntropyDropBound
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module CKLaneE.EntropyDropSharp =====
section

/-!
# Lane E: sharper diagonal expansions of the entropy drop and of `j - 4Δ`

* `entropyDrop_le_normalized6`: `Δ ≤ (b-a)²/(8 ln2)·((1+ρ²/6+⅖ρ⁴)/m + (1+κ²/6+⅖κ⁴)/(1-m))`
  (quintic log bounds; relative error `O(ρ⁴)`).
* `interiorCost_sub_four_drop`: `j - 4Δ ≥ (b-a)²/(12 ln2)·(ρ²/m + κ²/(1-m))`, from
  `j - 4Δ = (1/ln2)[m g(ρ) + (1-m) g(κ)]`, `g(z) = -(2+z)log(1+z) - (2-z)log(1-z) ≥ z⁴/3`.
Here `m = (a+b)/2`, `ρ = (b-a)/(a+b)`, `κ = (b-a)/(2-a-b)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE

open GeneralCK Set

theorem log_one_add_le_quintic {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1 + z) ≤ z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5 := by
  have key : MonotoneOn
      (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 5 / 5 - Real.log (1 + t)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => t ^ 5 / (1 + t))
    · intro t ht
      have h1 : (1 + t) ≠ 0 := by have := ht.out; linarith
      exact (((((continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)).add
        ((continuousAt_id.pow 3).div_const 3)).sub ((continuousAt_id.pow 4).div_const 4)).add
        ((continuousAt_id.pow 5).div_const 5)).sub
        ((continuousAt_const.add continuousAt_id).log h1)).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0 : ℝ) < t := ht
      have h1 : (0 : ℝ) < 1 + t := by linarith
      have hd := ((((((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub ((hasDerivAt_pow 4 t).div_const 4)).add
        ((hasDerivAt_pow 5 t).div_const 5)).sub
        (((hasDerivAt_id' t).const_add 1).log h1.ne'))
      have h1' : (1 + t) ≠ 0 := h1.ne'
      exact (hd.congr_deriv (by
        rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl,
          show (4:ℕ) - 1 = 3 from rfl, show (5:ℕ) - 1 = 4 from rfl]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0 : ℝ) < t := ht
      positivity
  have h := key (show (0 : ℝ) ∈ Ici (0 : ℝ) from Set.mem_Ici.mpr le_rfl)
    (show z ∈ Ici (0 : ℝ) from hz) hz
  simp only [add_zero, Real.log_one] at h
  norm_num at h
  linarith

theorem log_one_sub_le_quintic {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Real.log (1 - z) ≤ -z - z ^ 2 / 2 - z ^ 3 / 3 - z ^ 4 / 4 - z ^ 5 / 5 := by
  have key : MonotoneOn
      (fun t : ℝ => -t - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / 4 - t ^ 5 / 5 - Real.log (1 - t)) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) (f' := fun t => t ^ 5 / (1 - t))
    · intro t ht
      have h1 : (1 - t) ≠ 0 := by have := ht.2; linarith
      exact ((((((continuousAt_id.neg).sub ((continuousAt_id.pow 2).div_const 2)).sub
        ((continuousAt_id.pow 3).div_const 3)).sub ((continuousAt_id.pow 4).div_const 4)).sub
        ((continuousAt_id.pow 5).div_const 5)).sub
        ((continuousAt_const.sub continuousAt_id).log h1)).continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hd := (((((((hasDerivAt_id' t).neg).sub ((hasDerivAt_pow 2 t).div_const 2)).sub
        ((hasDerivAt_pow 3 t).div_const 3)).sub ((hasDerivAt_pow 4 t).div_const 4)).sub
        ((hasDerivAt_pow 5 t).div_const 5)).sub
        (((hasDerivAt_id' t).const_sub 1).log h1.ne'))
      have h1' : (1 - t) ≠ 0 := h1.ne'
      exact (hd.congr_deriv (by
        rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl,
          show (4:ℕ) - 1 = 3 from rfl, show (5:ℕ) - 1 = 4 from rfl]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h0 : (0 : ℝ) < t := ht.1
      have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      positivity
  have h := key (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_refl 0, by norm_num⟩)
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hz, hz1⟩) hz
  simp only [neg_zero, sub_zero, Real.log_one] at h
  norm_num at h
  linarith

/-- `2 log 2 · (1 - H((1-z)/2)) = (1+z) log(1+z) + (1-z) log(1-z)`. -/
theorem biasDeficit_eq_logs {z : ℝ} (hz1 : z < 1) (hz0 : -1 < z) :
    1 - H ((1 - z) / 2) =
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / (2 * Real.log 2) := by
  have hL := log_two_pos
  have h1z : 0 < 1 - z := by linarith
  have h1z' : 0 < 1 + z := by linarith
  have hq : Real.log ((1 - z) / 2) = Real.log (1 - z) - Real.log 2 :=
    Real.log_div h1z.ne' (by norm_num)
  have hq' : Real.log (1 - (1 - z) / 2) = Real.log (1 + z) - Real.log 2 := by
    rw [show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
    exact Real.log_div h1z'.ne' (by norm_num)
  rw [H_eq_logs, hq, hq']
  field_simp
  ring

theorem biasDeficit_le_poly6 {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    1 - H ((1 - z) / 2) ≤ (z ^ 2 + z ^ 4 / 6 + 2 / 5 * z ^ 6) / (2 * Real.log 2) := by
  have hL := log_two_pos
  have h1z : 0 < 1 - z := by linarith
  have h1z' : 0 < 1 + z := by linarith
  rw [biasDeficit_eq_logs hz1 (by linarith)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha := mul_le_mul_of_nonneg_left (log_one_add_le_quintic hz) h1z'.le
  have hb := mul_le_mul_of_nonneg_left (log_one_sub_le_quintic hz hz1) h1z.le
  nlinarith [ha, hb]

/-- Normalized entropy-drop bound with quartic-exact coefficients. -/
theorem entropyDrop_le_normalized6 {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤
      (b - a) ^ 2 / (8 * Real.log 2) *
        ((1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
          (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
            (1 - (a + b) / 2)) := by
  have hL := log_two_pos
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hchain := deterministic_entropy_chain ha (hab.trans hb) (ha.trans hab) hb
  set ρ := (b - a) / (a + b) with hρ
  set κ := (b - a) / (2 - a - b) with hκ
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hs.le
  have hρ1 : ρ < 1 := (div_lt_one hs).mpr (by linarith)
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) ht.le
  have hκ1 : κ < 1 := (div_lt_one ht).mpr (by linarith)
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  have htne' : 2 - (a + b) ≠ 0 := by intro h; linarith
  have hpa : a / (a + b) = (1 - ρ) / 2 := by rw [hρ]; field_simp; ring
  have hpb : (1 - b) / (2 - a - b) = (1 - κ) / 2 := by rw [hκ]; field_simp; ring
  rw [hchain, hpa, hpb]
  have h1 := biasDeficit_le_poly6 hρ0 hρ1
  have h2 := biasDeficit_le_poly6 hκ0 hκ1
  have hm : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hm1ne : 1 - (a + b) / 2 ≠ 0 := hm1.ne'
  have e1 : (a + b) / 2 * ((ρ ^ 2 + ρ ^ 4 / 6 + 2 / 5 * ρ ^ 6) / (2 * Real.log 2)) =
      (b - a) ^ 2 / (8 * Real.log 2) * ((1 + ρ ^ 2 / 6 + 2 / 5 * ρ ^ 4) / ((a + b) / 2)) := by
    rw [hρ]; field_simp; ring
  have e2 : (1 - (a + b) / 2) * ((κ ^ 2 + κ ^ 4 / 6 + 2 / 5 * κ ^ 6) / (2 * Real.log 2)) =
      (b - a) ^ 2 / (8 * Real.log 2) * ((1 + κ ^ 2 / 6 + 2 / 5 * κ ^ 4) / (1 - (a + b) / 2)) := by
    rw [hκ]; field_simp; ring
  have k1 := mul_le_mul_of_nonneg_left h1 hm.le
  have k2 := mul_le_mul_of_nonneg_left h2 hm1.le
  rw [e1] at k1
  rw [e2] at k2
  rw [mul_add]
  linarith

/-- `g(z) = -(2+z) log(1+z) - (2-z) log(1-z) ≥ z⁴/3` on `[0,1)`. -/
theorem g_ge_quartic {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    z ^ 4 / 3 ≤ -(2 + z) * Real.log (1 + z) - (2 - z) * Real.log (1 - z) := by
  have key : MonotoneOn
      (fun t : ℝ => -(2 + t) * Real.log (1 + t) - (2 - t) * Real.log (1 - t) - t ^ 4 / 3) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun t => 2 * t / (1 - t ^ 2) - (Real.log (1 + t) - Real.log (1 - t)) - 4 / 3 * t ^ 3)
    · intro t ht
      have h1 : (1 + t) ≠ 0 := by have := ht.1; linarith
      have h2 : (1 - t) ≠ 0 := by have := ht.2; linarith
      exact (((((continuousAt_const.add continuousAt_id).neg).mul
        ((continuousAt_const.add continuousAt_id).log h1)).sub
        ((continuousAt_const.sub continuousAt_id).mul
        ((continuousAt_const.sub continuousAt_id).log h2))).sub
        ((continuousAt_id.pow 4).div_const 3)).continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h1 : (0 : ℝ) < 1 + t := by linarith [ht.1]
      have h2 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hA := (((hasDerivAt_id' t).const_add 2).neg).mul (((hasDerivAt_id' t).const_add 1).log h1.ne')
      have hB := ((hasDerivAt_id' t).const_sub 2).mul (((hasDerivAt_id' t).const_sub 1).log h2.ne')
      have hd := (hA.sub hB).sub ((hasDerivAt_pow 4 t).div_const 3)
      have h1' : (1 + t) ≠ 0 := h1.ne'
      have h2' : (1 - t) ≠ 0 := h2.ne'
      have h3 : (1 - t ^ 2) ≠ 0 := by
        have : 0 < 1 - t ^ 2 := by nlinarith
        exact this.ne'
      exact (hd.congr_deriv (by
        rw [show (4:ℕ) - 1 = 3 from rfl]
        simp only [Pi.neg_apply]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h0 : (0 : ℝ) ≤ t := ht.1.le
      have h1 : t < 1 := ht.2
      have hs := Real.log_div_le_sum_range_add h0 h1 2
      have hq : (1 + t) / (1 - t) > 0 := div_pos (by linarith) (by linarith)
      rw [Real.log_div (by linarith) (by linarith)] at hs
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
      norm_num at hs
      have hden : 0 < 1 - t ^ 2 := by nlinarith
      have e : 2 * t / (1 - t ^ 2) = 2 * t + 2 * t ^ 3 + 2 * (t ^ 5 / (1 - t ^ 2)) := by
        field_simp; ring
      rw [e]
      set X := t ^ 5 / (1 - t ^ 2) with hX
      linarith [hs]
  have h := key (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_refl 0, by norm_num⟩)
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hz, hz1⟩) hz
  simp only [add_zero, sub_zero, Real.log_one, mul_zero] at h
  norm_num at h
  linarith

/-- The log-sum bonus: `j - 4Δ ≥ (b-a)²/(12 ln2)·(ρ²/m + κ²/(1-m))`. -/
theorem interiorCost_sub_four_drop {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (b - a) ^ 2 / (12 * Real.log 2) *
        (((b - a) / (a + b)) ^ 2 / ((a + b) / 2) + ((b - a) / (2 - a - b)) ^ 2 / (1 - (a + b) / 2)) ≤
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
  rw [hchain, hpa, hpb, biasDeficit_eq_logs (by linarith) (by linarith),
    biasDeficit_eq_logs (by linarith) (by linarith)]
  -- j in atanh form
  have hane : a ≠ 0 := ha.ne'
  have h1a : 1 - a ≠ 0 := by intro h; linarith
  have h1b : 1 - b ≠ 0 := by intro h; linarith
  have h2b : 2 - b * 2 ≠ 0 := by intro h; linarith
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
  have g1 := g_ge_quartic hρ0 hρ1
  have g2 := g_ge_quartic hκ0 hκ1
  have hm : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  -- (b-a) = 2 m ρ = 2 (1-m) κ
  have hd1 : b - a = 2 * ((a + b) / 2) * ρ := by rw [hρ]; field_simp
  have hd2 : b - a = 2 * (1 - (a + b) / 2) * κ := by rw [hκ]; field_simp; ring
  set m := (a + b) / 2 with hmdef
  -- target rewritten through the two decompositions
  have lhs_eq : (b - a) ^ 2 / (12 * Real.log 2) * (ρ ^ 2 / m + κ ^ 2 / (1 - m)) =
      (m * (ρ ^ 4 / 3) + (1 - m) * (κ ^ 4 / 3)) / Real.log 2 := by
    have e1 : (b - a) ^ 2 * (ρ ^ 2 / m) = 4 * m * ρ ^ 4 := by
      rw [hd1]; field_simp; ring
    have e2 : (b - a) ^ 2 * (κ ^ 2 / (1 - m)) = 4 * (1 - m) * κ ^ 4 := by
      rw [hd2]; field_simp; ring
    have : (b - a) ^ 2 / (12 * Real.log 2) * (ρ ^ 2 / m + κ ^ 2 / (1 - m)) =
        ((b - a) ^ 2 * (ρ ^ 2 / m) + (b - a) ^ 2 * (κ ^ 2 / (1 - m))) / (12 * Real.log 2) := by ring
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

end CKLaneE

#check @CKLaneE.entropyDrop_le_normalized6
#check @CKLaneE.g_ge_quartic
#check @CKLaneE.interiorCost_sub_four_drop
#print axioms CKLaneE.entropyDrop_le_normalized6
#print axioms CKLaneE.g_ge_quartic
#print axioms CKLaneE.interiorCost_sub_four_drop

end


