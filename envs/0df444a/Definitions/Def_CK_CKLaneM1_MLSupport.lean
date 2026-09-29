-- Prove2me | Definitions.Def_CK_CKLaneM1_MLSupport
-- name    : CK_CKLaneM1_MLSupport
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:07:26.786338+00:00
-- url     : https://prove2.me/theorems/cf872546-fabe-4f0b-b413-d328d3f31ca1
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLSupport` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLSupport` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLSupport` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLSupport (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLSupport.lean)

import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_GeneralCK_SmallMeanMeans
import Definitions.Def_CK_GeneralCK_LowInformationMeans

-- ===== source module CKLaneM1.MLSupport =====
section

/-!
# Lane M1: analytic support for the `same_side.mean_logsum` checker

* `pow2LowerOK` / `pow2UpperOK`: exact `Nat`-power certificates for `r ≤ 2^-u` and `2^-u ≤ r`
  (the construction and proofs follow Lane D, `CKLaneD.FleetBase`; re-stated here so that this lane
  does not depend on Lane D's evolving fleet modules).
* `A_ratio_monotone`: `A r / r` (with `A = atanh`) is monotone on `(0,1)`; together with the corpus
  `SmallMean.Cn_ratio_monotone` these are the two monotone ratios of the archived normalized
  mean-log-sum method (`Δ/d²` and `j/d²` in the coordinates `m`, `ρ = d/(2m)`, `κ = kρ`).
* `Cn_le_half_sq_over_gap'`: `Cn r ≤ r²/(2(1-r²))` (small-bias fallback; the corpus version lives in a
  module that is not compiled in the consumer root, so it is re-derived from `Cn_upper_sharp`).
* Rational point enclosures `cH z ≥ Cn z / z²`, `aLo z ≤ A z / z` with their Boolean side conditions,
  bound to all smaller (resp. larger) arguments by the monotone ratios.

No numerical fact is assumed; every enclosure is recomputed by `CKLaneE.FP` fixed-point logarithms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM1

open GeneralCK Set CKLaneE.FP

/-! ## Exact comparisons of `2^-u` with rationals (after Lane D) -/

/-- `r ≤ 2^-u`, certified by `num(r)^den(u) * 2^num(u) ≤ den(r)^den(u)`. -/
def pow2LowerOK (r u : ℚ) : Bool :=
  decide (0 < r) && decide (0 ≤ u) &&
    Nat.ble (r.num.toNat ^ u.den * 2 ^ u.num.toNat) (r.den ^ u.den)

/-- `2^-u ≤ r`, certified by `den(r)^den(u) ≤ num(r)^den(u) * 2^num(u)`. -/
def pow2UpperOK (r u : ℚ) : Bool :=
  decide (0 < r) && decide (0 ≤ u) &&
    Nat.ble (r.den ^ u.den) (r.num.toNat ^ u.den * 2 ^ u.num.toNat)

theorem rpow_neg_pow_den (u : ℚ) (hu : 0 ≤ u) :
    ((2 : ℝ) ^ (-(u : ℝ))) ^ u.den = ((2 : ℝ) ^ u.num.toNat)⁻¹ := by
  have hden : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_nz
  have hnum : (0 : ℤ) ≤ u.num := Rat.num_nonneg.mpr hu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hu' : (u : ℝ) = (u.num : ℝ) / (u.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have htn : ((u.num.toNat : ℕ) : ℝ) = (u.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hu', show -((u.num : ℝ) / (u.den : ℝ)) * (u.den : ℝ) = -(u.num : ℝ) by field_simp,
    Real.rpow_neg (by norm_num), ← htn, Real.rpow_natCast]

theorem rat_cast_eq_num_div_den (r : ℚ) (hr : 0 < r) :
    (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hr
  have htn : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  rw [htn, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]

theorem pow2LowerOK_sound {r u : ℚ} (h : pow2LowerOK r u = true) :
    (r : ℝ) ≤ (2 : ℝ) ^ (-(u : ℝ)) := by
  unfold pow2LowerOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, hu⟩, hle⟩ := h
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : u.den ≠ 0 := u.den_nz
  rw [← pow_le_pow_iff_left₀ hr'.le hpos.le hM, rpow_neg_pow_den u hu,
    rat_cast_eq_num_div_den r hr, div_pow]
  have hD : (0 : ℝ) < (r.den : ℝ) ^ u.den := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ u.num.toNat := by positivity
  rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ h2]
  exact_mod_cast hle

theorem pow2UpperOK_sound {r u : ℚ} (h : pow2UpperOK r u = true) :
    (2 : ℝ) ^ (-(u : ℝ)) ≤ (r : ℝ) := by
  unfold pow2UpperOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, hu⟩, hle⟩ := h
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : u.den ≠ 0 := u.den_nz
  rw [← pow_le_pow_iff_left₀ hpos.le hr'.le hM, rpow_neg_pow_den u hu,
    rat_cast_eq_num_div_den r hr, div_pow]
  have hD : (0 : ℝ) < (r.den : ℝ) ^ u.den := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ u.num.toNat := by positivity
  rw [le_div_iff₀ hD, inv_mul_eq_div, div_le_iff₀ h2]
  exact_mod_cast hle

/-! ## Monotone ratios -/

theorem A_ratio_monotone : MonotoneOn (fun r => SmallMean.A r / r) (Ioo (0 : ℝ) 1) := by
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r => SmallMean.A r / r)
      ((1 / (1 - r ^ 2) * r - SmallMean.A r * 1) / r ^ 2) r := by
    intro r hr
    exact (SmallMean.hasDerivAt_A (by linarith [hr.1]) hr.2).div (hasDerivAt_id r) hr.1.ne'
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
  · intro r hr
    exact (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hd r hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    apply div_nonneg _ (sq_nonneg r)
    have hA := SmallMean.A_upper hr.1.le hr.2
    have hn : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have e : 1 / (1 - r ^ 2) * r = r / (1 - r ^ 2) := by ring
    rw [e]
    linarith

theorem Cn_le_half_sq_over_gap' {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    SmallMean.Cn r ≤ r ^ 2 / (2 * (1 - r ^ 2)) := by
  have hn : 0 < 1 - r ^ 2 := by nlinarith [hr, hr']
  have hstrong := LowInformation.Cn_upper_sharp hr hr'
  have hstep : r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2)) ≤ r ^ 2 / (2 * (1 - r ^ 2)) := by
    have heq : r ^ 2 / (2 * (1 - r ^ 2)) - (r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2))) =
        5 * r ^ 4 / (12 * (1 - r ^ 2)) := by
      field_simp
      ring
    have hp : 0 ≤ 5 * r ^ 4 / (12 * (1 - r ^ 2)) := by positivity
    linarith
  exact hstrong.trans hstep

/-! ## Rational point enclosures of the two ratios -/

/-- Threshold below which the small-bias bound is used for `Cn z / z²`. -/
def smallZ : ℚ := 1 / 1024

/-- Upper enclosure of `Cn z / z²` at a rational point. -/
def cH (z : ℚ) : ℚ :=
  if smallZ ≤ z then LqHi * (1 - Hlo ((1 - z) / 2)) / (z * z) else 1 / (2 * (1 - z * z))

def cHok (z : ℚ) : Bool :=
  decide (0 < z ∧ z < 1) && (decide (z < smallZ) || ptOk ((1 - z) / 2))

/-- Lower enclosure of `A z / z` at a rational point (`A = atanh`). -/
def aLo (z : ℚ) : ℚ :=
  if z = 0 then 1 else
    if 1 ≤ -lHi ((1 - z) / (1 + z)) / (2 * z) then -lHi ((1 - z) / (1 + z)) / (2 * z) else 1

def aLook (z : ℚ) : Bool :=
  decide (z = 0) || (decide (0 < z ∧ z < 1) && ptOk ((1 - z) / (1 + z)))

theorem Cn_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ SmallMean.Cn r := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]; simp
  · exact (SmallMean.Cn_pos h hr1).le

theorem cH_point {z : ℚ} (h : cHok z = true) :
    SmallMean.Cn (z : ℝ) / (z : ℝ) ^ 2 ≤ ((cH z : ℚ) : ℝ) := by
  unfold cHok at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz0, hz1⟩, hcase⟩ := h
  have hz0' : (0 : ℝ) < z := by exact_mod_cast hz0
  have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
  have hz2 : (0 : ℝ) < (z : ℝ) ^ 2 := by positivity
  unfold cH
  split_ifs with hs
  · -- direct enclosure through `Hlo ((1 - z)/2)`
    have hpt : ptOk ((1 - z) / 2) = true := by
      rcases hcase with hc | hc
      · exact absurd hs (not_le.mpr hc)
      · exact hc
    obtain ⟨hHlo, _⟩ := H_bounds hpt
    have hcast : (((1 - z) / 2 : ℚ) : ℝ) = (1 - (z : ℝ)) / 2 := by push_cast; ring
    rw [hcast] at hHlo
    obtain ⟨_, hL2⟩ := log_two_mem
    have hH1 : H ((1 - (z : ℝ)) / 2) ≤ 1 := H_le_one _
    have hnn : (0 : ℝ) ≤ 1 - H ((1 - (z : ℝ)) / 2) := by linarith
    have hCn : SmallMean.Cn (z : ℝ) ≤ ((LqHi : ℚ) : ℝ) * (1 - ((Hlo ((1 - z) / 2) : ℚ) : ℝ)) := by
      unfold SmallMean.Cn
      exact mul_le_mul hL2 (by linarith) hnn (by linarith [log_two_pos])
    have e : (((LqHi * (1 - Hlo ((1 - z) / 2)) / (z * z) : ℚ)) : ℝ) =
        ((LqHi : ℚ) : ℝ) * (1 - ((Hlo ((1 - z) / 2) : ℚ) : ℝ)) / (z : ℝ) ^ 2 := by
      push_cast; ring
    rw [e]
    exact div_le_div_of_nonneg_right hCn hz2.le
  · have hb := Cn_le_half_sq_over_gap' hz0'.le hz1'
    have hn : (0 : ℝ) < 1 - (z : ℝ) ^ 2 := by nlinarith
    have e : (((1 / (2 * (1 - z * z)) : ℚ)) : ℝ) = 1 / (2 * (1 - (z : ℝ) ^ 2)) := by
      push_cast; ring
    rw [e, div_le_iff₀ hz2]
    calc SmallMean.Cn (z : ℝ) ≤ (z : ℝ) ^ 2 / (2 * (1 - (z : ℝ) ^ 2)) := hb
      _ = 1 / (2 * (1 - (z : ℝ) ^ 2)) * (z : ℝ) ^ 2 := by ring

/-- The point enclosure bounds the ratio at every smaller positive argument. -/
theorem cH_le {z : ℚ} (h : cHok z = true) {ρ : ℝ} (h0 : 0 < ρ) (hρz : ρ ≤ (z : ℝ)) :
    SmallMean.Cn ρ / ρ ^ 2 ≤ ((cH z : ℚ) : ℝ) := by
  have hz1 : (z : ℝ) < 1 := by
    unfold cHok at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact_mod_cast h.1.2
  have hm := SmallMean.Cn_ratio_monotone ⟨h0, by linarith⟩ ⟨lt_of_lt_of_le h0 hρz, hz1.le⟩ hρz
  exact hm.trans (cH_point h)

theorem cH_nonneg {z : ℚ} (h : cHok z = true) : (0 : ℝ) ≤ ((cH z : ℚ) : ℝ) := by
  have hz : (0 : ℝ) < z ∧ (z : ℝ) < 1 := by
    unfold cHok at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by exact_mod_cast h.1.1, by exact_mod_cast h.1.2⟩
  have h1 := cH_point h
  have h2 : 0 ≤ SmallMean.Cn (z : ℝ) / (z : ℝ) ^ 2 :=
    div_nonneg (Cn_nonneg hz.1.le hz.2.le) (sq_nonneg _)
  linarith

theorem one_le_aLo (z : ℚ) : (1 : ℚ) ≤ aLo z := by
  unfold aLo
  split_ifs with h1 h2
  · exact le_rfl
  · exact h2
  · exact le_rfl

/-- The point enclosure bounds `A ρ / ρ` from below at every larger argument in `(0,1)`. -/
theorem aLo_le {z : ℚ} (h : aLook z = true) {ρ : ℝ} (hzρ : (z : ℝ) ≤ ρ) (h0 : 0 < ρ)
    (h1 : ρ < 1) : ((aLo z : ℚ) : ℝ) ≤ SmallMean.A ρ / ρ := by
  have hAρ : 1 ≤ SmallMean.A ρ / ρ := by
    rw [le_div_iff₀ h0, one_mul]
    exact SmallMean.A_lower h0.le h1
  unfold aLook at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with hz | ⟨⟨hz0, hz1⟩, hpt⟩
  · unfold aLo
    rw [if_pos hz]
    simpa using hAρ
  · have hz0' : (0 : ℝ) < z := by exact_mod_cast hz0
    have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
    have hmono := A_ratio_monotone ⟨hz0', hz1'⟩ ⟨h0, h1⟩ hzρ
    simp only at hmono
    -- `A z / z` dominates the certified value
    obtain ⟨_, hlHi, _, _⟩ := ptOk_sound hpt
    have hcast : (((1 - z) / (1 + z) : ℚ) : ℝ) = (1 - (z : ℝ)) / (1 + z) := by push_cast; ring
    rw [hcast] at hlHi
    have hAz : SmallMean.A (z : ℝ) = -Real.log ((1 - (z : ℝ)) / (1 + z)) / 2 := by
      unfold SmallMean.A
      have hp : (0 : ℝ) < (1 + (z : ℝ)) / (1 - z) := by
        apply div_pos <;> linarith
      rw [show (1 - (z : ℝ)) / (1 + z) = ((1 + (z : ℝ)) / (1 - z))⁻¹ by
        field_simp, Real.log_inv]
      ring
    have hval : (-(((lHi ((1 - z) / (1 + z))) : ℚ) : ℝ)) / (2 * (z : ℝ)) ≤
        SmallMean.A (z : ℝ) / (z : ℝ) := by
      rw [hAz, div_div, mul_comm (2 : ℝ) (z : ℝ)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hAz1 : 1 ≤ SmallMean.A (z : ℝ) / (z : ℝ) := by
      rw [le_div_iff₀ hz0', one_mul]
      exact SmallMean.A_lower hz0'.le hz1'
    unfold aLo
    rw [if_neg (by intro hc; rw [hc] at hz0; exact lt_irrefl _ hz0)]
    split_ifs with hc
    · have e : (((-lHi ((1 - z) / (1 + z)) / (2 * z)) : ℚ) : ℝ) =
          (-(((lHi ((1 - z) / (1 + z))) : ℚ) : ℝ)) / (2 * (z : ℝ)) := by push_cast; ring
      rw [e]
      exact hval.trans hmono
    · simpa using hAz1.trans hmono

end CKLaneM1

#check @CKLaneM1.pow2LowerOK_sound
#check @CKLaneM1.pow2UpperOK_sound
#check @CKLaneM1.A_ratio_monotone
#check @CKLaneM1.cH_le
#check @CKLaneM1.aLo_le
#print axioms CKLaneM1.pow2LowerOK_sound
#print axioms CKLaneM1.pow2UpperOK_sound
#print axioms CKLaneM1.A_ratio_monotone
#print axioms CKLaneM1.cH_le
#print axioms CKLaneM1.aLo_le

end


