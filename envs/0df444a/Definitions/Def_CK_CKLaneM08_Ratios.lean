-- Prove2me | Definitions.Def_CK_CKLaneM08_Ratios
-- name    : CK_CKLaneM08_Ratios
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:46:29.378668+00:00
-- url     : https://prove2.me/theorems/52366615-0ebb-4c1c-95ef-1fe0cf566d5d
-- title:
--   Courtade–Kumar proof module `CKLaneM08.Ratios` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM08.Ratios` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM08.Ratios` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM08.Ratios (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM08/Ratios.lean)

import Definitions.Def_CK_CKLaneE_CertLS

-- ===== source module CKLaneM08.Ratios =====
section

/-!
# Lane M08: normalized log-sum ratio functions (analytic part of the entropy-endpoint kernel)

For `0 < a < b < 1` put `m = (a+b)/2`, `d = b - a`, `ρ = d/(a+b)`, `κ = d/(2-a-b)`.  With
`atanhR z = (log(1+z) - log(1-z))/2` and `gR z = ((1+z) log(1+z) + (1-z) log(1-z))/2` (nats):

* `log 2 · (H m - (H a + H b)/2) = m·gR ρ + (1-m)·gR κ`             (`log2_mul_drop_eq`)
* `log 2 · interiorCost a b = d·(atanhR ρ + atanhR κ)`               (`log2_mul_cost_eq`)
* `Aratio z = atanhR z / z` and `Gratio z = gR z / z^2` are monotone on `(0,1)`
  (`Aratio_mono`, `Gratio_mono`), via `ψ z = z/(1-z²) - atanhR z ≥ 0` and
  `φ z = z·atanhR z - 2 gR z ≥ 0`.

Normalized forms: `H m - C = d²(Gratio ρ/(4m) + Gratio κ/(4(1-m)))/log 2` and
`interiorCost a b = d²(Aratio ρ/(2m) + Aratio κ/(2(1-m)))/log 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM08

open GeneralCK Set

noncomputable def atanhR (z : ℝ) : ℝ := (Real.log (1 + z) - Real.log (1 - z)) / 2

noncomputable def gR (z : ℝ) : ℝ := ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / 2

noncomputable def Aratio (z : ℝ) : ℝ := atanhR z / z

noncomputable def Gratio (z : ℝ) : ℝ := gR z / (z * z)

@[simp] theorem atanhR_zero : atanhR 0 = 0 := by simp [atanhR]

@[simp] theorem gR_zero : gR 0 = 0 := by simp [gR]

theorem hasDerivAt_log_one_add {z : ℝ} (hz : -1 < z) :
    HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + z)) z := by
  have h1 : (1 + z) ≠ 0 := by linarith
  have := ((hasDerivAt_id' z).const_add 1).log h1
  simpa using this

theorem hasDerivAt_log_one_sub {z : ℝ} (hz : z < 1) :
    HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - z)) z := by
  have h1 : (1 - z) ≠ 0 := by linarith
  have := ((hasDerivAt_id' z).const_sub 1).log h1
  simpa using this

theorem hasDerivAt_atanhR {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    HasDerivAt atanhR (1 / (1 - z ^ 2)) z := by
  have h := ((hasDerivAt_log_one_add hz0).sub (hasDerivAt_log_one_sub hz1)).div_const 2
  have h1 : (1 + z) ≠ 0 := by linarith
  have h2 : (1 - z) ≠ 0 := by linarith
  have h3 : (1 - z ^ 2) ≠ 0 := by
    have : 1 - z ^ 2 = (1 + z) * (1 - z) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  exact h.congr_deriv (by field_simp; ring)

theorem hasDerivAt_gR {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    HasDerivAt gR (atanhR z) z := by
  have hA := ((hasDerivAt_id' z).const_add 1).mul (hasDerivAt_log_one_add hz0)
  have hB := ((hasDerivAt_id' z).const_sub 1).mul (hasDerivAt_log_one_sub hz1)
  have h := (hA.add hB).div_const 2
  have h1 : (1 + z) ≠ 0 := by linarith
  have h2 : (1 - z) ≠ 0 := by linarith
  exact h.congr_deriv (by unfold atanhR; field_simp; ring)

/-- `ψ z = z/(1-z²) - atanhR z` is nonnegative on `[0,1)`. -/
theorem psi_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : atanhR z ≤ z / (1 - z ^ 2) := by
  let ψ : ℝ → ℝ := fun y => y / ((1 - y) * (1 + y)) - atanhR y
  have hd : ∀ y : ℝ, -1 < y → y < 1 →
      HasDerivAt ψ (2 * y ^ 2 / ((1 - y) * (1 + y)) ^ 2) y := by
    intro y hy0 hy1
    have hne1 : (1 - y) ≠ 0 := by linarith
    have hne2 : (1 + y) ≠ 0 := by linarith
    have hne : (1 - y) * (1 + y) ≠ 0 := mul_ne_zero hne1 hne2
    have hq := (hasDerivAt_id' y).div
      (((hasDerivAt_id' y).const_sub 1).mul ((hasDerivAt_id' y).const_add 1)) hne
    have h := hq.sub (hasDerivAt_atanhR hy0 hy1)
    have h3 : (1 - y ^ 2) ≠ 0 := by
      have : 1 - y ^ 2 = (1 - y) * (1 + y) := by ring
      rw [this]; exact hne
    exact h.congr_deriv (by simp only [Pi.mul_apply]; field_simp; ring)
  have hmono : MonotoneOn ψ (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun y => 2 * y ^ 2 / ((1 - y) * (1 + y)) ^ 2)
    · intro y hy
      exact (hd y (by linarith [hy.1]) hy.2).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      exact (hd y (by linarith [hy.1]) hy.2).hasDerivWithinAt
    · intro y _
      positivity
  have h := hmono ⟨le_rfl, by norm_num⟩ ⟨hz0, hz1⟩ hz0
  simp only [ψ, atanhR_zero] at h
  norm_num at h
  have e : z / (1 - z ^ 2) = z / ((1 - z) * (1 + z)) := by ring_nf
  rw [e]
  linarith

/-- `φ z = z·atanhR z - 2 gR z` is nonnegative on `[0,1)`. -/
theorem phi_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 2 * gR z ≤ z * atanhR z := by
  let φ : ℝ → ℝ := fun y => y * atanhR y - 2 * gR y
  have hd : ∀ y : ℝ, -1 < y → y < 1 →
      HasDerivAt φ (y / (1 - y ^ 2) - atanhR y) y := by
    intro y hy0 hy1
    have h := ((hasDerivAt_id' y).mul (hasDerivAt_atanhR hy0 hy1)).sub
      ((hasDerivAt_gR hy0 hy1).const_mul 2)
    exact h.congr_deriv (by ring)
  have hmono : MonotoneOn φ (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun y => y / (1 - y ^ 2) - atanhR y)
    · intro y hy
      exact (hd y (by linarith [hy.1]) hy.2).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      exact (hd y (by linarith [hy.1]) hy.2).hasDerivWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      have := psi_nonneg hy.1.le hy.2
      linarith
  have h := hmono ⟨le_rfl, by norm_num⟩ ⟨hz0, hz1⟩ hz0
  simp only [φ, atanhR_zero, gR_zero] at h
  norm_num at h
  linarith

theorem Aratio_mono : MonotoneOn Aratio (Ioo 0 1) := by
  have hd : ∀ y : ℝ, 0 < y → y < 1 →
      HasDerivAt Aratio ((y / (1 - y ^ 2) - atanhR y) / y ^ 2) y := by
    intro y hy0 hy1
    have h := (hasDerivAt_atanhR (by linarith) hy1).div (hasDerivAt_id' y) hy0.ne'
    have hne : (1 - y ^ 2) ≠ 0 := by
      have : 0 < 1 - y ^ 2 := by nlinarith
      exact this.ne'
    exact h.congr_deriv (by field_simp)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
    (f' := fun y => (y / (1 - y ^ 2) - atanhR y) / y ^ 2)
  · intro y hy
    exact (hd y hy.1 hy.2).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hd y hy.1 hy.2).hasDerivWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    have := psi_nonneg hy.1.le hy.2
    apply div_nonneg (by linarith) (by positivity)

theorem Gratio_mono : MonotoneOn Gratio (Ioo 0 1) := by
  have hd : ∀ y : ℝ, 0 < y → y < 1 →
      HasDerivAt Gratio ((y * atanhR y - 2 * gR y) / y ^ 3) y := by
    intro y hy0 hy1
    have hy2 : y * y ≠ 0 := by positivity
    have h := (hasDerivAt_gR (by linarith) hy1).div ((hasDerivAt_id' y).mul (hasDerivAt_id' y)) hy2
    exact h.congr_deriv (by simp only [Pi.mul_apply]; field_simp; ring)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
    (f' := fun y => (y * atanhR y - 2 * gR y) / y ^ 3)
  · intro y hy
    exact (hd y hy.1 hy.2).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hd y hy.1 hy.2).hasDerivWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    have := phi_nonneg hy.1.le hy.2
    apply div_nonneg (by linarith) (by have := hy.1; positivity)

/-! ## Law identities -/

/-- `log 2 · (1 - H((1-z)/2)) = gR z`. -/
theorem log2_mul_one_sub_H_half {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    Real.log 2 * (1 - H ((1 - z) / 2)) = gR z := by
  rw [CKLaneE.H_eq_logs]
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have e1 : 1 - (1 - z) / 2 = (1 + z) / 2 := by ring
  rw [e1]
  have h1 : (0 : ℝ) < 1 - z := by linarith
  have h2 : (0 : ℝ) < 1 + z := by linarith
  rw [Real.log_div h1.ne' (by norm_num), Real.log_div h2.ne' (by norm_num)]
  unfold gR
  field_simp
  ring

theorem gR_nonneg {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) : 0 ≤ gR z := by
  rw [← log2_mul_one_sub_H_half hz0 hz1]
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := H_le_one ((1 - z) / 2)
  exact mul_nonneg hL.le (by linarith)

theorem Gratio_nonneg {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : 0 ≤ Gratio z := by
  unfold Gratio
  exact div_nonneg (gR_nonneg (by linarith) hz1) (by positivity)

theorem log2_mul_drop_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Real.log 2 * (H ((a + b) / 2) - (H a + H b) / 2) =
      (a + b) / 2 * gR ((b - a) / (a + b)) + (1 - (a + b) / 2) * gR ((b - a) / (2 - a - b)) := by
  have hb0 : 0 < b := ha.trans hab
  have ha1 : a < 1 := hab.trans hb
  rw [deterministic_entropy_chain ha ha1 hb0 hb]
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have e1 : a / (a + b) = (1 - (b - a) / (a + b)) / 2 := by field_simp; ring
  have e2 : (1 - b) / (2 - a - b) = (1 - (b - a) / (2 - a - b)) / 2 := by field_simp; ring
  rw [e1, e2]
  have hρ0 : -1 < (b - a) / (a + b) := by
    rw [lt_div_iff₀ hs]; linarith
  have hρ1 : (b - a) / (a + b) < 1 := by
    rw [div_lt_one hs]; linarith
  have hκ0 : -1 < (b - a) / (2 - a - b) := by
    rw [lt_div_iff₀ ht]; linarith
  have hκ1 : (b - a) / (2 - a - b) < 1 := by
    rw [div_lt_one ht]; linarith
  have k1 := log2_mul_one_sub_H_half hρ0 hρ1
  have k2 := log2_mul_one_sub_H_half hκ0 hκ1
  rw [← k1, ← k2]
  ring

theorem log2_mul_cost_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Real.log 2 * interiorCost a b =
      (b - a) * (atanhR ((b - a) / (a + b)) + atanhR ((b - a) / (2 - a - b))) := by
  have hb0 : 0 < b := ha.trans hab
  have ha1 : a < 1 := hab.trans hb
  rw [CKLaneE.LS.interiorCost_eq_logs ha hb0 ha1 hb]
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have p1 : 1 + (b - a) / (a + b) = 2 * b / (a + b) := by field_simp; ring
  have p2 : 1 - (b - a) / (a + b) = 2 * a / (a + b) := by field_simp; ring
  have p3 : 1 + (b - a) / (2 - a - b) = 2 * (1 - a) / (2 - a - b) := by field_simp; ring
  have p4 : 1 - (b - a) / (2 - a - b) = 2 * (1 - b) / (2 - a - b) := by field_simp; ring
  unfold atanhR
  rw [p1, p2, p3, p4]
  have q1 : (0 : ℝ) < 2 * b := by linarith
  have q2 : (0 : ℝ) < 2 * a := by linarith
  have q3 : (0 : ℝ) < 2 * (1 - a) := by linarith
  have q4 : (0 : ℝ) < 2 * (1 - b) := by linarith
  rw [Real.log_div q1.ne' hs.ne', Real.log_div q2.ne' hs.ne', Real.log_div q3.ne' ht.ne',
    Real.log_div q4.ne' ht.ne', Real.log_mul (by norm_num) hb0.ne',
    Real.log_mul (by norm_num) ha.ne', Real.log_mul (by norm_num) (by linarith : (1 - a) ≠ 0),
    Real.log_mul (by norm_num) (by linarith : (1 - b) ≠ 0), Real.log_div hb0.ne' ha.ne']
  field_simp
  ring

/-- Normalized entropy drop. -/
theorem drop_eq_normalized {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 =
      (b - a) ^ 2 * (Gratio ((b - a) / (a + b)) / (4 * ((a + b) / 2)) +
        Gratio ((b - a) / (2 - a - b)) / (4 * (1 - (a + b) / 2))) / Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := log2_mul_drop_eq ha hab hb
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 < b - a := by linarith
  have hρpos : 0 < (b - a) / (a + b) := div_pos hd hs
  have hκpos : 0 < (b - a) / (2 - a - b) := div_pos hd ht
  have hd1 : b - a = (b - a) / (a + b) * (a + b) := by field_simp
  have hd2 : b - a = (b - a) / (2 - a - b) * (2 - a - b) := by field_simp
  generalize hρ : (b - a) / (a + b) = ρ at h hρpos hd1 ⊢
  generalize hκ : (b - a) / (2 - a - b) = κ at h hκpos hd2 ⊢
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hκne : κ ≠ 0 := hκpos.ne'
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  rw [eq_div_iff hL.ne']
  unfold Gratio
  have hm1 : 1 - (a + b) / 2 = (2 - a - b) / 2 := by ring
  have e1 : (b - a) ^ 2 * (gR ρ / (ρ * ρ) / (4 * ((a + b) / 2))) = (a + b) / 2 * gR ρ := by
    rw [hd1]; field_simp; ring
  have e2 : (b - a) ^ 2 * (gR κ / (κ * κ) / (4 * (1 - (a + b) / 2))) =
      (1 - (a + b) / 2) * gR κ := by
    rw [hm1, hd2]; field_simp; ring
  rw [mul_add, e1, e2, ← h]
  ring

/-- Normalized parent cost. -/
theorem cost_eq_normalized {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    interiorCost a b =
      (b - a) ^ 2 * (Aratio ((b - a) / (a + b)) / (2 * ((a + b) / 2)) +
        Aratio ((b - a) / (2 - a - b)) / (2 * (1 - (a + b) / 2))) / Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := log2_mul_cost_eq ha hab hb
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 < b - a := by linarith
  have hρpos : 0 < (b - a) / (a + b) := div_pos hd hs
  have hκpos : 0 < (b - a) / (2 - a - b) := div_pos hd ht
  have hd1 : b - a = (b - a) / (a + b) * (a + b) := by field_simp
  have hd2 : b - a = (b - a) / (2 - a - b) * (2 - a - b) := by field_simp
  generalize hρ : (b - a) / (a + b) = ρ at h hρpos hd1 ⊢
  generalize hκ : (b - a) / (2 - a - b) = κ at h hκpos hd2 ⊢
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hκne : κ ≠ 0 := hκpos.ne'
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  rw [eq_div_iff hL.ne']
  unfold Aratio
  have hm1 : 1 - (a + b) / 2 = (2 - a - b) / 2 := by ring
  have e1 : (b - a) ^ 2 * (atanhR ρ / ρ / (2 * ((a + b) / 2))) = (b - a) * atanhR ρ := by
    rw [hd1]; field_simp
  have e2 : (b - a) ^ 2 * (atanhR κ / κ / (2 * (1 - (a + b) / 2))) = (b - a) * atanhR κ := by
    rw [hm1, hd2]; field_simp
  rw [mul_add, e1, e2, mul_comm (interiorCost a b), h]
  ring

end CKLaneM08

#check @CKLaneM08.Aratio_mono
#check @CKLaneM08.Gratio_mono
#check @CKLaneM08.drop_eq_normalized
#check @CKLaneM08.cost_eq_normalized
#print axioms CKLaneM08.Aratio_mono
#print axioms CKLaneM08.Gratio_mono
#print axioms CKLaneM08.drop_eq_normalized
#print axioms CKLaneM08.cost_eq_normalized

end


