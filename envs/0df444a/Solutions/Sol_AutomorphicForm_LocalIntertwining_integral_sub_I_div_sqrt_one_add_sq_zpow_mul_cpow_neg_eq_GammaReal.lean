-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9fc06073-fd03-5230-8663-a96be79898c0

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal

set_option autoImplicit false

noncomputable section

namespace M4aP2DGK
namespace ArchRealWeight

open MeasureTheory Filter Topology Complex

private def rad (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

private def base (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) : ℂ)

private def phase (x : ℝ) : ℂ := ((x : ℂ) - I) / ((rad x : ℝ) : ℂ)

private def Q (c : ℂ) (x : ℝ) : ℂ := base x ^ (-c)

private def J (k : ℤ) (c : ℂ) : ℂ := ∫ x : ℝ, phase x ^ k * Q c x

private def RHS (k : ℤ) (s : ℂ) : ℂ :=
  (-I) ^ k * (Gammaℝ (2 * s) * Gammaℝ (2 * s + 1)) / (Gammaℝ (2 * s + 1 + k) * Gammaℝ (2 * s + 1 - k))

private theorem one_add_sq_pos (x : ℝ) : (0 : ℝ) < 1 + x ^ 2 := by positivity

private theorem rad_pos (x : ℝ) : 0 < rad x := Real.sqrt_pos.mpr (one_add_sq_pos x)

private theorem rad_sq (x : ℝ) : rad x ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (one_add_sq_pos x).le

private theorem radC_ne_zero (x : ℝ) : ((rad x : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (rad_pos x).ne'

private theorem radC_sq (x : ℝ) : ((rad x : ℝ) : ℂ) ^ 2 = base x := by
  unfold base
  exact_mod_cast rad_sq x

private theorem radC_sq' (x : ℝ) : ((rad x : ℝ) : ℂ) ^ 2 = 1 + (x : ℂ) ^ 2 := by
  rw [radC_sq]
  unfold base
  push_cast
  ring

private theorem base_ne_zero (x : ℝ) : base x ≠ 0 := by
  unfold base
  exact_mod_cast (one_add_sq_pos x).ne'

private theorem base_mem_slitPlane (x : ℝ) : base x ∈ slitPlane := by
  unfold base
  exact Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

private theorem sub_I_ne_zero (x : ℝ) : (x : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem phase_ne_zero (x : ℝ) : phase x ≠ 0 :=
  div_ne_zero (sub_I_ne_zero x) (radC_ne_zero x)

private theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - I‖ = rad x := by
  have h : ‖(x : ℂ) - I‖ ^ 2 = 1 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
      Complex.ofReal_im, Complex.I_im, zero_sub]
    ring
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - I)), h]
  rfl

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rad_pos x)]
  exact div_self (rad_pos x).ne'

private theorem norm_Q (c : ℂ) (x : ℝ) : ‖Q c x‖ = (1 + x ^ 2) ^ (-c.re) := by
  unfold Q base
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  simp

private theorem norm_phase_zpow_mul_Q (k : ℤ) (c : ℂ) (x : ℝ) :
    ‖phase x ^ k * Q c x‖ = (1 + x ^ 2) ^ (-c.re) := by
  rw [norm_mul, norm_zpow, norm_phase, one_zpow, one_mul, norm_Q]

private theorem Q_div_base (c : ℂ) (x : ℝ) : Q c x / base x = Q (c + 1) x := by
  unfold Q
  rw [div_eq_mul_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (base_ne_zero x)]
  congr 1
  ring

private theorem base_cpow_neg_sub_one (c : ℂ) (x : ℝ) : base x ^ (-c - 1) = Q (c + 1) x := by
  unfold Q
  congr 1
  ring

private theorem radC_eq_base_cpow_half (x : ℝ) : ((rad x : ℝ) : ℂ) = base x ^ ((1 / 2 : ℂ)) := by
  unfold rad base
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (one_add_sq_pos x).le]
  congr 1
  push_cast
  ring

private theorem rad_mul_Q (c : ℂ) (x : ℝ) : ((rad x : ℝ) : ℂ) * Q (c + 1) x = Q (c + 1 / 2) x := by
  unfold Q
  rw [radC_eq_base_cpow_half, ← Complex.cpow_add _ _ (base_ne_zero x)]
  congr 1
  ring

private theorem ofReal_eq_rad_mul_phase_add_I (x : ℝ) : (x : ℂ) = ((rad x : ℝ) : ℂ) * phase x + I := by
  unfold phase
  rw [mul_comm ((rad x : ℝ) : ℂ) _, div_mul_cancel₀ _ (radC_ne_zero x)]
  ring

private theorem phase_mul_phase_neg (x : ℝ) : phase x * phase (-x) = -1 := by
  have hr : rad (-x) = rad x := by
    unfold rad
    rw [neg_sq]
  have hR := radC_ne_zero x
  unfold phase
  rw [hr, div_mul_div_comm, div_eq_iff (mul_ne_zero hR hR), ← pow_two, radC_sq']
  push_cast
  linear_combination Complex.I_sq

private theorem phase_neg (x : ℝ) : phase (-x) = -(phase x)⁻¹ := by
  have h0 := phase_ne_zero x
  have h1 : phase (-x) = -1 / phase x := by
    rw [eq_div_iff h0, mul_comm]
    exact phase_mul_phase_neg x
  rw [h1, neg_div, one_div]

private theorem Q_neg (c : ℂ) (x : ℝ) : Q c (-x) = Q c x := by
  unfold Q base
  rw [neg_sq]

private theorem continuous_phase : Continuous phase := by
  unfold phase rad
  refine Continuous.div (Complex.continuous_ofReal.sub continuous_const)
    (Complex.continuous_ofReal.comp ((continuous_const.add (continuous_pow 2)).sqrt)) ?_
  intro x
  exact radC_ne_zero x

private theorem continuous_Q (c : ℂ) : Continuous (Q c) := by
  unfold Q base
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2)))
    continuous_const ?_
  intro x
  left
  rw [Complex.ofReal_re]
  exact one_add_sq_pos x

private theorem continuous_phase_zpow_mul_Q (k : ℤ) (c : ℂ) :
    Continuous (fun x : ℝ => phase x ^ k * Q c x) :=
  (continuous_phase.zpow₀ k fun x => Or.inl (phase_ne_zero x)).mul (continuous_Q c)

private theorem integrable_phase_zpow_mul_Q (k : ℤ) {c : ℂ} (hc : 1 / 2 < c.re) :
    Integrable (fun x : ℝ => phase x ^ k * Q c x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * c.re := by
    simp
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono'
    (continuous_phase_zpow_mul_Q k c).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_phase_zpow_mul_Q, Real.norm_eq_abs, sq_abs]
  apply le_of_eq
  congr 1
  ring

private theorem tendsto_phase_zpow_mul_Q_atTop (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun x : ℝ => phase x ^ k * Q c x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun t : ℝ => t ^ (-c.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  have h3 := h2.comp h1
  refine h3.congr fun x => ?_
  show (1 + x ^ 2) ^ (-c.re) = ‖phase x ^ k * Q c x‖
  rw [norm_phase_zpow_mul_Q]

private theorem tendsto_phase_zpow_mul_Q_atBot (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun x : ℝ => phase x ^ k * Q c x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun x : ℝ => 1 + x ^ 2) atBot atTop := by
    have : Tendsto (fun x : ℝ => 1 + (-x) ^ 2) atBot atTop :=
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)).comp tendsto_neg_atBot_atTop
    simpa [neg_sq] using this
  have h2 : Tendsto (fun t : ℝ => t ^ (-c.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  have h3 := h2.comp h1
  refine h3.congr fun x => ?_
  show (1 + x ^ 2) ^ (-c.re) = ‖phase x ^ k * Q c x‖
  rw [norm_phase_zpow_mul_Q]

private theorem hasDerivAt_phase (x : ℝ) : HasDerivAt phase (I * phase x / base x) x := by
  have hN : HasDerivAt (fun y : ℝ => (y : ℂ) - I) 1 x := by
    have h := (hasDerivAt_id x).ofReal_comp
    simpa using h.sub_const I
  have hsq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_add 1
    simpa using h
  have hne : 1 + x ^ 2 ≠ 0 := (one_add_sq_pos x).ne'
  have hs0 : Real.sqrt (1 + x ^ 2) ≠ 0 := (rad_pos x).ne'
  have hR : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2)) (2 * x / (2 * Real.sqrt (1 + x ^ 2))) x :=
    hsq.sqrt hne
  have hRC : HasDerivAt (fun y : ℝ => ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ))
      (((2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ)) x := hR.ofReal_comp
  have hdiv := hN.div hRC (radC_ne_zero x)
  refine hdiv.congr_deriv ?_
  have hrC := radC_ne_zero x
  have hd : ((2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ) = (x : ℂ) / ((rad x : ℝ) : ℂ) := by
    have e : (2 * x / (2 * Real.sqrt (1 + x ^ 2)) : ℝ) = x / rad x := by
      unfold rad
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero hs0) hs0]
      ring
    rw [e, Complex.ofReal_div]
  rw [hd]
  unfold phase
  change (1 * ((rad x : ℝ) : ℂ) - ((x : ℂ) - I) * ((x : ℂ) / ((rad x : ℝ) : ℂ))) / ((rad x : ℝ) : ℂ) ^ 2
      = I * (((x : ℂ) - I) / ((rad x : ℝ) : ℂ)) / base x
  rw [← radC_sq x, div_left_inj' (pow_ne_zero 2 hrC), ← mul_left_inj' hrC, sub_mul, one_mul]
  rw [show ((x : ℂ) - I) * ((x : ℂ) / ((rad x : ℝ) : ℂ)) * ((rad x : ℝ) : ℂ) = ((x : ℂ) - I) * x by
        rw [mul_assoc, div_mul_cancel₀ _ hrC]]
  rw [show I * (((x : ℂ) - I) / ((rad x : ℝ) : ℂ)) * ((rad x : ℝ) : ℂ) = I * ((x : ℂ) - I) by
        rw [mul_assoc, div_mul_cancel₀ _ hrC]]
  linear_combination radC_sq' x + Complex.I_sq

private theorem hasDerivAt_phase_zpow (k : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => phase y ^ k) ((k : ℂ) * I * (phase x ^ k / base x)) x := by
  have h := (hasDerivAt_zpow k (phase x) (Or.inl (phase_ne_zero x))).comp x (hasDerivAt_phase x)
  refine h.congr_deriv ?_
  have h0 := phase_ne_zero x
  rw [zpow_sub_one₀ h0 k]
  calc (k : ℂ) * (phase x ^ k * (phase x)⁻¹) * (I * phase x / base x)
      = (k : ℂ) * I * (phase x ^ k / base x) * ((phase x)⁻¹ * phase x) := by ring
    _ = (k : ℂ) * I * (phase x ^ k / base x) := by rw [inv_mul_cancel₀ h0, mul_one]

private theorem hasDerivAt_Q (c : ℂ) (x : ℝ) :
    HasDerivAt (Q c) (-(2 * c) * (x : ℂ) * Q (c + 1) x) x := by
  have hu : HasDerivAt (fun y : ℝ => ((1 + y ^ 2 : ℝ) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have h := ((hasDerivAt_pow 2 x).const_add 1).ofReal_comp
    refine h.congr_deriv ?_
    push_cast
    ring
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := -c) (base_mem_slitPlane x)).hasDerivAt.comp x hu
  have hc' : HasDerivAt (Q c) (-c * base x ^ (-c - 1) * (((2 * x : ℝ)) : ℂ)) x := hc
  refine hc'.congr_deriv ?_
  rw [base_cpow_neg_sub_one]
  push_cast
  ring

private theorem hasDerivAt_G (k : ℤ) (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => phase y ^ k * Q c y)
      (I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
        - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x)) x := by
  have h := (hasDerivAt_phase_zpow k x).mul (hasDerivAt_Q c x)
  refine h.congr_deriv ?_
  have hQ : phase x ^ k / base x * Q c x = phase x ^ k * Q (c + 1) x := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Q_div_base]
  have hx : (x : ℂ) * (phase x ^ k * Q (c + 1) x)
      = phase x ^ (k + 1) * Q (c + 1 / 2) x + I * (phase x ^ k * Q (c + 1) x) := by
    conv_lhs => rw [ofReal_eq_rad_mul_phase_add_I x]
    rw [zpow_add_one₀ (phase_ne_zero x), ← rad_mul_Q c x]
    ring
  calc (k : ℂ) * I * (phase x ^ k / base x) * Q c x + phase x ^ k * (-(2 * c) * (x : ℂ) * Q (c + 1) x)
      = (k : ℂ) * I * (phase x ^ k / base x * Q c x)
          - 2 * c * ((x : ℂ) * (phase x ^ k * Q (c + 1) x)) := by ring
    _ = (k : ℂ) * I * (phase x ^ k * Q (c + 1) x)
          - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x + I * (phase x ^ k * Q (c + 1) x)) := by
        rw [hQ, hx]
    _ = I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
          - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x) := by ring

private theorem recursion_raw (k : ℤ) {c : ℂ} (hc : 0 < c.re) :
    2 * c * J (k + 1) (c + 1 / 2) = I * ((k : ℂ) - 2 * c) * J k (c + 1) := by
  have hc1 : 1 / 2 < (c + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hc2 : 1 / 2 < (c + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hI1 : Integrable (fun x : ℝ => phase x ^ k * Q (c + 1) x) :=
    integrable_phase_zpow_mul_Q k hc1
  have hI2 : Integrable (fun x : ℝ => phase x ^ (k + 1) * Q (c + 1 / 2) x) :=
    integrable_phase_zpow_mul_Q (k + 1) hc2
  have hderiv := fun x => hasDerivAt_G k c x
  have hint : Integrable (fun x : ℝ => I * ((k : ℂ) - 2 * c) * (phase x ^ k * Q (c + 1) x)
      - 2 * c * (phase x ^ (k + 1) * Q (c + 1 / 2) x)) :=
    (hI1.const_mul _).sub (hI2.const_mul _)
  have hzero := integral_of_hasDerivAt_of_tendsto hderiv hint
    (tendsto_phase_zpow_mul_Q_atBot k hc) (tendsto_phase_zpow_mul_Q_atTop k hc)
  rw [sub_zero, integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
    integral_const_mul] at hzero
  unfold J
  linear_combination (-1 : ℂ) * hzero

private theorem recursion (k : ℤ) {s : ℂ} (hs : 0 < s.re) :
    J (k + 1) (s + 1 / 2) = -I * ((s - (k : ℂ) / 2) / s) * J k (s + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h := recursion_raw k hs
  have h2 : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have h3 : J (k + 1) (s + 1 / 2) = (2 * s)⁻¹ * (I * ((k : ℂ) - 2 * s) * J k (s + 1)) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  rw [h3]
  field_simp
  ring

private theorem closed_form_zero {s : ℂ} (hs : 0 < s.re) : J 0 (s + 1 / 2) = RHS 0 s := by
  have hB : Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  have hbase := AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs
  unfold J RHS
  simp only [zpow_zero, one_mul, Int.cast_zero, add_zero, sub_zero]
  unfold Q base
  rw [hbase, mul_div_mul_right _ _ hB]

private theorem RHS_step (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    RHS ((k : ℤ) + 1) s = -I * ((s - (k : ℂ) / 2) / s) * RHS k (s + 1 / 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hA : Gammaℝ (2 * s) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.mul_re]
    norm_num
    linarith
  have hB : Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  have hD : Gammaℝ (2 * s + 2 + k) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.add_re, Complex.mul_re, Complex.natCast_re]
    norm_num
    linarith
  have hC : Gammaℝ (2 * s + 2) = Gammaℝ (2 * s) * (2 * s) / 2 / Real.pi :=
    Complex.Gammaℝ_add_two (mul_ne_zero two_ne_zero hs0)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero

  have g1 : Gammaℝ (2 * s + 1 + (((k : ℤ) + 1 : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 + k) := by
    congr 1; push_cast; ring
  have g2 : Gammaℝ (2 * s + 1 - (((k : ℤ) + 1 : ℤ) : ℂ)) = Gammaℝ (2 * s - k) := by
    congr 1; push_cast; ring
  have g3 : Gammaℝ (2 * (s + 1 / 2)) = Gammaℝ (2 * s + 1) := by
    congr 1; ring
  have g4 : Gammaℝ (2 * (s + 1 / 2) + 1) = Gammaℝ (2 * s + 2) := by
    congr 1; ring
  have g5 : Gammaℝ (2 * (s + 1 / 2) + 1 + ((k : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 + k) := by
    congr 1; push_cast; ring
  have g6 : Gammaℝ (2 * (s + 1 / 2) + 1 - ((k : ℤ) : ℂ)) = Gammaℝ (2 * s + 2 - k) := by
    congr 1; push_cast; ring
  unfold RHS
  rw [g1, g2, g3, g4, g5, g6]
  by_cases hE : Gammaℝ (2 * s - k) = 0
  ·
    rw [hE, mul_zero, div_zero]
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hE
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    ·
      subst hn0
      have hsk : s - (k : ℂ) / 2 = 0 := by
        simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
        linear_combination hn / 2
      rw [hsk]
      simp
    ·
      have hF : Gammaℝ (2 * s + 2 - k) = 0 := by
        refine Complex.Gammaℝ_eq_zero_iff.mpr ⟨n - 1, ?_⟩
        have e : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub hnpos]
          simp
        rw [e]
        linear_combination hn
      rw [hF, mul_zero, div_zero, mul_zero]
  ·
    have hk0 : (2 * s - k : ℂ) ≠ 0 := by
      intro h0
      apply hE
      rw [h0]
      exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
    have hF : Gammaℝ (2 * s + 2 - k) = Gammaℝ (2 * s - k) * (2 * s - k) / 2 / Real.pi := by
      rw [show (2 * s + 2 - k : ℂ) = (2 * s - k) + 2 by ring]
      exact Complex.Gammaℝ_add_two hk0
    rw [hF, hC, zpow_add_one₀ hI0]
    field_simp

private theorem closed_form_nat (k : ℕ) : ∀ {s : ℂ}, 0 < s.re → J k (s + 1 / 2) = RHS k s := by
  induction k with
  | zero =>
      intro s hs
      exact_mod_cast closed_form_zero hs
  | succ k ih =>
      intro s hs
      have hs' : 0 < (s + 1 / 2).re := by
        rw [Complex.add_re]
        norm_num
        linarith
      have hrec := recursion (k : ℤ) hs
      push_cast at hrec
      have hih := ih hs'
      have e1 : J (k : ℤ) (s + 1) = RHS k (s + 1 / 2) := by
        rw [← hih]
        congr 1
        ring
      push_cast
      rw [hrec, e1, RHS_step k hs]

private theorem J_neg (k : ℤ) (c : ℂ) : J (-k) c = (-1) ^ k * J k c := by
  unfold J
  have h := integral_neg_eq_self (fun x : ℝ => phase x ^ (-k) * Q c x) volume
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [phase_neg, Q_neg]
  have e : -(phase x)⁻¹ = (-1) * (phase x)⁻¹ := by ring
  rw [e, mul_zpow, inv_zpow', neg_neg, zpow_neg, ← inv_zpow, inv_neg_one]
  ring

private theorem RHS_neg (k : ℤ) (s : ℂ) : RHS (-k) s = (-1) ^ k * RHS k s := by
  have hI : (-I : ℂ) ^ (-k) = (-1) ^ k * (-I) ^ k := by
    rw [zpow_neg, ← inv_zpow, ← mul_zpow]
    congr 1
    rw [inv_neg, Complex.inv_I]
    ring
  have e1 : Gammaℝ (2 * s + 1 + ((-k : ℤ) : ℂ)) = Gammaℝ (2 * s + 1 - k) := by
    congr 1; push_cast; ring
  have e2 : Gammaℝ (2 * s + 1 - ((-k : ℤ) : ℂ)) = Gammaℝ (2 * s + 1 + k) := by
    congr 1; push_cast; ring
  unfold RHS
  rw [hI, e1, e2]
  ring

private theorem closed_form (k : ℤ) {s : ℂ} (hs : 0 < s.re) : J k (s + 1 / 2) = RHS k s := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact closed_form_nat n hs
  · rw [J_neg, RHS_neg, closed_form_nat n hs]

private theorem main (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (-Complex.I) ^ k * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
          / (Complex.Gammaℝ (2 * s + 1 + k) * Complex.Gammaℝ (2 * s + 1 - k)) :=
  closed_form k hs

end M4aP2DGK.ArchRealWeight

end

theorem solution
    (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (-Complex.I) ^ k * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
          / (Complex.Gammaℝ (2 * s + 1 + k) * Complex.Gammaℝ (2 * s + 1 - k)) :=
  M4aP2DGK.ArchRealWeight.main k s hs

end S_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal (solution)
