-- Prove2me | solution 1 for Arxiv2608_05214.flux_normalised_power_flux
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:54:22.647052+00:00
-- url     : https://prove2.me/submissions/a5007da2-9188-4857-a798-c3aaf219b897

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

set_option autoImplicit false

open Arxiv2608_05214 in
theorem solution (omega ρ k : ℝ) (hk : 0 < k / (omega * ρ)) (P V : ℂ) :
    (starRingEnd ℂ P * V).re =
        k / (omega * ρ) * (‖downgoingP omega ρ k P V‖ ^ 2 - ‖upgoingP omega ρ k P V‖ ^ 2) ∧
    ‖fluxNormalised omega ρ k (downgoingP omega ρ k P V)‖ ^ 2
        - ‖fluxNormalised omega ρ k (upgoingP omega ρ k P V)‖ ^ 2 = (starRingEnd ℂ P * V).re := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hw0 : omega * ρ ≠ 0 := by intro h; rw [h, div_zero] at hk; exact lt_irrefl _ hk
  set a : ℝ := omega * ρ / (2 * k) with ha
  have hd : downgoingP omega ρ k P V = P / 2 + (a : ℂ) * V := by
    unfold downgoingP; rw [ha]; push_cast; ring
  have hu : upgoingP omega ρ k P V = P / 2 - (a : ℂ) * V := by
    unfold upgoingP; rw [ha]; push_cast; ring
  have key : ‖downgoingP omega ρ k P V‖ ^ 2 - ‖upgoingP omega ρ k P V‖ ^ 2 =
      2 * a * (starRingEnd ℂ P * V).re := by
    rw [hd, hu, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_sub]
    simp [Complex.mul_re, Complex.div_re, Complex.conj_re, Complex.conj_im]
    ring
  have p1 : (starRingEnd ℂ P * V).re =
      k / (omega * ρ) * (‖downgoingP omega ρ k P V‖ ^ 2 - ‖upgoingP omega ρ k P V‖ ^ 2) := by
    rw [key, ha]; field_simp; rw [mul_assoc, mul_div_assoc, div_self hw0, mul_one]
  refine ⟨p1, ?_⟩
  have hc : (k / (omega * ρ : ℂ)) = ((k / (omega * ρ) : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖(k / (omega * ρ : ℂ)) ^ (1 / 2 : ℂ)‖ ^ 2 = k / (omega * ρ) := by
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos hk]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le]
    norm_num
  unfold fluxNormalised
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hn, ← mul_sub, ← p1]
