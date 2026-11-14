-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePrimitives
-- name    : row23_rh_supp_RHLegendrePrimitives
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:01:28.461858+00:00
-- url     : https://prove2.me/theorems/858e73a5-3d94-446a-b21b-a66534b7e115
-- title:
--   Row 23 RH support: RHLegendrePrimitives
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothing
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex Finset
noncomputable def rising (ρ : ℂ) (k : ℕ) : ℂ := ∏ i ∈ range (k+1), (ρ+(i:ℂ))
lemma rising_zero (ρ : ℂ) : rising ρ 0=ρ := by simp [rising]
lemma rising_succ (ρ : ℂ) (k : ℕ) : rising ρ (k+1)=rising ρ k*(ρ+(k:ℂ)+1) := by
  unfold rising
  rw [Finset.prod_range_succ]
  push_cast
  ring
lemma rising_ne_zero (ρ : ℂ) (k : ℕ) (hρ : ρ.im≠0) : rising ρ k≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi he
  apply hρ
  have h := congrArg Complex.im he
  simpa only [Complex.add_im,Complex.natCast_im,add_zero,Complex.zero_im] using h
lemma rising_norm_lower (ρ : ℂ) (k : ℕ) : |ρ.im|^(k+1)≤‖rising ρ k‖ := by
  calc
    _ = ∏ i ∈ range (k+1), |ρ.im| := by simp
    _ ≤ ∏ i ∈ range (k+1), ‖ρ+(i:ℂ)‖ := by
      apply Finset.prod_le_prod
      · intro i hi; exact abs_nonneg _
      · intro i hi
        simpa only [Complex.add_im,Complex.natCast_im,add_zero] using Complex.abs_im_le_norm (ρ+(i:ℂ))
    _ = _ := by simp only [rising,norm_prod]
noncomputable def normalizedPrimitive (k : ℕ) (ρ : ℂ) (δ t : ℝ) : ℂ :=
  (1+(δ:ℂ)*(t:ℂ))^(ρ+(k:ℂ)) / ((δ:ℂ)^k*rising ρ k)
lemma normalizedPrimitive_zero (ρ : ℂ) (δ t : ℝ) :
    normalizedPrimitive 0 ρ δ t=(1+(δ:ℂ)*(t:ℂ))^ρ/ρ := by
  simp [normalizedPrimitive,rising_zero]
 theorem normalizedPrimitive_deriv (k : ℕ) (ρ : ℂ) (δ t : ℝ)
    (hd : 0<δ) (hρ : ρ.im≠0) (ht : 0<1+δ*t) :
    HasDerivAt (normalizedPrimitive (k+1) ρ δ) (normalizedPrimitive k ρ δ t) t := by
  have hs : (1:ℂ)+(δ:ℂ)*(t:ℂ) ∈ Complex.slitPlane := by
    rw [show (1:ℂ)+(δ:ℂ)*(t:ℂ)=((1+δ*t:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ofReal_mem_slitPlane.mpr ht
  have ha := ((hasDerivAt_id (t:ℂ)).const_mul (δ:ℂ)).const_add (1:ℂ)
  have hp := (ha.cpow_const (c:=ρ+((k+1:ℕ):ℂ)) hs).div_const ((δ:ℂ)^(k+1)*rising ρ (k+1))
  have h := hp.comp_ofReal
  simp only [id_eq,mul_one] at h
  have hd' : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hr := rising_ne_zero ρ k hρ
  have hk : ρ+(k:ℂ)+1≠0 := by
    intro he
    apply hρ
    have hh := congrArg Complex.im he
    simpa using hh
  apply h.congr_deriv
  unfold normalizedPrimitive
  rw [show ρ+((k+1:ℕ):ℂ)-1=ρ+(k:ℂ) by push_cast; ring,rising_succ,pow_succ]
  push_cast
  field_simp
  ring
 theorem normalizedPrimitive_norm (k : ℕ) (ρ : ℂ) (δ t : ℝ)
    (hd : 0<δ) (hi : 0 < |ρ.im|) (ht : 0<1+δ*t) :
    ‖normalizedPrimitive k ρ δ t‖ ≤
      (1+δ*t)^(ρ.re+(k:ℝ)) / (δ^k*|ρ.im|^(k+1)) := by
  have hn : ‖((1:ℂ)+(δ:ℂ)*(t:ℂ))^(ρ+(k:ℂ))‖ =
      (1+δ*t)^(ρ.re+(k:ℝ)) := by
    rw [show (1:ℂ)+(δ:ℂ)*(t:ℂ)=((1+δ*t:ℝ):ℂ) by push_cast; rfl]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (ρ+(k:ℂ))
  unfold normalizedPrimitive
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,hn]
  exact div_le_div₀ (Real.rpow_nonneg ht.le _) (le_refl _) (mul_pos (pow_pos hd _) (pow_pos hi _))
    (mul_le_mul_of_nonneg_left (rising_norm_lower ρ k) (pow_nonneg hd.le _))
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.normalizedPrimitive_deriv
#print axioms DusartLegendreSmoothing.normalizedPrimitive_norm


