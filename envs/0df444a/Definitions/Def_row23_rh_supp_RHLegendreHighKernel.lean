-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreHighKernel
-- name    : row23_rh_supp_RHLegendreHighKernel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:03:43.512717+00:00
-- url     : https://prove2.me/theorems/3890c4e3-1cbb-4070-8b07-0e33619ca5dd
-- title:
--   Row 23 RH support: RHLegendreHighKernel
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreMajorant
import Definitions.Def_row23_rh_supp_RHLegendrePrimitives
import Definitions.Def_row23_rh_supp_RHLegendreLowKernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory intervalIntegral
lemma base_positive (δ t : ℝ) (hd : 0≤δ) (ht : t ∈ Set.uIcc (0:ℝ) 1) : 0<1+δ*t := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
  nlinarith [mul_nonneg hd ht.1]
lemma normalizedPrimitive_continuousOn (k : ℕ) (ρ : ℂ) (δ : ℝ) (hd : 0≤δ) :
    ContinuousOn (normalizedPrimitive k ρ δ) (Set.uIcc (0:ℝ) 1) := by
  have hb : ContinuousOn (fun t : ℝ => (1:ℂ)+(δ:ℂ)*(t:ℂ)) (Set.uIcc (0:ℝ) 1) := by fun_prop
  have hs : ∀ t ∈ Set.uIcc (0:ℝ) 1, (1:ℂ)+(δ:ℂ)*(t:ℂ)∈Complex.slitPlane := by
    intro t ht
    rw [show (1:ℂ)+(δ:ℂ)*(t:ℂ)=((1+δ*t:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ofReal_mem_slitPlane.mpr (base_positive δ t hd ht)
  exact (hb.cpow_const (b:=ρ+(k:ℂ)) hs).div_const _
 theorem zeroKernel_high (m : ℕ) (ρ : ℂ) (δ : ℝ)
    (hd : 0<δ) (hβ : ρ.re≤1) (hi : 0 < |ρ.im|) :
    ‖zeroKernel m ρ δ‖ ≤ derivativeMass m δ/(δ^m*|ρ.im|^(m+1)) := by
  let F : ℕ → ℝ → ℂ := fun n => normalizedPrimitive (m-n) ρ δ
  let D : ℝ := δ^m*|ρ.im|^(m+1)
  have hD : 0<D := mul_pos (pow_pos hd _) (pow_pos hi _)
  have hc : ∀ k ≤ m, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1) := by
    intro k hk
    exact normalizedPrimitive_continuousOn (m-k) ρ δ hd.le
  have hder : ∀ k < m, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t := by
    intro k hk t ht
    dsimp only [F]
    rw [show m-k=m-(k+1)+1 by omega]
    exact normalizedPrimitive_deriv (m-(k+1)) ρ δ t hd (abs_pos.mp hi) (base_positive δ t hd.le ht)
  have hp : ∀ t ∈ Set.uIcc (0:ℝ) 1, ‖F 0 t‖≤(1/D)*(1+δ*t)^(m+1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    have hb : 1≤1+δ*t := by nlinarith [mul_nonneg hd.le ht'.1]
    have hpow : (1+δ*t)^(ρ.re+(m:ℝ))≤(1+δ*t)^(m+1) := by
      have h := Real.rpow_le_rpow_of_exponent_le hb (add_le_add_right hβ (m:ℝ))
      have he : (m:ℝ)+1=((m+1:ℕ):ℝ) := by push_cast; rfl
      rw [he,Real.rpow_natCast] at h
      simpa only [add_comm] using h
    calc
      _ ≤ (1+δ*t)^(ρ.re+(m:ℝ))/D := by
        simpa only [F,Nat.sub_zero,D] using normalizedPrimitive_norm m ρ δ t hd hi (base_positive δ t hd.le ht)
      _ ≤ (1+δ*t)^(m+1)/D := div_le_div_of_nonneg_right hpow hD.le
      _ = _ := by ring
  have hn := weighted_norm_after_ibp m δ (1/D) F hc hder hp
  have he : zeroKernel m ρ δ = ∫ t : ℝ in 0..1, (weight m t:ℂ)*F m t := by
    unfold zeroKernel
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [F,Nat.sub_self]
    rw [normalizedPrimitive_zero]
    push_cast
    ring
  rw [←he] at hn
  exact hn.trans_eq (by dsimp [D]; ring)
 theorem zeroKernel_scaled_high (m : ℕ) (ρ : ℂ) (x δ : ℝ)
    (hx : 0<x) (hd : 0<δ) (hβ : ρ.re≤1) (hi : 0 < |ρ.im|) :
    ‖(x:ℂ)^ρ*zeroKernel m ρ δ‖ ≤ x^ρ.re*derivativeMass m δ/(δ^m*|ρ.im|^(m+1)) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  calc
    _ ≤ x^ρ.re*(derivativeMass m δ/(δ^m*|ρ.im|^(m+1))) :=
      mul_le_mul_of_nonneg_left (zeroKernel_high m ρ δ hd hβ hi) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zeroKernel_high
#print axioms DusartLegendreSmoothing.zeroKernel_scaled_high


