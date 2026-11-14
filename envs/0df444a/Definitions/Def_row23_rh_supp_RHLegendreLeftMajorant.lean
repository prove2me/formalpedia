-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLeftMajorant
-- name    : row23_rh_supp_RHLegendreLeftMajorant
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:43.443252+00:00
-- url     : https://prove2.me/theorems/8065bd0e-2de4-4efc-8d80-a6db2c7d686d
-- title:
--   Row 23 RH support: RHLegendreLeftMajorant
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreLeftKernel
import Definitions.Def_dusart_psi_433_20261014_ZetaLeftBound
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory
 theorem zeroKernel_left_cubic (m : ℕ) (hm : 2 ≤ m) (δ v : ℝ)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    δ^2*(‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖*|v|^3) ≤ (16*(m:ℝ))^2 := by
  by_cases hv : v=0
  · simp [hv]
  have hp : (1+δ)^(3/2:ℝ) ≤ 4 := by
    calc
      _ ≤ (1+δ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (1+δ)^2 := Real.rpow_natCast _ 2
      _ ≤ 4 := by nlinarith
  have hi : 0 < |(-(1/2:ℂ)+v*I).im| := by simpa using abs_pos.mpr hv
  have hn := zeroKernel_second_high m hm (-(1/2:ℂ)+v*I) δ hd (by norm_num) hi
  have him : (-(1/2:ℂ)+v*I).im=v := by simp
  rw [him] at hn
  have hden : 0 < δ^2*|v|^3 := by positivity
  have hh := (le_div_iff₀ hden).mp hn
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hK : 0 ≤ 8*(m:ℝ)*(2*m+1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hp hK
  nlinarith
 theorem zeroKernel_left_rational (m : ℕ) (hm : 2 ≤ m) (δ v : ℝ)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    ‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖*|v| ≤
      2*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2) := by
  let n := ‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hden : 0 < (16*(m:ℝ))^2+δ^2*v^2 := by positivity
  have hlo : n*|v| ≤ 1 := by
    by_cases hv : v=0
    · simp [hv]
    have hn := zeroKernel_left_inverse m δ v hd.le hv
    exact (le_div_iff₀ (abs_pos.mpr hv)).mp hn
  have hhi := zeroKernel_left_cubic m hm δ v hd hd1
  change δ^2*(n*|v|^3) ≤ (16*(m:ℝ))^2 at hhi
  apply (le_div_iff₀ hden).2
  have hh := mul_le_mul_of_nonneg_right hlo (sq_nonneg (16*(m:ℝ)))
  have hv2 : |v|^2=v^2 := sq_abs v
  change n*|v| *((16*(m:ℝ))^2+δ^2*v^2) ≤ _
  have he : δ^2*(n*|v|^3)=n*|v| *(δ^2*v^2) := by rw [←sq_abs v]; ring
  rw [he] at hhi
  nlinarith only [hh,hhi]
noncomputable def leftKernelMajorant (m : ℕ) (δ v : ℝ) : ℝ :=
  (Set.Icc (-32:ℝ) 32).indicator (fun _ => (128:ℝ)) v +
    4*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2)
 theorem norm_left_kernel_logDeriv (m : ℕ) (hm : 2 ≤ m) (δ v : ℝ)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    ‖zeroKernel m (-(1/2:ℂ)+v*I) δ *
      logDeriv riemannZeta (-(1/2:ℂ)+v*I)‖ ≤ leftKernelMajorant m δ v := by
  let n := ‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖
  have hn0 : 0 ≤ n := norm_nonneg _
  have hn2 : n ≤ 2 := zeroKernel_left_uniform m δ v hd.le
  have hZ := DusartSmoothing.RvM.norm_logDeriv_zeta_left v
  have hr := zeroKernel_left_rational m hm δ v hd hd1
  have hR : 0 ≤ 4*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2) := by positivity
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hZ hn0).trans
  change n*(|v|+32) ≤ _
  by_cases hv : |v| ≤ 32
  · have hv' : v ∈ Set.Icc (-32:ℝ) 32 := abs_le.mp hv
    simp only [leftKernelMajorant,Set.indicator_of_mem hv']
    have hh := mul_le_mul hn2 (by linarith : |v|+32 ≤ 64) (by positivity : 0 ≤ |v|+32) (by norm_num : (0:ℝ) ≤ 2)
    linarith
  · have hv' : v ∉ Set.Icc (-32:ℝ) 32 := fun h => hv (abs_le.mpr h)
    simp only [leftKernelMajorant,Set.indicator_of_notMem hv',zero_add]
    change n*|v| ≤ _ at hr
    have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hv) hn0
    calc
      n*(|v|+32) ≤ n*|v|+n*|v| := by nlinarith only [hh]
      _ ≤ 2*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2)+
          2*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2) := add_le_add hr hr
      _ = _ := by ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.norm_left_kernel_logDeriv


