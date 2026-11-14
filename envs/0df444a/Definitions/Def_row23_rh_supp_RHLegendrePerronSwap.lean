-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePerronSwap
-- name    : row23_rh_supp_RHLegendrePerronSwap
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:14.014892+00:00
-- url     : https://prove2.me/theorems/6f60fbfd-b047-4a28-9c2c-9295406cb806
-- title:
--   Row 23 RH support: RHLegendrePerronSwap
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePerronProduct
import Definitions.Def_row23_rh_supp_RHLegendreSecondKernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory DusartSmoothing
 theorem legendrePerronRemainder_vertical (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) :
    legendrePerronRemainder m x δ = (1/(2*Real.pi):ℂ)*∫ v : ℝ,
      -((x:ℂ)^(-(1/2:ℂ)+v*I))*zeroKernel m (-(1/2:ℂ)+v*I) δ *
        logDeriv riemannZeta (-(1/2:ℂ)+v*I) := by
  let W : ℝ → ℂ := fun u => ((iteratedDeriv 2 (weight m) u:ℝ):ℂ)
  let P : ℝ → ℝ → ℂ := fun u v => perronIntegrand (x*(1+δ*u)) (-(1/2:ℂ)+v*I)
  let c : ℂ := 1/(2*Real.pi)
  let d : ℂ := ((δ*x:ℝ):ℂ)^2
  have hs : (∫ u : ℝ in 0..1, ∫ v : ℝ, W u*P u v) =
      ∫ v : ℝ, ∫ u : ℝ in 0..1, W u*P u v := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (integral_integral_swap (weighted_perron_product_integrable m x δ hx hd.le))
  have he (u : ℝ) : W u*(c*∫ v : ℝ, P u v)=c*∫ v : ℝ, W u*P u v := by
    rw [integral_const_mul]
    ring
  change (∫ u : ℝ in 0..1, W u*(c*∫ v : ℝ, P u v))/d = _
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,hs,mul_div_assoc,←integral_div]
  congr 1
  apply integral_congr_ae
  have hzero : ∀ᵐ v : ℝ, v ≠ 0 := Measure.ae_ne volume 0
  filter_upwards [hzero] with v hv
  let s : ℂ := -(1/2:ℂ)+v*I
  have hsi : s.im ≠ 0 := by simpa [s] using hv
  have hp : (fun u : ℝ => W u*P u v) = fun u : ℝ =>
      (-logDeriv riemannZeta s)*(W u*quadraticKernel (x*(1+δ*u)) s) := by
    funext u
    dsimp only [P,perronIntegrand,s]
    ring
  rw [hp,intervalIntegral.integral_const_mul,mul_div_assoc]
  have hk := integral_affine_quadratic_kernel m hm s x δ hx hd hsi
  change (∫ u : ℝ in 0..1, W u*quadraticKernel (x*(1+δ*u)) s)/d = _ at hk
  rw [hk]
  dsimp only [s]
  ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.legendrePerronRemainder_vertical


