-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePerronProduct
-- name    : row23_rh_supp_RHLegendrePerronProduct
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:09.214769+00:00
-- url     : https://prove2.me/theorems/9a4af188-e9a7-4b3b-9212-c393f76225fa
-- title:
--   Row 23 RH support: RHLegendrePerronProduct
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePerronRemainder
import Definitions.Def_row23_rh_supp_RHLegendreMajorant
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory DusartSmoothing
lemma left_denominator_ne_zero (v : ℝ) :
    (-(1/2:ℂ)+v*I)*(-(1/2:ℂ)+v*I+1)*(-(1/2:ℂ)+v*I+2) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  all_goals intro h; have hh := congrArg Complex.re h; norm_num at hh
lemma continuous_logDeriv_zeta_left :
    Continuous (fun v : ℝ => logDeriv riemannZeta (-(1/2:ℂ)+v*I)) := by
  have h := (continuous_perron_left 1 (by norm_num)).neg.mul
    (show Continuous (fun v : ℝ =>
      (-(1/2:ℂ)+v*I)*(-(1/2:ℂ)+v*I+1)*(-(1/2:ℂ)+v*I+2)) by fun_prop)
  apply h.congr
  intro v
  dsimp only [Pi.mul_apply,Pi.neg_apply]
  simp only [perronIntegrand,quadraticKernel,Complex.ofReal_one,Complex.one_cpow,neg_mul,neg_neg]
  calc
    _ = (logDeriv riemannZeta (-(1/2:ℂ)+v*I) /
      ((-(1/2:ℂ)+v*I)*(-(1/2:ℂ)+v*I+1)*(-(1/2:ℂ)+v*I+2))) *
      ((-(1/2:ℂ)+v*I)*(-(1/2:ℂ)+v*I+1)*(-(1/2:ℂ)+v*I+2)) := by ring
    _ = _ := div_mul_cancel₀ _ (left_denominator_ne_zero v)
lemma weighted_perron_product_continuousOn (m : ℕ) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 ≤ δ) :
    ContinuousOn (fun p : ℝ × ℝ => ((iteratedDeriv 2 (weight m) p.1:ℝ):ℂ)*
      perronIntegrand (x*(1+δ*p.1)) (-(1/2:ℂ)+p.2*I))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  have hb : ContinuousOn (fun p : ℝ × ℝ => ((x*(1+δ*p.1):ℝ):ℂ))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) := by fun_prop
  have hp := hb.cpow
    (show ContinuousOn (fun p : ℝ × ℝ => -(1/2:ℂ)+p.2*I+2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) by fun_prop) (by
        intro p hp
        exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hx (by
          nlinarith [mul_nonneg hd hp.1.1])))
  have hD : ContinuousOn (fun p : ℝ × ℝ =>
      (-(1/2:ℂ)+p.2*I)*(-(1/2:ℂ)+p.2*I+1)*(-(1/2:ℂ)+p.2*I+2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) := by fun_prop
  have hQ := hp.div hD (fun p _ => left_denominator_ne_zero p.2)
  have hZ : ContinuousOn (fun p : ℝ × ℝ => logDeriv riemannZeta (-(1/2:ℂ)+p.2*I))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) :=
    (continuous_logDeriv_zeta_left.comp continuous_snd).continuousOn
  have hW : ContinuousOn (fun p : ℝ × ℝ => ((iteratedDeriv 2 (weight m) p.1:ℝ):ℂ))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ) := (Complex.continuous_ofReal.comp
    ((iterated_weight_continuous m 2).comp continuous_fst)).continuousOn
  exact hW.mul (hQ.neg.mul hZ)
 theorem weighted_perron_product_integrable (m : ℕ) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 ≤ δ) :
    Integrable (fun p : ℝ × ℝ => ((iteratedDeriv 2 (weight m) p.1:ℝ):ℂ)*
      perronIntegrand (x*(1+δ*p.1)) (-(1/2:ℂ)+p.2*I))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod volume) := by
  have hW : IntegrableOn (fun u : ℝ => |iteratedDeriv 2 (weight m) u|) (Set.Ioc (0:ℝ) 1) :=
    ((iterated_weight_continuous m 2).abs.intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)).1
  have hV : Integrable (fun v : ℝ => 256*(x*(1+δ))^(3/2:ℝ)*(1+v^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hG := hW.mul_prod hV
  have hfm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((iteratedDeriv 2 (weight m) p.1:ℝ):ℂ)*
      perronIntegrand (x*(1+δ*p.1)) (-(1/2:ℂ)+p.2*I))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioc.prod MeasurableSet.univ)
    exact (weighted_perron_product_continuousOn m x δ hx hd).mono
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Subset.rfl)
  apply hG.mono' hfm
  rw [Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp
  have hy : 0 < x*(1+δ*p.1) := mul_pos hx (by nlinarith [mul_nonneg hd hp.1.1.le])
  have hxy : x*(1+δ*p.1) ≤ x*(1+δ) := by
    apply mul_le_mul_of_nonneg_left _ hx.le
    nlinarith [mul_le_mul_of_nonneg_left hp.1.2 hd]
  have hpow := Real.rpow_le_rpow hy.le hxy (by norm_num : (0:ℝ) ≤ 3/2)
  have hP := (norm_perron_left_majorant _ hy p.2).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 256)) (by positivity))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simpa only [div_eq_mul_inv,mul_assoc] using
    mul_le_mul_of_nonneg_left hP (abs_nonneg (iteratedDeriv 2 (weight m) p.1))
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.weighted_perron_product_integrable


