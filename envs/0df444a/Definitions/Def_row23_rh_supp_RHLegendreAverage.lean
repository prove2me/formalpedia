-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreAverage
-- name    : row23_rh_supp_RHLegendreAverage
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:01:59.993276+00:00
-- url     : https://prove2.me/theorems/13a7b104-7cee-4351-84ee-6f8b18697813
-- title:
--   Row 23 RH support: RHLegendreAverage
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothing
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
noncomputable def average (m : ℕ) (f : ℝ → ℝ) (x δ : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, weight m t*f (x*(1+δ*t))
lemma affine_monotone (x δ : ℝ) (hx : 0≤x) (hd : 0≤δ) :
    Monotone (fun t : ℝ => x*(1+δ*t)) := by
  intro a b hab
  have h := mul_le_mul_of_nonneg_left hab (mul_nonneg hx hd)
  nlinarith
lemma average_integrable (m : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (x δ : ℝ) (hx : 0≤x) (hd : 0≤δ) :
    IntervalIntegrable (fun t : ℝ => weight m t*f (x*(1+δ*t))) volume 0 1 := by
  have hc := (hf.comp (affine_monotone x δ hx hd)).intervalIntegrable (μ:=volume) (a:=0) (b:=1)
  simpa only [mul_comm,Function.comp_apply] using hc.mul_continuousOn (weight_continuous m).continuousOn
lemma average_id (m : ℕ) (x δ : ℝ) : average m id x δ=x*(1+δ/2) := by
  have hw := (weight_continuous m).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have ht : IntervalIntegrable (fun t : ℝ => weight m t*t) volume 0 1 := by
    change IntervalIntegrable (weight m * id) volume 0 1
    exact ((weight_continuous m).mul continuous_id).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have he : (fun t : ℝ => weight m t*id (x*(1+δ*t)))=
      (fun t : ℝ => x*weight m t+(x*δ)*(weight m t*t)) := by funext t; simp only [id_eq]; ring
  rw [average,he,intervalIntegral.integral_add (hw.const_mul x) (ht.const_mul (x*δ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_weight,first_moment]
  ring
lemma average_monotone_bounds (m : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (x δ : ℝ) (hx : 0≤x) (hd : 0≤δ) :
    f x ≤ average m f x δ ∧ average m f x δ ≤ f (x*(1+δ)) := by
  have hav := average_integrable m f hf x δ hx hd
  have hw := (weight_continuous m).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hlo := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) (hw.mul_const (f x)) hav
    (show ∀ t ∈ Set.Icc (0:ℝ) 1, weight m t*f x ≤ weight m t*f (x*(1+δ*t)) from by
      intro t ht
      apply mul_le_mul_of_nonneg_left (hf ?_) (weight_nonneg m t ht)
      calc x=x*1 := by ring
           _≤x*(1+δ*t) := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hd ht.1]) hx)
  have hhi := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) hav (hw.mul_const (f (x*(1+δ))))
    (show ∀ t ∈ Set.Icc (0:ℝ) 1, weight m t*f (x*(1+δ*t)) ≤ weight m t*f (x*(1+δ)) from by
      intro t ht
      apply mul_le_mul_of_nonneg_left (hf ?_) (weight_nonneg m t ht)
      apply mul_le_mul_of_nonneg_left ?_ hx
      have hd' := mul_le_mul_of_nonneg_left ht.2 hd
      nlinarith)
  simpa only [intervalIntegral.integral_mul_const,integral_weight,one_mul,average] using And.intro hlo hhi
 theorem desmoothing (m : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (x δ E : ℝ) (hx : 0≤x) (hd : 0≤δ) (hE : 0≤E)
    (hupper : |average m f x δ-x*(1+δ/2)|≤E*x)
    (hlower : |average m f (x/(1+δ)) δ-(x/(1+δ))*(1+δ/2)|≤E*(x/(1+δ))) :
    |f x-x|≤(δ/2+E)*x := by
  have hd1 : 0<1+δ := by linarith
  let a := x/(1+δ)
  have ha : 0≤a := div_nonneg hx hd1.le
  have hax : a≤x := (div_le_iff₀ hd1).mpr (by nlinarith [mul_nonneg hx hd])
  have heq : a*(1+δ)=x := div_mul_cancel₀ x hd1.ne'
  have hup := (average_monotone_bounds m f hf x δ hx hd).1
  have hlo := (average_monotone_bounds m f hf a δ ha hd).2
  rw [heq] at hlo
  have hu := (abs_le.mp hupper).2
  have hl := (abs_le.mp hlower).1
  change -(E*a) ≤ average m f a δ-a*(1+δ/2) at hl
  have hEa : E*a≤E*x := mul_le_mul_of_nonneg_left hax hE
  have hda : δ*a≤δ*x := mul_le_mul_of_nonneg_left hax hd
  apply abs_le.mpr
  constructor <;> nlinarith
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.average_id
#print axioms DusartLegendreSmoothing.average_monotone_bounds
#print axioms DusartLegendreSmoothing.desmoothing


