-- Prove2me | Definitions.Def_OAIQWBNS000
-- name    : OAIQWBNS000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:34:37.194132+00:00
-- url     : https://prove2.me/theorems/2e71fa73-3545-4ca5-b351-81a86580f97f
-- title:
--   OpenAI Bernoulli cone split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that $\mathbb R^7$ carries a nonzero, one-homogeneous, nonflat global minimizer of the one-phase Bernoulli energy (`OAI.Bernoulli.nonflat_in_seven`, the second assertion of the paper's Theorem 1.1, which the paper takes from De Silva and Jerison). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/BernoulliCone` (OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, OpenAI Math Release, September 24, 2026, result family 367, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the De Silva–Jerison double cone `DeSilvaJerison.U` with its spherical profile (`DeSilvaJerison.p`, `DeSilvaJerison.t7`, `DeSilvaJerison.κ`), the cap and outer supersolutions and the upper foliation by their dilates (`DeSilvaJerison.smoothCap`, `DeSilvaJerison.outerSigned`, `DeSilvaJerison.upperFamily`, `DeSilvaJerison.upperParameter`, `DeSilvaJerison.upperFlux`), and the vertical potential and divergence of the calibration argument (`Foliation.verticalPotential`, `Foliation.divergence`).
--
--   The definitions of the published statement (`Space`, `H1`, `H10`, `energy`, `GlobalMinimizer`, `OneHomogeneous`, `Nonzero`, `Flat` and the rest) are not repeated: the bundle imports them from the published bundle `Def_BernoulliNonflatInSeven`. It imports no other bundle of this split.
--
--   Modules (some only in part): `BoundedCalibration`, `CapCalculus`, `CapFoliation`, `CapGeometry`, `ClampedFoliationGraph`, `CylindricalCalculus`, `FoliationBulkGerm`, `FoliationDifferential`, `FoliationGraph`, `IntegratedPrimitive`, `JointIntervalIntegral`, `LocalFluxExtensions`, `LowerSupport`, `OuterGeometry`, `PiecewiseFoliationGraph`, `PositiveFoliation`, `PositiveQuotient`, `ScalarLaplacian`, `SeamCalibration`, `SeamHeight`, `SobolevCalculus`, `SobolevIdeals`, `ThresholdRecovery`, `UpperCalibration`, `UpperFamily`, `UpperFoliation`, `UpperLeaves`, `UpperLimits`, `UpperLipschitzComparison`, `UpperSeam`, `UpperSupport`, `VerticalGraphLocalization`.
--
--   The theorems the definitions do not need are proved in the four solutions of this split. One proves the published intermediate statement `OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound`, one proves `OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison` from it, one proves `OAI.Bernoulli.DeSilvaJerison.U_global_minimizer` from that, and the fourth proves `OAI.Bernoulli.nonflat_in_seven`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The critical dimension for one-phase Bernoulli minimizers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 367; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/BernoulliCone at commit adc7f12

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven

section
-- module Solutions.OAIQW_BernoulliCone.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SobolevCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uE uF uK uι

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution

namespace Bernoulli.Mollification
open scoped _root_.Bernoulli

variable {d : ℕ}
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
variable {F : Type uF} [NormedAddCommGroup F]

/-- Translation on the actual Lebesgue L² space. -/
def translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    Lp F 2 (volume : Measure (Space d)) :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) f

@[simp] lemma norm_translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    ‖translate f y‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f (measurePreserving_sub_right volume y)

section Inner
variable [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma memLp_convolution {κ : Space d → ℝ} {f : Space d → F}
    (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    MemLp (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) 2 volume :=
  (hcκ.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    (hf.locallyIntegrable (by norm_num))).memLp_of_hasCompactSupport
    (hcκ.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcf)

end Inner

end Bernoulli.Mollification

namespace Bernoulli.SobolevDensity
open scoped _root_.Bernoulli
open scoped Convolution
variable {d : ℕ}

open scoped Pointwise

/-- A fixed sequence of positive-radius smooth normalized mollifiers. -/
def bumps (d : ℕ) (n : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    apply one_div_lt_one_div_of_lt hn
    nlinarith

end Bernoulli.SobolevDensity

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli

def cutSlope (n : ℕ) (t : ℝ) : ℝ := min (max (((n : ℝ)+1)*t) 0) 1

def cutPrimitive (n : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, cutSlope n s

@[simp] lemma cutPrimitive_zero (n : ℕ) : cutPrimitive n 0 = 0 := by
  simp [cutPrimitive]

end Bernoulli.SobolevCalculus

open scoped Manifold

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LowerSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open Set Filter Finset
open scoped Topology
namespace Bernoulli.DeSilvaJerison

/-- Half the logarithmic ratio; it is artanh on (-1,1). -/
def A (t : ℝ) : ℝ := (Real.log (1+t) - Real.log (1-t))/2

/-- The even solution of (1-t²)f''-6tf'+6f=0 with f(0)=1. -/
def f (t : ℝ) : ℝ :=
  (8-25*t^2+15*t^4)/(8*(1-t^2)^2) - (15/8)*t*A t

/-- A convenient rational-logarithmic expression for f'. -/
def fp (t : ℝ) : ℝ :=
  -t/(1-t^2)^3 - (5/4)*t/(1-t^2)^2 - (15/8)*t/(1-t^2) - (15/8)*A t

lemma A_neg (t : ℝ) : A (-t) = -A t := by
  simp only [A, sub_eq_add_neg, neg_neg]
  ring

@[simp] lemma A_zero : A 0 = 0 := by simp [A]
@[simp] lemma f_zero : f 0 = 1 := by norm_num [f]
@[simp] lemma fp_zero : fp 0 = 0 := by simp [fp]

lemma f_neg (t : ℝ) : f (-t) = f t := by
  simp only [f, neg_sq, A_neg]
  ring

lemma A_eq_half_log {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    A t = 1/2 * Real.log ((1+t)/(1-t)) := by
  rw [Real.log_div (by linarith [ht.1] : 1+t≠0) (by linarith [ht.2] : 1-t≠0)]
  unfold A
  ring

lemma hasDerivAt_A {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt A (1/(1-t^2)) t := by
  have hp : 1+t≠0 := by linarith [ht.1]
  have hm : 1-t≠0 := by linarith [ht.2]
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  apply (((((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log hm)).div_const 2).congr_deriv
  norm_num
  field_simp [hd,hp,hm]
  ring

lemma hasDerivAt_f {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt f (fp t) t := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hden : 8*(1-t^2)^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hd)
  have hnum := ((hasDerivAt_const t (8:ℝ)).sub
    (((hasDerivAt_id t).pow 2).const_mul 25)).add
      (((hasDerivAt_id t).pow 4).const_mul 15)
  have hden' := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2).const_mul 8
  apply ((hnum.div hden' hden).sub
    (((hasDerivAt_id t).const_mul (15/8)).mul (hasDerivAt_A ht))).congr_deriv
  norm_num [fp]
  field_simp [hd]
  ring

lemma hasDerivAt_fp {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt fp (-6/(1-t^2)^4) t := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hD := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)
  apply (((((hasDerivAt_id t).neg.div (hD.pow 3) (pow_ne_zero _ hd)).sub
    (((hasDerivAt_id t).const_mul (5/4)).div (hD.pow 2) (pow_ne_zero _ hd))).sub
    (((hasDerivAt_id t).const_mul (15/8)).div hD hd)).sub
    ((hasDerivAt_A ht).const_mul (15/8))).congr_deriv
  norm_num
  field_simp [hd]
  ring

lemma f_relation {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    t * fp t - f t = -1/(1-t^2)^3 := by
  have hd : 1-t^2≠0 := by nlinarith [ht.1,ht.2]
  unfold fp f
  field_simp
  ring

lemma A_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : 0 ≤ A t := by
  rw [A_eq_half_log ⟨by linarith,ht1⟩]
  exact mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith)))

lemma fp_neg {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : fp t < 0 := by
  have hD : 0<1-t^2 := by nlinarith
  have hA := A_nonneg ht.le ht1
  have h1 : 0 < t/(1-t^2)^3 := div_pos ht (pow_pos hD _)
  have h2 : 0 ≤ (5/4:ℝ)*t/(1-t^2)^2 := by positivity
  have h3 : 0 ≤ (15/8:ℝ)*t/(1-t^2) := by positivity
  unfold fp
  rw [neg_div]
  nlinarith

lemma f_strictAnti : StrictAntiOn f (Ico (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro t ht
    exact (hasDerivAt_f ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    rw [(hasDerivAt_f ⟨by linarith [ht.1],ht.2⟩).deriv]
    exact fp_neg ht.1 ht.2

/-- A certified enclosure, replacing the decimal root in the preprint. -/
lemma f_lower_pos : 0 < f (517330/1000000) := by
  have hA : A (517330/1000000) ≤ 5726875/10000000 := by
    rw [A_eq_half_log (by norm_num)]
    refine (Real.log_div_le_sum_range_add (by norm_num) (by norm_num) 12).trans ?_
    norm_num [Finset.sum_range_succ]
  unfold f
  norm_num at hA ⊢
  linarith

lemma f_upper_neg : f (517331/1000000) < 0 := by
  have hA : 572688/1000000 ≤ A (517331/1000000) := by
    rw [A_eq_half_log (by norm_num)]
    refine le_trans ?_ (Real.sum_range_le_log_div (by norm_num) (by norm_num) 12)
    norm_num [Finset.sum_range_succ]
  unfold f
  norm_num at hA ⊢
  linarith

lemma exists_profile_root : ∃ t ∈ Icc (517330/1000000 : ℝ) (517331/1000000), f t = 0 := by
  have hc : ContinuousOn f (Icc (517330/1000000 : ℝ) (517331/1000000)) := by
    intro t ht
    exact (hasDerivAt_f ⟨by linarith [ht.1],by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' (by norm_num : (517330/1000000 : ℝ) ≤ 517331/1000000)
    hc ⟨f_upper_neg.le, f_lower_pos.le⟩
  exact ⟨t,ht,hft⟩

/-- The first positive root t₇ of the normalized profile. -/
def t7 : ℝ := exists_profile_root.choose

lemma t7_bounds : t7 ∈ Icc (517330/1000000 : ℝ) (517331/1000000) :=
  exists_profile_root.choose_spec.1

@[simp] lemma f_t7 : f t7 = 0 := exists_profile_root.choose_spec.2

lemma t7_pos : 0 < t7 := by linarith [t7_bounds.1]
lemma t7_lt_one : t7 < 1 := by linarith [t7_bounds.2]

lemma f_pos_of_abs_lt {t : ℝ} (ht : |t| < t7) : 0 < f t := by
  have h : 0 < f |t| := by
    rw [← f_t7]
    exact f_strictAnti ⟨abs_nonneg t,lt_trans ht t7_lt_one⟩
      ⟨t7_pos.le,t7_lt_one⟩ ht
  by_cases h0 : 0 ≤ t
  · simpa [abs_of_nonneg h0] using h
  · simpa [abs_of_neg (lt_of_not_ge h0), f_neg] using h

/-- The square of the normal derivative of the unscaled conical function. -/
def c7 : ℝ := (1-t7^2) * (fp t7)^2

lemma c7_pos : 0 < c7 := by
  have hD : 0 < 1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  exact mul_pos hD (sq_pos_of_neg (fp_neg t7_pos t7_lt_one))

lemma contDiffAt_f {n : WithTop ℕ∞} {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ n f t := by
  have hd : 8*(1-t^2)^2≠0 := by
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero _ (by nlinarith [ht.1,ht.2])
  have hp : 1+t≠0 := by linarith [ht.1]
  have hm : 1-t≠0 := by linarith [ht.2]
  unfold f A
  fun_prop

/-- Extend the positive spherical profile by zero outside its first two roots. -/
def p (t : ℝ) : ℝ := f (min |t| t7)

lemma f_abs (t : ℝ) : f |t| = f t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), f_neg]

lemma p_eq_f {t : ℝ} (ht : |t| ≤ t7) : p t = f t := by
  rw [p, min_eq_left ht, f_abs]

lemma p_eq_zero {t : ℝ} (ht : t7 ≤ |t|) : p t = 0 := by
  rw [p, min_eq_right ht, f_t7]

@[simp] lemma p_zero : p 0 = 1 := by rw [p_eq_f (by simpa using t7_pos.le), f_zero]

lemma p_pos_iff (t : ℝ) : 0 < p t ↔ |t| < t7 := by
  constructor
  · intro ht
    by_contra hn
    rw [p_eq_zero (le_of_not_gt hn)] at ht
    exact lt_irrefl 0 ht
  · intro ht
    rw [p_eq_f ht.le]
    exact f_pos_of_abs_lt ht

lemma p_nonneg (t : ℝ) : 0 ≤ p t := by
  rcases lt_or_ge |t| t7 with ht | ht
  · exact ((p_pos_iff t).mpr ht).le
  · rw [p_eq_zero ht]

/-- The normalization imposed by the Bernoulli condition. -/
def κ : ℝ := (Real.sqrt c7)⁻¹

lemma κ_pos : 0 < κ := inv_pos.mpr (Real.sqrt_pos.mpr c7_pos)

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

/-- The homogeneous, nonnegative profile, prior to normalizing its boundary slope. -/
def Z (x : Space 7) : ℝ := ‖x‖ * p (x 6 / ‖x‖)

def U (x : Space 7) : ℝ := κ * Z x

@[simp] lemma Z_zero : Z 0 = 0 := by simp [Z]
@[simp] lemma U_zero : U 0 = 0 := by simp [U]
lemma Z_nonneg (x : Space 7) : 0 ≤ Z x := mul_nonneg (norm_nonneg x) (p_nonneg _)
lemma U_nonneg (x : Space 7) : 0 ≤ U x := mul_nonneg κ_pos.le (Z_nonneg x)

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Axisymmetric
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_radius (x v : E) (t : ℝ) (h : x+t • v ≠ 0) :
    HasDerivAt (fun a:ℝ=>‖x+a • v‖)
      (inner ℝ (x+t • v) v / ‖x+t • v‖) t := by
  have hc : HasDerivAt (fun a:ℝ=>x+a • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hn : ‖x+t • v‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hh := hc.norm_sq.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1; field_simp

lemma hasDerivAt_axis (x v e : E) (t : ℝ) :
    HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) e) (inner ℝ v e) t := by
  have hc : HasDerivAt (fun a:ℝ=>x+a • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  simpa using hc.inner ℝ (hasDerivAt_const t e)

/-- Lift of a polar profile; values at the origin use the usual total operations. -/
def lift (e : E) (α : ℝ) (φ : ℝ → ℝ) (x : E) : ℝ :=
  ‖x‖ ^ α * φ (inner ℝ x e / ‖x‖)

lemma hasDerivAt_angular (x v e : E) (t : ℝ) (h : x+t • v≠0) :
    HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) e / ‖x+a • v‖)
      ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
        inner ℝ (x+t • v) v) / ‖x+t • v‖^3) t := by
  have hn := norm_ne_zero_iff.mpr h
  apply ((hasDerivAt_axis x v e t).div (hasDerivAt_radius x v t h) hn).congr_deriv
  field_simp

lemma hasDerivAt_lift_line {φ : ℝ → ℝ} {φ' : ℝ} (e x v : E) (α t : ℝ)
    (hx : x+t • v≠0)
    (hφ : HasDerivAt φ φ' (inner ℝ (x+t • v) e / ‖x+t • v‖)) :
    HasDerivAt (fun a:ℝ=>lift e α φ (x+a • v))
      (‖x+t • v‖^α *
        (α * inner ℝ (x+t • v) v / ‖x+t • v‖^2 * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) +
          φ' * ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
            inner ℝ (x+t • v) v) / ‖x+t • v‖^3))) t := by
  have hn := norm_ne_zero_iff.mpr hx
  have hr := (hasDerivAt_radius x v t hx).rpow_const (p:=α) (Or.inl hn)
  have hp := hφ.comp t (hasDerivAt_angular x v e t hx)
  apply (hr.mul hp).congr_deriv
  simp only [Function.comp_def]
  rw [Real.rpow_sub_one hn]
  field_simp

/-- The explicit first derivative along a line, used to avoid assuming an ODE
or a second derivative in the Euclidean Laplacian computation. -/
def lineFirst (e x v : E) (α : ℝ) (φ φ₁ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖x+t • v‖^α *
    (α * inner ℝ (x+t • v) v / ‖x+t • v‖^2 * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) +
      φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
        ((inner ℝ v e * ‖x+t • v‖^2 - inner ℝ (x+t • v) e *
          inner ℝ (x+t • v) v) / ‖x+t • v‖^3))

/-- Scalar diagonal Hessian coefficient in a unit radial/angular frame. -/
def secondCoeff (α F F₁ F₂ s p b n : ℝ) : ℝ :=
  α*F*n + α*(α-2)*F*p^2 + 2*(α-1)*F₁*p*(b-s*p) -
    s*F₁*(n-p^2) + F₂*(b-s*p)^2

lemma contDiffAt_lift {φ : ℝ → ℝ} {e x : E} {α : ℝ} {n : WithTop ℕ∞}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ n φ (inner ℝ x e / ‖x‖)) :
    ContDiffAt ℝ n (lift e α φ) x := by
  have hn : ContDiffAt ℝ n (fun y:E=>‖y‖) x := contDiffAt_id.norm ℝ hx
  have ha : ContDiffAt ℝ n (fun y:E=>inner ℝ y e / ‖y‖) x :=
    ((contDiffAt_id.inner ℝ contDiffAt_const).div hn (norm_ne_zero_iff.mpr hx))
  exact (hn.rpow_const_of_ne (norm_ne_zero_iff.mpr hx)).mul (hf.comp x ha)

/-- The radial unit vector (at nonzero points) and the tangential polar direction. -/
def radial (x : E) : E := ‖x‖⁻¹ • x

def polarGradient (e x : E) (a b : ℝ) : E :=
  a • radial x + b • (e - (inner ℝ x e / ‖x‖) • radial x)

lemma hasGradientAt_lift [CompleteSpace E] {φ : ℝ → ℝ} {φ₁ : ℝ}
    (e x : E) (α : ℝ) (hx : x≠0)
    (hφ : HasDerivAt φ φ₁ (inner ℝ x e / ‖x‖)) :
    HasGradientAt (lift e α φ)
      ((‖x‖^α / ‖x‖) • polarGradient e x (α*φ (inner ℝ x e / ‖x‖)) φ₁) x := by
  have hn := norm_ne_zero_iff.mpr hx
  have hdN : DifferentiableAt ℝ (fun y:E=>‖y‖) x := differentiableAt_id.norm ℝ hx
  have ha : ContDiffAt ℝ 1 (fun y:E=>inner ℝ y e / ‖y‖) x :=
    (contDiffAt_id.inner ℝ contDiffAt_const).div (contDiffAt_id.norm ℝ hx) hn
  have hdA := ha.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hd : DifferentiableAt ℝ (lift e α φ) x := by
    exact (hdN.rpow_const (Or.inl hn)).fun_mul (hφ.differentiableAt.comp x hdA)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply hd.hasFDerivAt.congr_fderiv
  ext v
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd0 : HasFDerivAt (lift e α φ) (fderiv ℝ (lift e α φ) x) (x+(0:ℝ) • v) := by
    simpa using hd.hasFDerivAt
  have hcomp := hd0.comp_hasDerivAt (0:ℝ) hl
  have hline := hasDerivAt_lift_line e x v α 0 (by simpa using hx) (by simpa using hφ)
  simp only [zero_smul,add_zero] at hline
  rw [hcomp.unique hline]
  simp only [InnerProductSpace.toDual_apply_apply,real_inner_smul_left,polarGradient,
    inner_add_left,inner_sub_left,real_inner_smul_left,radial,real_inner_smul_left,
    real_inner_comm e v]
  field_simp

end Bernoulli.Axisymmetric

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

def axis : Space 7 := EuclideanSpace.single 6 1

def angle (x : Space 7) : ℝ := x 6 / ‖x‖

@[simp] lemma axis_norm : ‖axis‖=1 := by simp [axis]
@[simp] lemma inner_axis (x : Space 7) : inner ℝ x axis=x 6 := by
  simp [axis, EuclideanSpace.inner_single_right]

lemma U_pos_iff (x : Space 7) : 0<U x ↔ x≠0 ∧ |angle x|<t7 := by
  rw [U, mul_pos_iff_of_pos_left κ_pos,Z]
  constructor
  · intro h
    have hx : x≠0 := by rintro rfl; simp at h
    exact ⟨hx, (p_pos_iff _).mp ((mul_pos_iff_of_pos_left (norm_pos_iff.mpr hx)).mp h)⟩
  · rintro ⟨hx,ht⟩
    exact mul_pos (norm_pos_iff.mpr hx) ((p_pos_iff _).mpr ht)

/-- Smooth signed extension near the free boundary away from the singular axis. -/
def Zsigned : Space 7 → ℝ := lift axis 1 f

def Usigned (x : Space 7) : ℝ := κ*Zsigned x

lemma Zsigned_eq (x : Space 7) : Zsigned x=‖x‖*f (angle x) := by
  simp [Zsigned,lift,angle]

lemma signed_contDiffAt {x : Space 7} {n : WithTop ℕ∞} (hx : x≠0)
    (ha : |angle x|<1) : ContDiffAt ℝ n Zsigned x := by
  apply contDiffAt_lift hx
  simpa only [inner_axis,angle] using contDiffAt_f (abs_lt.mp ha)

lemma gradient_const_mul {F : Space 7 → ℝ} {x : Space 7} (c : ℝ)
    (hF : DifferentiableAt ℝ F x) :
    gradient (fun y=>c*F y) x=c • gradient F x := by
  rw [gradient, fderiv_const_mul hF]
  simp only [map_smul,gradient]

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open scoped BigOperators

def B (n:ℕ) (u:ℝ) : ℝ := ∑ i ∈ Finset.range n, u^i / (2*i+1)

lemma odd_sum_eq (n:ℕ) (t:ℝ) :
    (∑ i ∈ Finset.range n, t^(2*i+1)/(2*i+1))=t*B n (t^2) := by
  rw [B,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add,pow_mul]
  ring

lemma A_series_bounds (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    t*B n (t^2) ≤ A t ∧ A t ≤ t*(B n (t^2)+(t^2)^n/(1-t^2)) := by
  have hI : t∈Ioo (-1:ℝ) 1 := ⟨by linarith,ht1⟩
  have hL := Real.sum_range_le_log_div ht ht1 n
  have hU := Real.log_div_le_sum_range_add ht ht1 n
  rw [odd_sum_eq,A_eq_half_log hI] at *
  constructor
  · exact hL
  · convert hU using 1
    rw [pow_add,pow_mul]
    ring

end Bernoulli.DeSilvaJerison

noncomputable section
open scoped BigOperators
namespace Bernoulli.DeSilvaJerison.Algebra
def g (u:ℝ) : ℝ := (1+u*((2869387/1000000:ℝ)+u*((589981/125000:ℝ)+u*((6566689/1000000:ℝ)+u*((4206127/500000:ℝ)+u*((10257227/1000000:ℝ)+u*((6050939/500000:ℝ)+u*((2789267/200000:ℝ)+u*(7895333/500000:ℝ)))))))))

def g1 (u:ℝ) : ℝ := ((2869387/1000000:ℝ)+u*((589981/62500:ℝ)+u*((19700067/1000000:ℝ)+u*((4206127/125000:ℝ)+u*((10257227/200000:ℝ)+u*((18152817/250000:ℝ)+u*((19524869/200000:ℝ)+u*(7895333/62500:ℝ))))))))

def g2 (u:ℝ) : ℝ := ((589981/62500:ℝ)+u*((19700067/500000:ℝ)+u*((12618381/125000:ℝ)+u*((10257227/50000:ℝ)+u*((18152817/50000:ℝ)+u*((58574607/100000:ℝ)+u*(55267331/62500:ℝ)))))))

def FlowNum (u:ℝ) : ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))

def JlowNum (u:ℝ) : ℝ := (48+u*(-80+u*(48+u*((-48/7:ℝ)+u*((-16/21:ℝ)+u*((-16/77:ℝ)+u*((-95/77:ℝ)+u*((80/33:ℝ)+u*(-15/11:ℝ)))))))))

def H (u:ℝ) : ℝ :=
 (1-(-643/200:ℝ))^2 * (FlowNum u)^2*(1-u)^2*(g u)^2
 +u*(1-u)*(JlowNum u*g u+2*FlowNum u*(1-u)*g1 u)^2
 -64*(177344/10000:ℝ)*(1-u)^6*(g u)^2

def bern (x:ℝ) :ℝ :=
 (1273/625:ℝ)*x^0*(1-x)^34 +
 (18301700752813/39062500000:ℝ)*x^1*(1-x)^33 +
 (215052290412518053937/15625000000000000:ℝ)*x^2*(1-x)^32 +
 (4011660524023528296977/19531250000000000:ℝ)*x^3*(1-x)^31 +
 (2737813200177456418780827/1367187500000000000:ℝ)*x^4*(1-x)^30 +
 (36470062299690915838876891/2563476562500000000:ℝ)*x^5*(1-x)^29 +
 (25224069904037561558116841153/322265625000000000000:ℝ)*x^6*(1-x)^28 +
 (1140064408982925692415284885429/3289794921875000000000:ℝ)*x^7*(1-x)^27 +
 (41702430755303183867323989789361/32897949218750000000000:ℝ)*x^8*(1-x)^26 +
 (3302410109850186979935464577903227/845947265625000000000000:ℝ)*x^9*(1-x)^25 +
 (607809096133375762153335847523839391/59216308593750000000000000:ℝ)*x^10*(1-x)^24 +
 (8427099588852868346099742136229588957/361877441406250000000000000:ℝ)*x^11*(1-x)^23 +
 (83162165720757436741420385026341254509/1809387207031250000000000000:ℝ)*x^12*(1-x)^22 +
 (6465714023183326120974320513863787790989/81422424316406250000000000000:ℝ)*x^13*(1-x)^21 +
 (3070489019357153411700150072588091455833/25444507598876953125000000000:ℝ)*x^14*(1-x)^20 +
 (82369624574464912186052678411201103823739/508890151977539062500000000000:ℝ)*x^15*(1-x)^19 +
 (3910314359275519861283649778682853171355229/20355606079101562500000000000000:ℝ)*x^16*(1-x)^18 +
 (979175253390516279186463881299949127320211/4846572875976562500000000000000:ℝ)*x^17*(1-x)^17 +
 (18263450287363530970672089631693726965414361/96931457519531250000000000000000:ℝ)*x^18*(1-x)^16 +
 (17617068143172995639202711944743442184849557/113086700439453125000000000000000:ℝ)*x^19*(1-x)^15 +
 (5805157568137808862325200615665450856083238073/50889015197753906250000000000000000:ℝ)*x^20*(1-x)^14 +
 (106751395374573342818643134988112428956196041/1445710659027099609375000000000000:ℝ)*x^21*(1-x)^13 +
 (13399476602886887470912830751358415258789263239/318056344985961914062500000000000000:ℝ)*x^22*(1-x)^12 +
 (203394843320074906765348971241270582814374973/9638071060180664062500000000000000:ℝ)*x^23*(1-x)^11 +
 (73412104728736551372464217800669117696986097123/7951408624649047851562500000000000000:ℝ)*x^24*(1-x)^10 +
 (139309476218905417280721075386752271276084623033/39757043123245239257812500000000000000:ℝ)*x^25*(1-x)^9 +
 (32477127068915750179291210097408098171730074813/28397887945175170898437500000000000000:ℝ)*x^26*(1-x)^8 +
 (39433145196824909814460561789894422591933034093/124240759760141372680664062500000000000:ℝ)*x^27*(1-x)^7 +
 (1852317908162190170035216935656039577364200647/25099143385887145996093750000000000000:ℝ)*x^28*(1-x)^6 +
 (5836982899230309706402487066150347002468521567/414135865867137908935546875000000000000:ℝ)*x^29*(1-x)^5 +
 (53440683331803983473324825254354074715316174661/24848151952028274536132812500000000000000:ℝ)*x^30*(1-x)^4 +
 (1564303979409844850797520400352897238700085837/6212037988007068634033203125000000000000:ℝ)*x^31*(1-x)^3 +
 (219633445088755317503000659291685432421229847/10353396646678447723388671875000000000000:ℝ)*x^32*(1-x)^2 +
 (4437106302213137739667714564011045560602003/3882523742504417896270751953125000000000:ℝ)*x^33*(1-x)^1 +
 (57307964213152837654157884692498315776209/1941261871252208948135375976562500000000:ℝ)*x^34*(1-x)^0

end Bernoulli.DeSilvaJerison.Algebra

namespace Bernoulli.DeSilvaJerison

def gSub (t:ℝ) : ℝ := Algebra.g (t^2)
def gSub1 (t:ℝ) : ℝ := 2*t*Algebra.g1 (t^2)
def gSub2 (t:ℝ) : ℝ := 2*Algebra.g1 (t^2)+4*t^2*Algebra.g2 (t^2)
def qSub (t:ℝ) : ℝ := gSub1 t/gSub t

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

/-- The free-boundary gradient numerator for the explicit lower barrier. -/
def GSub (t:ℝ) : ℝ := (1-(-643/200:ℝ))^2*(f t)^2+
  (1-t^2)*(fp t-f t*qSub t)^2

def FLo (t:ℝ) : ℝ := Algebra.FlowNum (t^2)/(8*(1-t^2)^2)
def JLo (t:ℝ) : ℝ := Algebra.JlowNum (t^2)/(8*(1-t^2)^3)

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

/-- Positive superharmonic ground state used by the lower comparison. -/
def YSub : Space 7 → ℝ := lift axis (-643/200) gSub

end Bernoulli.DeSilvaJerison

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ScalarLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma line_deriv {f:E→ℝ} {x:E} (hf:DifferentiableAt ℝ f x) (v:E) :
    deriv (fun t:ℝ=>f (x+t • v)) 0 = inner ℝ (gradient f x) v := by
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • v) := by simpa using hf.hasFDerivAt
  simpa only [Function.comp_def,inner_gradient_left] using (hfx.comp_hasDerivAt 0 hl).deriv

lemma gradient_mul {f g:E→ℝ} {x:E} (hf:DifferentiableAt ℝ f x)
    (hg:DifferentiableAt ℝ g x) :
    gradient (fun y=>f y*g y) x = g x • gradient f x + f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left,
    inner_gradient_left,inner_gradient_left]
  change (fderiv ℝ (f*g) x) v = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma gradient_comp {φ:ℝ→ℝ} {f:E→ℝ} {x:E} (hφ:DifferentiableAt ℝ φ (f x))
    (hf:DifferentiableAt ℝ f x) :
    gradient (fun y=>φ (f y)) x = deriv φ (f x) • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (φ ∘ f) x) v = _
  rw [inner_gradient_left,fderiv_comp x hφ hf,ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul,real_inner_smul_left,inner_gradient_left]

end Bernoulli.ScalarLaplacian

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CylindricalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
open ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
def axis (e x:E) : ℝ := inner ℝ x e
def transverse (e x:E) : E := x-axis e x • e
def radiusSq (e x:E) : ℝ := ‖x‖^2-(axis e x)^2

omit [FiniteDimensional ℝ E] in
theorem transverse_sq [FiniteDimensional ℝ E] (e x:E) (he:‖e‖=1) : ‖transverse e x‖^2=radiusSq e x := by
  rw [transverse,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,he,
    real_inner_smul_right]
  unfold radiusSq axis
  ring
lemma radiusSq_nonneg (e x:E) (he:‖e‖=1) : 0≤radiusSq e x := by
  rw [←transverse_sq e x he]; positivity
omit [FiniteDimensional ℝ E] in
lemma axis_contDiff [FiniteDimensional ℝ E] (e:E) {n:WithTop ℕ∞} : ContDiff ℝ n (axis e) := contDiff_id.inner ℝ contDiff_const
lemma radiusSq_contDiff (e:E) {n:WithTop ℕ∞} : ContDiff ℝ n (radiusSq e) :=
  (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=n)).sub ((axis_contDiff e).pow 2)
lemma gradient_axis (e x:E) : gradient (axis e) x=e := by
  apply ext_inner_right ℝ
  intro v
  rw [←line_deriv (axis_contDiff e (n:=1) |>.differentiable (by norm_num) x) v]
  have hh:=Axisymmetric.hasDerivAt_axis x v e 0
  change deriv (fun t:ℝ=>inner ℝ (x+t • v) e) 0 = _
  rw [hh.deriv,real_inner_comm]
lemma gradient_norm_sq (x:E) : gradient (fun z:E=>‖z‖^2) x=(2:ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [←line_deriv (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=1) |>.differentiable (by norm_num) x) v]
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  rw [hl.norm_sq.deriv]
  simp [real_inner_smul_left]
lemma gradient_radiusSq (e x:E) : gradient (radiusSq e) x=(2:ℝ) • transverse e x := by
  have ha := (axis_contDiff e (n:=1)).differentiable (by norm_num) x
  have hn := (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=1)).differentiable (by norm_num) x
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  change (fderiv ℝ (fun z:E=>‖z‖^2-(axis e z)^2) x) v = _
  have hh:=hn.hasFDerivAt.sub (ha.hasFDerivAt.pow 2)
  change (fderiv ℝ ((fun z:E=>‖z‖^2)-(fun z:E=>(axis e z)^2)) x) v = _
  rw [hh.fderiv]
  simp only [sub_apply,smul_apply]
  rw [←inner_gradient_left,gradient_norm_sq,←inner_gradient_left,gradient_axis]
  dsimp [transverse]
  simp only [real_inner_smul_left,inner_sub_left]
  ring

/-- A smooth cylindrical cap, expressed using the squared transverse radius so
that the symmetry axis is included without a singular-coordinate convention. -/
def lift (e:E) (y k h:ℝ→ℝ) (x:E) : ℝ := y (radiusSq e x)*h (axis e x*k (radiusSq e x))
lemma contDiffAt_lift {e x:E} {y k h:ℝ→ℝ} {n:WithTop ℕ∞}
    (hy:ContDiffAt ℝ n y (radiusSq e x)) (hk:ContDiffAt ℝ n k (radiusSq e x))
    (hh:ContDiffAt ℝ n h (axis e x*k (radiusSq e x))) : ContDiffAt ℝ n (lift e y k h) x := by
  exact (hy.comp x (radiusSq_contDiff e).contDiffAt).mul
    (hh.comp x ((axis_contDiff e).contDiffAt.mul (hk.comp x (radiusSq_contDiff e).contDiffAt)))

lemma gradient_lift {e x:E} {y k h:ℝ→ℝ}
    (hy:DifferentiableAt ℝ y (radiusSq e x)) (hk:DifferentiableAt ℝ k (radiusSq e x))
    (hh:DifferentiableAt ℝ h (axis e x*k (radiusSq e x))) :
    gradient (lift e y k h) x =
      (2*deriv y (radiusSq e x)*h (axis e x*k (radiusSq e x))) • transverse e x+
      (y (radiusSq e x)*deriv h (axis e x*k (radiusSq e x))) •
        (k (radiusSq e x) • e+(2*axis e x*deriv k (radiusSq e x)) • transverse e x) := by
  have hq: DifferentiableAt ℝ (radiusSq e) x :=
    (radiusSq_contDiff e (n:=1)).differentiable (by norm_num) x
  have ha: DifferentiableAt ℝ (axis e) x :=
    (axis_contDiff e (n:=1)).differentiable (by norm_num) x
  have hyq : DifferentiableAt ℝ (fun z=>y (radiusSq e z)) x := hy.comp x hq
  have hkq : DifferentiableAt ℝ (fun z=>k (radiusSq e z)) x := hk.comp x hq
  have hs : DifferentiableAt ℝ (fun z=>axis e z*k (radiusSq e z)) x := ha.mul hkq
  have hhs : DifferentiableAt ℝ (fun z=>h (axis e z*k (radiusSq e z))) x := hh.comp x hs
  change gradient (fun z=>y (radiusSq e z)*h (axis e z*k (radiusSq e z))) x=_
  rw [gradient_mul hyq hhs,gradient_comp hy hq,gradient_comp (f:=fun z:E=>axis e z*k (radiusSq e z)) hh hs,
    gradient_mul ha hkq,gradient_comp hk hq,gradient_radiusSq,gradient_axis]
  simp only [smul_smul]
  module

end Bernoulli.Cylindrical

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison.UpperAlgebra
def flo (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))

def fhi (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((35/33:ℝ)+u*(-15/11:ℝ)))))))))

def numerator (u F:ℝ) :ℝ := 9*u*(1-u)*(1+u)^2*F^2+
  ((1-6*u-3*u^2)*F-8*(1+u))^2
def denominator (u:ℝ) :ℝ := 64*u*(1-u)^5*(1+u)^2
def bern_lo (x:ℝ) :ℝ :=
 (8963403802771821580584196553916675261935501120693147951646273/14551915228366851806640625000000000000000000000000000000000000:ℝ)*x^0*(1-x)^19 +
 (489924829765456954778865308004779162353303628212611757632243/36379788070917129516601562500000000000000000000000000000000:ℝ)*x^1*(1-x)^18 +
 (49769555037754151943109135153056907940324983405814454742197/363797880709171295166015625000000000000000000000000000000:ℝ)*x^2*(1-x)^17 +
 (241171544309613921452176651513547035701117488149602398545521/280124368146061897277832031250000000000000000000000000000:ℝ)*x^3*(1-x)^16 +
 (813419086138655742693400878597426747137820729361029314453283/215695763472467660903930664062500000000000000000000000000:ℝ)*x^4*(1-x)^15 +
 (26390534901568505873385225990643235317241761460076963637719/2156957634724676609039306640625000000000000000000000000:ℝ)*x^5*(1-x)^14 +
 (164606421874770730021787386234243493522999746324215690279/5392394086811691522598266601562500000000000000000000:ℝ)*x^6*(1-x)^13 +
 (12937649845297388757164077325683850040267461146379488389/215695763472467660903930664062500000000000000000000:ℝ)*x^7*(1-x)^12 +
 (406574381504531640456151479204496276555618768129464927/4313915269449353218078613281250000000000000000000:ℝ)*x^8*(1-x)^11 +
 (234332377637560595227876241971859462384073890057109/1960870577022433280944824218750000000000000000:ℝ)*x^9*(1-x)^10 +
 (1203984888564608030855581683826211128963939859577/9804352885112166404724121093750000000000000:ℝ)*x^10*(1-x)^9 +
 (2506388470738655109137023670431246929874450257/24510882212780416011810302734375000000000:ℝ)*x^11*(1-x)^8 +
 (16837782271327404835800216484886618277280203/245108822127804160118103027343750000000:ℝ)*x^12*(1-x)^7 +
 (723289103741917289394757467584219903883291/19608705770224332809448242187500000000:ℝ)*x^13*(1-x)^6 +
 (47755665140733764406977363749637036181/3063860276597552001476287841796875:ℝ)*x^14*(1-x)^5 +
 (109117483702727600919378994299975467223/21569576347246766090393066406250000:ℝ)*x^15*(1-x)^4 +
 (1047331065768340618289444397103804113/862783053889870643615722656250000:ℝ)*x^16*(1-x)^3 +
 (436047208669296315095634434961738/2156957634724676609039306640625:ℝ)*x^17*(1-x)^2 +
 (255902850597815514061767304524/12325472198426723480224609375:ℝ)*x^18*(1-x)^1 +
 (3394151041074323326944784128/3451132215559482574462890625:ℝ)*x^19*(1-x)^0

def bern_hi (x:ℝ) :ℝ :=
 (849523188772202062952127582590706450849117609037139000351019273/1455191522836685180664062500000000000000000000000000000000000000:ℝ)*x^0*(1-x)^19 +
 (93179306357846201343445973374906275904817545892951388839542101/7275957614183425903320312500000000000000000000000000000000000:ℝ)*x^1*(1-x)^18 +
 (18974602329449808545744283216823565346085275621762543853178403/145519152283668518066406250000000000000000000000000000000000:ℝ)*x^2*(1-x)^17 +
 (822165382959604220103480910444756120428984820375372799568597/1000444171950221061706542968750000000000000000000000000000:ℝ)*x^3*(1-x)^16 +
 (310839707059004093165581312310472350330992935722408242942327377/86278305388987064361572265625000000000000000000000000000000:ℝ)*x^4*(1-x)^15 +
 (5044142694946429551001220955882851233800847971499479484212663/431391526944935321807861328125000000000000000000000000000:ℝ)*x^5*(1-x)^14 +
 (251668014204735969749054760546283303474370942339591664607899/8627830538898706436157226562500000000000000000000000000:ℝ)*x^6*(1-x)^13 +
 (1235634399554121908924030947860850986652889899126252252659/21569576347246766090393066406250000000000000000000000:ℝ)*x^7*(1-x)^12 +
 (77589953736219644144344335770737845793137550523323731459/862783053889870643615722656250000000000000000000000:ℝ)*x^8*(1-x)^11 +
 (44660548374712752221624841808257378586562188161986073/392174115404486656188964843750000000000000000000:ℝ)*x^9*(1-x)^10 +
 (916250005076041111106254606666895886986689057674891/7843482308089733123779296875000000000000000000:ℝ)*x^10*(1-x)^9 +
 (951585875820484883100134663640175605694076953623/9804352885112166404724121093750000000000000:ℝ)*x^11*(1-x)^8 +
 (51000683351293175464330418461775052425785022601/784348230808973312377929687500000000000000:ℝ)*x^12*(1-x)^7 +
 (136459634108357108721466303242775319311756947/3921741154044866561889648437500000000000:ℝ)*x^13*(1-x)^6 +
 (1148423078874808213210387852442026970758371/78434823080897331237792968750000000000:ℝ)*x^14*(1-x)^5 +
 (10196766646349518045449719053047121364523/2156957634724676609039306640625000000:ℝ)*x^15*(1-x)^4 +
 (12153537895134647265778113696039851901/10784788173623383045196533203125000:ℝ)*x^16*(1-x)^3 +
 (10034649455828992505480875647694257/53923940868116915225982666015625:ℝ)*x^17*(1-x)^2 +
 (5823221991208531503907222896876/308136804960668087005615234375:ℝ)*x^18*(1-x)^1 +
 (76044167690309330248836548352/86278305388987064361572265625:ℝ)*x^19*(1-x)^0

end Bernoulli.DeSilvaJerison.UpperAlgebra

namespace Bernoulli.DeSilvaJerison

/-- For τ=-2 the auxiliary Legendre solution is elementary and rational. -/
def gSup (t:ℝ) :ℝ := (1+t^2)/(1-t^2)^2
def gSup1 (t:ℝ) :ℝ := 2*t*(3+t^2)/(1-t^2)^3
def qSup (t:ℝ) :ℝ := 2*t*(3+t^2)/((1-t^2)*(1+t^2))
def qSup1 (t:ℝ) :ℝ := (6*t*qSup t+6)/(1-t^2)-(qSup t)^2
def GSup (t:ℝ) :ℝ := 9*(f t)^2+(1-t^2)*(fp t-f t*qSup t)^2

lemma gSup_pos {t:ℝ} (ht:|t|<1) :0<gSup t := by
  have hd:0<1-t^2 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  unfold gSup
  positivity

lemma hasDerivAt_gSup {t:ℝ} (ht:|t|<1) : HasDerivAt gSup (gSup1 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  convert! (((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2)).div
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2)
    (pow_ne_zero 2 hd)) using 1
  norm_num only [gSup1,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  field_simp [hd]
  ring

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

/-- The transverse unit-cylinder profile of the concrete upper barrier. -/
def capAmplitude : ℝ := -(10/17)*f (3/5)
def capRadius (s:ℝ) :ℝ := Real.sqrt (1+s^2)
def capAngle (s:ℝ) :ℝ := s/capRadius s
def capH (s:ℝ) :ℝ := capRadius s*f (capAngle s)+capAmplitude*(1+2*s^2)
def capHP (s:ℝ) :ℝ := capAngle s*f (capAngle s)+fp (capAngle s)/(capRadius s)^2+4*capAmplitude*s

def capP :ℝ := (3125/1024-13/2*capAmplitude)/(3125/1024-capAmplitude/8)
def capB :ℝ := (capP+3/50)/2

lemma capRadius_pos (s:ℝ) :0<capRadius s := Real.sqrt_pos.mpr (by positivity)
lemma capRadius_sq (s:ℝ) : (capRadius s)^2=1+s^2 := Real.sq_sqrt (by positivity)
lemma capAngle_mem (s:ℝ) : capAngle s∈Ioo (-1:ℝ) 1 := by
  have hr:=capRadius_pos s
  have hs:=capRadius_sq s
  constructor
  · rw [capAngle,lt_div_iff₀ hr]; nlinarith
  · rw [capAngle,div_lt_iff₀ hr]; nlinarith
lemma capAngle_d (s:ℝ) : 1-(capAngle s)^2=1/(capRadius s)^2 := by
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  nlinarith [capRadius_sq s]

lemma hasDerivAt_capRadius (s:ℝ) : HasDerivAt capRadius (s/capRadius s) s := by
  have hh:=(((hasDerivAt_const s (1:ℝ)).add ((hasDerivAt_id s).pow 2)).sqrt (by positivity : (1+s^2:ℝ)≠0))
  convert! hh using 1
  norm_num only [pow_one,id_eq]
  dsimp [capRadius]
  ring

lemma hasDerivAt_capAngle (s:ℝ) : HasDerivAt capAngle (1/(capRadius s)^3) s := by
  convert! (hasDerivAt_id s).div (hasDerivAt_capRadius s) (capRadius_pos s).ne' using 1
  simp only [id_eq,one_mul]
  field_simp [(capRadius_pos s).ne']
  nlinarith [capRadius_sq s]

lemma cap_f_relation (s:ℝ) : f (capAngle s)=capAngle s*fp (capAngle s)+(capRadius s)^6 := by
  have hh:=f_relation (capAngle_mem s)
  rw [capAngle_d] at hh
  have hr:capRadius s≠0:=(capRadius_pos s).ne'
  field_simp [hr] at hh
  linear_combination -hh

lemma hasDerivAt_capH (s:ℝ) : HasDerivAt capH (capHP s) s := by
  have hF:=(hasDerivAt_f (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hh:=((hasDerivAt_capRadius s).mul hF).add
    (((hasDerivAt_const s (1:ℝ)).add (((hasDerivAt_id s).pow 2).const_mul 2)).const_mul capAmplitude)
  convert! hh using 1
  simp only [Function.comp_apply,id_eq,capHP,capAngle]
  field_simp [(capRadius_pos s).ne']
  ring

lemma hasDerivAt_capHP (s:ℝ) : HasDerivAt capHP (-5*(capRadius s)^3+4*capAmplitude) s := by
  have hF:=(hasDerivAt_f (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hFP:=(hasDerivAt_fp (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hh:=(((hasDerivAt_capAngle s).mul hF).add
    (hFP.div ((hasDerivAt_capRadius s).pow 2) (pow_ne_zero 2 (capRadius_pos s).ne'))).add
      ((hasDerivAt_id s).const_mul (4*capAmplitude))
  convert! hh using 1
  simp only [Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,capAngle_d,cap_f_relation]
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  ring

lemma capH_even (s:ℝ) : capH (-s)=capH s := by
  simp only [capH,capRadius,neg_sq,capAngle,neg_div,f_neg]
lemma capHP_odd (s:ℝ) : capHP (-s)= -capHP s := by
  simp only [capHP,capRadius,neg_sq,capAngle,neg_div,f_neg,fp,A_neg]
  simp only [neg_div,neg_mul,mul_neg,neg_neg]
  ring
lemma capHP_zero : capHP 0=0 := by norm_num [capHP,capRadius,capAngle,fp_zero]
lemma capRadius_end : capRadius (3/4)=5/4 := by
  apply (sq_eq_sq₀ (capRadius_pos _).le (by norm_num)).mp
  rw [capRadius_sq]
  norm_num
lemma capAngle_end : capAngle (3/4)=3/5 := by rw [capAngle,capRadius_end]; norm_num
lemma capH_end : capH (3/4)=0 := by
  rw [capH,capRadius_end,capAngle_end,capAmplitude]
  ring

lemma capAmplitude_bounds : 289237/1000000≤capAmplitude ∧ capAmplitude≤289241/1000000 := by
  have hA: (3/5:ℝ)*B 12 ((3/5:ℝ)^2)≤A (3/5) ∧
      A (3/5)≤(3/5:ℝ)*(B 12 ((3/5:ℝ)^2)+((3/5:ℝ)^2)^12/(1-(3/5:ℝ)^2)) :=
    A_series_bounds 12 (by norm_num) (by norm_num)
  dsimp [capAmplitude,f]
  norm_num [B,Finset.sum_range_succ] at hA ⊢
  constructor <;> linarith [hA.1,hA.2]
lemma capAmplitude_pos : 0<capAmplitude := by linarith [capAmplitude_bounds.1]
lemma capAmplitude_le : capAmplitude≤29/100 := by linarith [capAmplitude_bounds.2]

lemma capB_bounds : 2242/10000≤capB ∧ capB≤2243/10000 := by
  have hd:0<3125/1024-capAmplitude/8:=by linarith [capAmplitude_bounds.2]
  unfold capB capP
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (sub_le_iff_le_add).mp
    apply (le_div_iff₀ hd).mpr
    linarith [capAmplitude_bounds.2]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_sub_iff_add_le).mp
    apply (div_le_iff₀ hd).mpr
    linarith [capAmplitude_bounds.1]

end Bernoulli.DeSilvaJerison

noncomputable section
namespace Bernoulli.DeSilvaJerison.CapSign
def flo (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))
def polyK (u:ℝ) :ℝ := (431/200-673/250)*flo u/8+673/250-5*(1-u)+
  29/100*(1-u)*(4*(1-u)-4*(673/250)*u+431/200*(1+u))
def bern (x:ℝ) :ℝ :=
 (21201/20000:ℝ)*x^0*(1-x)^8 +
 (4795737/625000:ℝ)*x^1*(1-x)^7 +
 (1494048963/62500000:ℝ)*x^2*(1-x)^6 +
 (1300927593/31250000:ℝ)*x^3*(1-x)^5 +
 (480518798097/10937500000:ℝ)*x^4*(1-x)^4 +
 (1936812554529/68359375000:ℝ)*x^5*(1-x)^3 +
 (159112309786509/15039062500000:ℝ)*x^6*(1-x)^2 +
 (22814203319679/11749267578125:ℝ)*x^7*(1-x)^1 +
 (187538043427107/1879882812500000:ℝ)*x^8*(1-x)^0
end Bernoulli.DeSilvaJerison.CapSign

namespace Bernoulli.DeSilvaJerison

lemma capRadius_one_le (s:ℝ) :1≤capRadius s := by
  have hp:=capRadius_pos s
  nlinarith [capRadius_sq s,sq_nonneg s]

lemma capHP_antitone : Antitone capHP := by
  apply antitone_of_deriv_nonpos (fun s=>(hasDerivAt_capHP s).differentiableAt)
  intro s
  rw [(hasDerivAt_capHP s).deriv]
  have hh:1≤(capRadius s)^3:=one_le_pow₀ (capRadius_one_le s)
  linarith [capAmplitude_le]

lemma capHP_nonpos {s:ℝ} (hs:0≤ s) :capHP s≤0 := by
  have hh:=capHP_antitone hs
  simpa only [capHP_zero] using hh

lemma capHP_le_linear {s:ℝ} (hs:0≤ s) : capHP s≤(-5+4*capAmplitude)*s := by
  let g:ℝ→ℝ:=fun t=>capHP t-(-5+4*capAmplitude)*t
  have hD (t:ℝ) :HasDerivAt g (-5*(capRadius t)^3+5) t := by
    convert! (hasDerivAt_capHP t).sub ((hasDerivAt_id t).const_mul (-5+4*capAmplitude)) using 1
    ring
  have hM:Antitone g := by
    apply antitone_of_deriv_nonpos (fun t=>(hD t).differentiableAt)
    intro t
    rw [(hD t).deriv]
    have hh:1≤(capRadius t)^3:=one_le_pow₀ (capRadius_one_le t)
    linarith
  have hh:=hM hs
  dsimp [g] at hh
  rw [capHP_zero] at hh
  linarith

lemma capH_antitone : AntitoneOn capH (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ))
  · exact fun s _=>(hasDerivAt_capH s).continuousAt.continuousWithinAt
  · exact fun s _=>(hasDerivAt_capH s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_capH s).deriv]
    exact capHP_nonpos (interior_subset hs)

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

def capEta : ℝ := capP - (9/16)*capP*(capP-3/25)/(1+(9/16)*capP^2)
def capW (s : ℝ) : ℝ := (1-capEta)*capH s+(capP-1)*s*capHP s-3*capAmplitude*(1+2*s^2)
def capWP (s : ℝ) : ℝ := (capP-capEta)*capHP s+(capP-1)*s*(-5*(capRadius s)^3+4*capAmplitude)-12*capAmplitude*s
def capWPP (s : ℝ) : ℝ := (2*capP-capEta-1)*(-5*(capRadius s)^3+4*capAmplitude)+(capP-1)*(-15*s^2*capRadius s)-12*capAmplitude

def capZ (q : ℝ) : ℝ := capW (Real.sqrt q)
def capZP (q : ℝ) : ℝ := capWP (Real.sqrt q)/(2*Real.sqrt q)

end Bernoulli.DeSilvaJerison
noncomputable section
namespace Bernoulli.DeSilvaJerison.CapAlgebra

def V (u b:ℝ) :ℝ := 203/200-b+b*u-3/200*u^2
def D (u b:ℝ) :ℝ := 2*b-3/50*u
def E (u b:ℝ) :ℝ := 2*b-9/50*u
def H (u b:ℝ) :ℝ := 1+9/16*u*(D u b)^2
def MN (u b:ℝ) :ℝ := E u b*(1-9/16*u*(D u b)^2)+5*D u b*H u b
def NN (u b:ℝ) :ℝ := MN u b*H u b-
  9/16*V u b*((E u b)^2-9/25*u*D u b+5*D u b*E u b)*H u b+
  3*(9/16)^2*V u b*u*(D u b)^2*(E u b)^2
def Mlo_0 (z:ℝ) :ℝ :=
 (3363/1250:ℝ)*z^0*(1-z)^3 +
 (20181/2500:ℝ)*z^1*(1-z)^2 +
 (5046/625:ℝ)*z^2*(1-z)^1 +
 (6729/2500:ℝ)*z^3*(1-z)^0
def Mlo_1 (z:ℝ) :ℝ :=
 (655278251049/250000000000:ℝ)*z^0*(1-z)^3 +
 (3932303435601/500000000000:ℝ)*z^1*(1-z)^2 +
 (7865874760083/1000000000000:ℝ)*z^2*(1-z)^1 +
 (5244761786163/2000000000000:ℝ)*z^3*(1-z)^0
def Mlo_2 (z:ℝ) :ℝ :=
 (79391132481/31250000000:ℝ)*z^0*(1-z)^3 +
 (1905718586601/250000000000:ℝ)*z^1*(1-z)^2 +
 (1906050008229/250000000000:ℝ)*z^2*(1-z)^1 +
 (2541841925913/1000000000000:ℝ)*z^3*(1-z)^0
def Mlo_3 (z:ℝ) :ℝ :=
 (612606431397/250000000000:ℝ)*z^0*(1-z)^3 +
 (3676325647803/500000000000:ℝ)*z^1*(1-z)^2 +
 (7354025498499/1000000000000:ℝ)*z^2*(1-z)^1 +
 (4903599856989/2000000000000:ℝ)*z^3*(1-z)^0
def Mlo_4 (z:ℝ) :ℝ :=
 (73512952587/31250000000:ℝ)*z^0*(1-z)^3 +
 (882332198601/125000000000:ℝ)*z^1*(1-z)^2 +
 (220627244901/31250000000:ℝ)*z^2*(1-z)^1 +
 (1176914365413/500000000000:ℝ)*z^3*(1-z)^0
def bern_Mlo (u z:ℝ) :ℝ :=
 1*Mlo_0 z*u^0*(1-u)^4 +
 4*Mlo_1 z*u^1*(1-u)^3 +
 6*Mlo_2 z*u^2*(1-u)^2 +
 4*Mlo_3 z*u^3*(1-u)^1 +
 1*Mlo_4 z*u^4*(1-u)^0
def Mhi_0 (z:ℝ) :ℝ :=
 (1/625:ℝ)*z^0*(1-z)^3 +
 (9/2500:ℝ)*z^1*(1-z)^2 +
 (3/1250:ℝ)*z^2*(1-z)^1 +
 (1/2500:ℝ)*z^3*(1-z)^0
def Mhi_1 (z:ℝ) :ℝ :=
 (73500870587/500000000000:ℝ)*z^0*(1-z)^3 +
 (219902631939/500000000000:ℝ)*z^1*(1-z)^2 +
 (877210578219/2000000000000:ℝ)*z^2*(1-z)^1 +
 (145801766401/1000000000000:ℝ)*z^3*(1-z)^0
def Mhi_2 (z:ℝ) :ℝ :=
 (72533364337/250000000000:ℝ)*z^0*(1-z)^3 +
 (217301121189/250000000000:ℝ)*z^1*(1-z)^2 +
 (868008569469/1000000000000:ℝ)*z^2*(1-z)^1 +
 (72234385513/250000000000:ℝ)*z^3*(1-z)^0
def Mhi_3 (z:ℝ) :ℝ :=
 (215270976761/500000000000:ℝ)*z^0*(1-z)^3 +
 (645218633817/500000000000:ℝ)*z^1*(1-z)^2 +
 (2578497272157/2000000000000:ℝ)*z^2*(1-z)^1 +
 (429353321953/1000000000000:ℝ)*z^3*(1-z)^0
def Mhi_4 (z:ℝ) :ℝ :=
 (71002129337/125000000000:ℝ)*z^0*(1-z)^3 +
 (212859027189/125000000000:ℝ)*z^1*(1-z)^2 +
 (850846641969/500000000000:ℝ)*z^2*(1-z)^1 +
 (35427381319/62500000000:ℝ)*z^3*(1-z)^0
def bern_Mhi (u z:ℝ) :ℝ :=
 1*Mhi_0 z*u^0*(1-u)^4 +
 4*Mhi_1 z*u^1*(1-u)^3 +
 6*Mhi_2 z*u^2*(1-u)^2 +
 4*Mhi_3 z*u^3*(1-u)^1 +
 1*Mhi_4 z*u^4*(1-u)^0
def Nlo_0 (z:ℝ) :ℝ :=
 (269221760061/125000000000:ℝ)*z^0*(1-z)^5 +
 (5384829779091/500000000000:ℝ)*z^1*(1-z)^4 +
 (2692612172703/125000000000:ℝ)*z^2*(1-z)^3 +
 (43084951201347/2000000000000:ℝ)*z^3*(1-z)^2 +
 (10772026886763/1000000000000:ℝ)*z^4*(1-z)^1 +
 (4309126380039/2000000000000:ℝ)*z^5*(1-z)^0
def Nlo_1 (z:ℝ) :ℝ :=
 (382600657861063335909/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1530524055108837852339/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (382661369286668105259/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (6123067590235820584581/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (6123553265387536509219/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (24496155736186519478199/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_2 (z:ℝ) :ℝ :=
 (775057445541430053771/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1550247224503752406083/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (3100759115968495184859/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (6202047566103361871307/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (12405153801040206854811/1120000000000000000000:ℝ)*z^4*(1-z)^1 +
 (24812424940772777719203/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_3 (z:ℝ) :ℝ :=
 (48958478704618351989/21875000000000000000:ℝ)*z^0*(1-z)^5 +
 (783407241197278452747/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (391739412012590216571/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (447743090147723034423/20000000000000000000:ℝ)*z^3*(1-z)^2 +
 (783621992398198851/70000000000000000:ℝ)*z^4*(1-z)^1 +
 (12539097247122349634271/5600000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_4 (z:ℝ) :ℝ :=
 (394997188657314790971/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (790071314230783404417/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (1580296505902245781203/70000000000000000000:ℝ)*z^2*(1-z)^3 +
 (632180154781400295717/28000000000000000000:ℝ)*z^3*(1-z)^2 +
 (6322417086470145808443/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (12646065279172462395873/5600000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_5 (z:ℝ) :ℝ :=
 (79500176095315489509/35000000000000000000:ℝ)*z^0*(1-z)^5 +
 (318033589904376947673/28000000000000000000:ℝ)*z^1*(1-z)^4 +
 (79516619129149257177/3500000000000000000:ℝ)*z^2*(1-z)^3 +
 (1272397456873777666359/56000000000000000000:ℝ)*z^3*(1-z)^2 +
 (254505802408353089607/22400000000000000000:ℝ)*z^4*(1-z)^1 +
 (5090642286289762414869/2240000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_6 (z:ℝ) :ℝ :=
 (798333880165936252233/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1596842554436556680349/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (3194034711701294217297/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (6388768658308765709541/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (1825562263564842891039/160000000000000000000:ℝ)*z^4*(1-z)^1 +
 (25560668863677337021869/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nlo_7 (z:ℝ) :ℝ :=
 (14285237132421382131/6250000000000000000:ℝ)*z^0*(1-z)^5 +
 (28573776877165480983/2500000000000000000:ℝ)*z^1*(1-z)^4 +
 (57154159307184777219/2500000000000000000:ℝ)*z^2*(1-z)^3 +
 (114321530376744764967/5000000000000000000:ℝ)*z^3*(1-z)^2 +
 (228669485592076793331/20000000000000000000:ℝ)*z^4*(1-z)^1 +
 (457391823490005261783/200000000000000000000:ℝ)*z^5*(1-z)^0
def bern_Nlo (u z:ℝ) :ℝ :=
 1*Nlo_0 z*u^0*(1-u)^7 +
 7*Nlo_1 z*u^1*(1-u)^6 +
 21*Nlo_2 z*u^2*(1-u)^5 +
 35*Nlo_3 z*u^3*(1-u)^4 +
 35*Nlo_4 z*u^4*(1-u)^3 +
 21*Nlo_5 z*u^5*(1-u)^2 +
 7*Nlo_6 z*u^6*(1-u)^1 +
 1*Nlo_7 z*u^7*(1-u)^0
def Nhi_0 (z:ℝ) :ℝ :=
 (153239939/125000000000:ℝ)*z^0*(1-z)^5 +
 (2670220909/500000000000:ℝ)*z^1*(1-z)^4 +
 (1137827297/125000000000:ℝ)*z^2*(1-z)^3 +
 (15048798653/2000000000000:ℝ)*z^3*(1-z)^2 +
 (2973113237/1000000000000:ℝ)*z^4*(1-z)^1 +
 (873619961/2000000000000:ℝ)*z^5*(1-z)^0
def Nhi_1 (z:ℝ) :ℝ :=
 (6710618236436664091/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (26729745999162147661/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (950607916038484963/2500000000000000000:ℝ)*z^2*(1-z)^3 +
 (106017199577179415419/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (105566322934463490781/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (420461826653480521801/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_2 (z:ℝ) :ℝ :=
 (13111446287006550577/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (52330785122706030907/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (26107893543479728289/35000000000000000000:ℝ)*z^2*(1-z)^3 +
 (208403164157297163073/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (207943187913353315467/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (829932878440629602647/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_3 (z:ℝ) :ℝ :=
 (38827439179978619951/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (19384386394708716919/35000000000000000000:ℝ)*z^1*(1-z)^4 +
 (154840428418693554377/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (154605768499513427459/140000000000000000000:ℝ)*z^3*(1-z)^2 +
 (123496889117325415927/224000000000000000000:ℝ)*z^4*(1-z)^1 +
 (77068228553325460813/700000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_4 (z:ℝ) :ℝ :=
 (800715769361209697/5468750000000000000:ℝ)*z^0*(1-z)^5 +
 (51185932986797940953/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (25563028582094833723/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (40852945416226297891/28000000000000000000:ℝ)*z^3*(1-z)^2 +
 (51006306804067794449/70000000000000000000:ℝ)*z^4*(1-z)^1 +
 (815142916232554221677/5600000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_5 (z:ℝ) :ℝ :=
 (1587610118570041229/8750000000000000000:ℝ)*z^0*(1-z)^5 +
 (3625329355203510101/4000000000000000000:ℝ)*z^1*(1-z)^4 +
 (25352849141682898457/14000000000000000000:ℝ)*z^2*(1-z)^3 +
 (101313571449733664801/56000000000000000000:ℝ)*z^3*(1-z)^2 +
 (10121574659285550611/11200000000000000000:ℝ)*z^4*(1-z)^1 +
 (404471687976992180831/2240000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_6 (z:ℝ) :ℝ :=
 (37821484030869718321/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (151160996163694918501/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (10788289715972042801/5000000000000000000:ℝ)*z^2*(1-z)^3 +
 (603644462802436405159/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (603144700768341858451/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (2410579751926825325881/11200000000000000000000:ℝ)*z^5*(1-z)^0
def Nhi_7 (z:ℝ) :ℝ :=
 (12530356731138217727/50000000000000000000:ℝ)*z^0*(1-z)^5 +
 (12521232400567437053/10000000000000000000:ℝ)*z^1*(1-z)^4 +
 (50048432087552403293/20000000000000000000:ℝ)*z^2*(1-z)^3 +
 (12502983594891765863/5000000000000000000:ℝ)*z^3*(1-z)^2 +
 (199901745909919602587/160000000000000000000:ℝ)*z^4*(1-z)^1 +
 (199755753521828125643/800000000000000000000:ℝ)*z^5*(1-z)^0
def bern_Nhi (u z:ℝ) :ℝ :=
 1*Nhi_0 z*u^0*(1-u)^7 +
 7*Nhi_1 z*u^1*(1-u)^6 +
 21*Nhi_2 z*u^2*(1-u)^5 +
 35*Nhi_3 z*u^3*(1-u)^4 +
 35*Nhi_4 z*u^4*(1-u)^3 +
 21*Nhi_5 z*u^5*(1-u)^2 +
 7*Nhi_6 z*u^6*(1-u)^1 +
 1*Nhi_7 z*u^7*(1-u)^0

lemma H_pos {u b:ℝ} (hu:0≤u) : 0<H u b := by unfold H; positivity
end Bernoulli.DeSilvaJerison.CapAlgebra

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
namespace CapAlgebra
lemma V_bounds {q b:ℝ} (hq:0≤q) (hq1:q≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0<V q b ∧ V q b≤1 := by
  have hqq : q^2≤q := by nlinarith
  have he : V q b=1-(1-q)*(b-3/200*(q+1)) := by unfold V; ring
  have hl : 0≤b*q := mul_nonneg (by linarith) hq
  constructor
  · unfold V
    nlinarith
  · rw [he]
    have hh : 0≤(1-q)*(b-3/200*(q+1)) := mul_nonneg (by linarith) (by linarith)
    linarith
lemma hasDerivAt_V (q b:ℝ) : HasDerivAt (fun q=>V q b) (D q b/2) q := by
  convert! (((hasDerivAt_const q (203/200-b)).add ((hasDerivAt_id q).const_mul b)).sub
    (((hasDerivAt_id q).pow 2).const_mul (3/200))) using 1
  dsimp [V,D]
  ring
lemma hasDerivAt_D (q b:ℝ) : HasDerivAt (fun q=>D q b) (-3/50) q := by
  convert! (hasDerivAt_const q (2*b)).sub ((hasDerivAt_id q).const_mul (3/50)) using 1
  ring
lemma hasDerivAt_H (q b:ℝ) : HasDerivAt (fun q=>H q b) (9/16*D q b*E q b) q := by
  convert! (hasDerivAt_const q (1:ℝ)).add
    ((((hasDerivAt_id q).const_mul (9/16)).mul ((hasDerivAt_D q b).pow 2))) using 1
  dsimp [D,E]
  ring
lemma V_contDiff (b:ℝ) {n:WithTop ℕ∞} : ContDiff ℝ n (fun q=>V q b) := by
  exact (contDiff_const.add (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul (contDiff_id.pow 2))
lemma H_contDiff (b:ℝ) {n:WithTop ℕ∞} : ContDiff ℝ n (fun q=>H q b) := by
  exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul
    ((contDiff_const.sub (contDiff_const.mul contDiff_id)).pow 2))
/-- The cap prefactor in squared transverse coordinates. -/
def Y (q b C:ℝ) :ℝ := C*V q b/Real.sqrt (H q b)
def Y1 (q b C:ℝ) :ℝ :=
  C*(D q b/2/Real.sqrt (H q b)-V q b*(9/16*D q b*E q b)/(2*(Real.sqrt (H q b))^3))
def Y2 (q b C:ℝ) :ℝ :=
  C*((-3/100)/Real.sqrt (H q b)-D q b/2*(9/16*D q b*E q b)/(Real.sqrt (H q b))^3-
    V q b*(9/16*((-3/50)*E q b+D q b*(-9/50)))/(2*(Real.sqrt (H q b))^3)+
    3*V q b*(9/16*D q b*E q b)^2/(4*(Real.sqrt (H q b))^5))
lemma Y_contDiffAt {q b C:ℝ} (hH:0<H q b) {n:WithTop ℕ∞} : ContDiffAt ℝ n (fun q=>Y q b C) q :=
  (contDiffAt_const.mul (V_contDiff b (n:=n)).contDiffAt).div ((H_contDiff b (n:=n)).contDiffAt.sqrt hH.ne')
    (Real.sqrt_pos.mpr hH).ne'
lemma hasDerivAt_Y {q b C:ℝ} (hH:0<H q b) : HasDerivAt (fun q=>Y q b C) (Y1 q b C) q := by
  have hS:=Real.sqrt_pos.mpr hH
  have hSsq:=Real.sq_sqrt hH.le
  convert! ((hasDerivAt_V q b).const_mul C).div ((hasDerivAt_H q b).sqrt hH.ne') hS.ne' using 1
  simp only [Y1]
  field_simp
lemma deriv_Y {q b C:ℝ} (hH:0<H q b) : deriv (fun q=>Y q b C) q=Y1 q b C := (hasDerivAt_Y hH).deriv
lemma hasDerivAt_invV {q b:ℝ} (hv:V q b≠0) :
    HasDerivAt (fun q=>(V q b)⁻¹) (-D q b/(2*(V q b)^2)) q := by
  convert! (hasDerivAt_V q b).inv hv using 1
  ring

end CapAlgebra

lemma capH_contDiff : ContDiff ℝ ∞ capH := by
  have hr : ContDiff ℝ ∞ capRadius := by
    apply ContDiff.sqrt
    · exact contDiff_const.add (contDiff_id.pow 2)
    · intro x; positivity
  have ht : ContDiff ℝ ∞ capAngle := contDiff_id.div hr (fun x=>(capRadius_pos x).ne')
  have hf : ContDiff ℝ ∞ (fun s=>f (capAngle s)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    exact (contDiffAt_f (capAngle_mem s)).comp s ht.contDiffAt
  exact (hr.mul hf).add (contDiff_const.mul (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))))

def capC :ℝ := Real.sqrt (1+9/16*capP^2)
def smoothCap (x:Space 7) :ℝ := Cylindrical.lift axis (fun q=>CapAlgebra.Y q capB capC)
  (fun q=>(CapAlgebra.V q capB)⁻¹) capH x

lemma smoothCap_contDiffAt {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    ContDiffAt ℝ ∞ smoothCap x := by
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv := (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  exact Cylindrical.contDiffAt_lift (CapAlgebra.Y_contDiffAt (CapAlgebra.H_pos hq))
    ((CapAlgebra.V_contDiff capB).contDiffAt.inv hv.ne') capH_contDiff.contDiffAt

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capH_abs (s:ℝ) : capH |s|=capH s := by
  rcases le_total 0 s with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,capH_even]
lemma capC_pos : 0<capC := by unfold capC; positivity
lemma capC_sq : capC^2=1+9/16*capP^2 := Real.sq_sqrt (by positivity)

lemma gradient_smoothCap {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q := Cylindrical.radiusSq axis x
    let V := CapAlgebra.V q capB
    let s := Cylindrical.axis axis x/V
    gradient smoothCap x =
      (2*CapAlgebra.Y1 q capB capC*capH s) • Cylindrical.transverse axis x +
      (CapAlgebra.Y q capB capC*capHP s) •
        (V⁻¹ • axis+(-Cylindrical.axis axis x*CapAlgebra.D q capB/V^2) • Cylindrical.transverse axis x) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hh:0<CapAlgebra.H q capB:=CapAlgebra.H_pos (b:=capB) hq
  have hv:0<CapAlgebra.V q capB:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hg:=Cylindrical.gradient_lift (e:=axis) (x:=x)
    (CapAlgebra.Y_contDiffAt (C:=capC) (n:=1) hh |>.differentiableAt (by norm_num))
    (CapAlgebra.hasDerivAt_invV hv.ne').differentiableAt
    (hasDerivAt_capH _).differentiableAt
  change gradient smoothCap x= _ at hg
  change gradient smoothCap x=
    (2*deriv (fun q=>CapAlgebra.Y q capB capC) q*capH (a*(CapAlgebra.V q capB)⁻¹)) • Cylindrical.transverse axis x+
    (CapAlgebra.Y q capB capC*deriv capH (a*(CapAlgebra.V q capB)⁻¹)) •
      ((CapAlgebra.V q capB)⁻¹ • axis+(2*a*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q) • Cylindrical.transverse axis x) at hg
  rw [hg]
  simp only [CapAlgebra.deriv_Y hh,(CapAlgebra.hasDerivAt_invV hv.ne').deriv,
    (hasDerivAt_capH _).deriv,←div_eq_mul_inv]
  have he:2*a*(-CapAlgebra.D q capB/(2*CapAlgebra.V q capB^2)) = -a*CapAlgebra.D q capB/CapAlgebra.V q capB^2 := by ring
  rw [he]

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capHP_mul_nonpos (s:ℝ) : s*capHP s≤0 := by
  rcases le_total 0 s with h|h
  · exact mul_nonpos_of_nonneg_of_nonpos h (capHP_nonpos h)
  · have hh:=capHP_nonpos (s:= -s) (by linarith)
    rw [capHP_odd] at hh
    exact mul_nonpos_of_nonpos_of_nonneg h (by linarith)

lemma capHP_neg {s:ℝ} (hs:0<s) : capHP s<0 := by
  have hh:=capHP_le_linear hs.le
  have hn: -5+4*capAmplitude<0 := by linarith [capAmplitude_le]
  exact hh.trans_lt (mul_neg_of_neg_of_pos hn hs)

lemma capH_strictAnti : StrictAntiOn capH (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_capH x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_capH x).deriv]
    exact capHP_neg hx

lemma capH_pos_iff (s:ℝ) : 0<capH s ↔ |s|<3/4 := by
  rw [←capH_abs]
  constructor
  · intro hh
    by_contra hn
    have hh1:=capH_antitone (show (3/4:ℝ)∈Ici 0 by norm_num)
      (abs_nonneg s) (le_of_not_gt hn)
    rw [capH_end] at hh1
    linarith
  · intro hs
    have hh:=capH_strictAnti (abs_nonneg s) (show (3/4:ℝ)∈Ici 0 by norm_num) hs
    rwa [capH_end] at hh

namespace CapAlgebra
lemma V_radial_pos {q b:ℝ} (_hq:0≤q) (hq1:q≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0<V q b-q*D q b := by
  have hmul:q*b≤b:=mul_le_of_le_one_left (by linarith) hq1
  unfold V D
  nlinarith [sq_nonneg q]
lemma D_pos {q b:ℝ} (hq1:q≤1) (hb:2242/10000≤b) :0<D q b := by
  unfold D; linarith
lemma E_pos {q b:ℝ} (hq1:q≤1) (hb:2242/10000≤b) :0<E q b := by
  unfold E; linarith
lemma Y_pos {q b C:ℝ} (hq:0≤q) (hv:0<V q b) (hc:0<C) :0<Y q b C := by
  unfold Y; exact div_pos (mul_pos hc hv) (Real.sqrt_pos.mpr (H_pos hq))
lemma Y1_eq {q b C:ℝ} (hh:0<H q b) (hv:V q b≠0) :
    2*Y1 q b C=Y q b C*(D q b/V q b-9/16*D q b*E q b/H q b) := by
  have hs:Real.sqrt (H q b)≠0:=(Real.sqrt_pos.mpr hh).ne'
  have hs2:=Real.sq_sqrt hh.le
  unfold Y1 Y
  generalize V q b=v at *
  generalize D q b=d at *
  generalize E q b=e at *
  generalize H q b=h at *
  field_simp
  rw [hs2]
  ring
end CapAlgebra

lemma smoothCap_radial_defect {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q:=Cylindrical.radiusSq axis x
    let V:=CapAlgebra.V q capB
    let H:=CapAlgebra.H q capB
    let D:=CapAlgebra.D q capB
    let E:=CapAlgebra.E q capB
    let s:=Cylindrical.axis axis x/V
    smoothCap x-inner ℝ x (gradient smoothCap x)=
      CapAlgebra.Y q capB capC*((1-q*D/V+q*9/16*D*E/H)*capH s-
        s*capHP s*(1-q*D/V)) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<CapAlgebra.V q capB:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<CapAlgebra.H q capB:=CapAlgebra.H_pos hq
  have ht:inner ℝ x (Cylindrical.transverse axis x)=q := by
    simp only [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    change ‖x‖^2-a*a=‖x‖^2-a^2
    ring
  rw [gradient_smoothCap hx]
  simp only [inner_add_right,real_inner_smul_right,ht]
  change smoothCap x-(2*CapAlgebra.Y1 q capB capC*capH (a/CapAlgebra.V q capB)*q+
    CapAlgebra.Y q capB capC*capHP (a/CapAlgebra.V q capB)*
      ((CapAlgebra.V q capB)⁻¹*a+(-a*CapAlgebra.D q capB/(CapAlgebra.V q capB)^2)*q))=_
  rw [CapAlgebra.Y1_eq hh hv.ne']
  change CapAlgebra.Y q capB capC*capH (a*(CapAlgebra.V q capB)⁻¹)-_=_
  dsimp only [q,a] at *
  simp only [div_eq_mul_inv]
  field_simp
  ring

lemma smoothCap_radial_defect_pos {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hp:0<smoothCap x) : 0<smoothCap x-inner ℝ x (gradient smoothCap x) := by
  let q:=Cylindrical.radiusSq axis x
  let V:=CapAlgebra.V q capB
  let H:=CapAlgebra.H q capB
  let D:=CapAlgebra.D q capB
  let E:=CapAlgebra.E q capB
  let s:=Cylindrical.axis axis x/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<V:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<H:=CapAlgebra.H_pos hq
  have hd:0<D:=CapAlgebra.D_pos hx capB_bounds.1
  have he:0<E:=CapAlgebra.E_pos hx capB_bounds.1
  have hy:0<CapAlgebra.Y q capB capC:=CapAlgebra.Y_pos hq hv capC_pos
  have hhpos:0<capH s := by
    change 0<CapAlgebra.Y q capB capC*capH (Cylindrical.axis axis x*V⁻¹) at hp
    rw [←div_eq_mul_inv] at hp
    exact pos_of_mul_pos_right hp hy.le
  have hk:0<1-q*D/V := by
    have hl:=CapAlgebra.V_radial_pos hq hx capB_bounds.1 capB_bounds.2
    apply sub_pos.mpr
    apply (div_lt_iff₀ hv).mpr
    simpa only [one_mul] using (show q*D<V by linarith)
  have hk1:0≤q*9/16*D*E/H:=by positivity
  have hsprod:=capHP_mul_nonpos s
  rw [smoothCap_radial_defect hx]
  change 0<CapAlgebra.Y q capB capC*((1-q*D/V+q*9/16*D*E/H)*capH s-s*capHP s*(1-q*D/V))
  have ht:=mul_pos (show 0<1-q*D/V+q*9/16*D*E/H by linarith) hhpos
  have ht1:=mul_nonpos_of_nonpos_of_nonneg hsprod hk.le
  exact mul_pos hy (by linarith)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.OuterGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric

def gSup2 (t:ℝ) :ℝ := (6+36*t^2+6*t^4)/(1-t^2)^4
lemma gSup_contDiffAt {t:ℝ} {n:WithTop ℕ∞} (ht:|t|<1) : ContDiffAt ℝ n gSup t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  exact (contDiffAt_const.add (contDiffAt_id.pow 2)).div
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).pow 2) (pow_ne_zero 2 hd)

def KSup : Space 7→ℝ := lift axis (-2) gSup
def outerSigned (x:Space 7) :ℝ := Zsigned x+capAmplitude*KSup x

lemma KSup_pos {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :0<KSup x := by
  unfold KSup lift
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)
  exact gSup_pos (by simpa [inner_axis,angle] using ha)
lemma KSup_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) (ha:|angle x|<1) :ContDiffAt ℝ n KSup x := by
  exact contDiffAt_lift hx (gSup_contDiffAt (by simpa [inner_axis,angle] using ha))
lemma KSup_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient KSup x=(‖x‖^(-2:ℝ)/‖x‖) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x)) := by
  have hi:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
  simpa only [KSup,inner_axis,angle] using (hasGradientAt_lift axis x (-2) hx (hasDerivAt_gSup hi)).gradient
lemma outerSigned_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) (ha:|angle x|<1) :
    ContDiffAt ℝ n outerSigned x := (signed_contDiffAt hx ha).add
      (contDiffAt_const.mul (KSup_contDiffAt hx ha))

lemma polarGradient_inner_radial (x:Space 7) (hx:x≠0) (a b:ℝ) :
    inner ℝ x (polarGradient axis x a b)=‖x‖*a := by
  have hn:‖x‖≠0:=norm_ne_zero_iff.mpr hx
  simp only [polarGradient,inner_add_right,inner_sub_right,real_inner_smul_right,
    radial,real_inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp
  ring
lemma gradient_add' {d:ℕ} {f g:Space d→ℝ} {x:Space d}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    gradient (fun x=>f x+g x) x=gradient f x+gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,inner_gradient_left,inner_gradient_left,inner_gradient_left]
  change (fderiv ℝ (f+g) x) v=_
  rw [fderiv_add hf hg]
  rfl
lemma outerSigned_radial_defect {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    outerSigned x-inner ℝ x (gradient outerSigned x)=3*capAmplitude*KSup x := by
  have hdz: DifferentiableAt ℝ Zsigned x := (signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk: DifferentiableAt ℝ KSup x := (KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hg:gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
    have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by simpa only [inner_axis,angle] using (show angle x∈Ioo (-1:ℝ) 1 from abs_lt.mp ha)
    rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
    simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
  change Zsigned x+capAmplitude*KSup x-inner ℝ x (gradient (fun x=>Zsigned x+capAmplitude*KSup x) x)=_
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,hg,KSup_gradient hx ha]
  simp only [inner_add_right,real_inner_smul_right,polarGradient_inner_radial x hx]
  rw [Zsigned_eq]
  unfold KSup lift
  simp only [inner_axis,angle]
  field_simp
  ring

lemma radiusSq_pos_data {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) : x≠0 ∧ |angle x|<1 := by
  have he:Cylindrical.radiusSq axis x=‖x‖^2-(x 6)^2 := by rw [Cylindrical.radiusSq,Cylindrical.axis,inner_axis]
  have hx:x≠0 := by intro hh; simp [hh,Cylindrical.radiusSq,Cylindrical.axis] at hq
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  refine ⟨hx,?_⟩
  rw [angle,abs_div,abs_norm,div_lt_iff₀ hn]
  rw [he] at hq
  nlinarith [sq_abs (x 6)]
lemma KSup_cylindrical {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    KSup x=(Cylindrical.radiusSq axis x+2*(Cylindrical.axis axis x)^2)/(Cylindrical.radiusSq axis x)^2 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hn:=norm_ne_zero_iff.mpr hx
  have hd:1-(inner ℝ x axis/‖x‖)^2≠0 := by
    have hh:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
    obtain ⟨h1,h2⟩:=abs_lt.mp hh; nlinarith
  unfold KSup lift gSup Cylindrical.radiusSq Cylindrical.axis
  rw [Real.rpow_neg (norm_nonneg x),show ‖x‖^(2:ℝ)=‖x‖^2 by norm_cast]
  have hqne:‖x‖^2-(inner ℝ x axis)^2≠0:=hq.ne'
  field_simp [hn,hd,hqne]
  ring
lemma outerSigned_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    outerSigned x=capH (Cylindrical.axis axis x) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  have hn:‖x‖=capRadius (Cylindrical.axis axis x) := by
    have he:‖x‖^2=1+(Cylindrical.axis axis x)^2 := by
      rw [Cylindrical.radiusSq] at hq; linarith
    apply (sq_eq_sq₀ (norm_nonneg x) (capRadius_pos _).le).mp
    rw [capRadius_sq,he]
  rw [outerSigned,KSup_cylindrical hqp,hq,Zsigned_eq]
  simp only [one_pow,div_one]
  rw [angle,←inner_axis,←Cylindrical.axis,hn]
  rfl
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

namespace CapAlgebra
lemma V_one (b:ℝ) : V 1 b=1 := by unfold V; ring
lemma D_one : D 1 capB=capP := by unfold D capB; ring
lemma H_one : H 1 capB=capC^2 := by rw [H,D_one,capC_sq]; ring
lemma Y_one : Y 1 capB capC=1 := by
  rw [Y,V_one,H_one,Real.sqrt_sq capC_pos.le,mul_one,div_self capC_pos.ne']
end CapAlgebra

lemma smoothCap_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    smoothCap x=capH (Cylindrical.axis axis x) := by
  simp only [smoothCap,Cylindrical.lift,hq,CapAlgebra.Y_one,CapAlgebra.V_one,inv_one,mul_one,one_mul]
lemma upper_seam_agreement {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    smoothCap x=outerSigned x := by rw [smoothCap_at_seam hq,outerSigned_at_seam hq]

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
lemma axis_smul {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (t:ℝ) : axis e (t • x)=t*axis e x := by simp [axis,real_inner_smul_left]
lemma radiusSq_smul {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (t:ℝ) : radiusSq e (t • x)=t^2*radiusSq e x := by
  simp only [radiusSq,axis_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
end Bernoulli.Cylindrical
namespace Bernoulli.DeSilvaJerison
lemma angle_smul (x:Space 7) {t:ℝ} (ht:0<t) : angle (t • x)=angle x := by
  simp only [angle,norm_smul,Real.norm_eq_abs,abs_of_pos ht,PiLp.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ ht.ne'
lemma Zsigned_smul (x:Space 7) {t:ℝ} (ht:0<t) : Zsigned (t • x)=t*Zsigned x := by
  rw [Zsigned_eq,Zsigned_eq,angle_smul x ht,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  ring
lemma KSup_smul {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) {t:ℝ} (ht:0<t) :
    KSup (t • x)=t^(-2:ℤ)*KSup x := by
  have hqt:0<Cylindrical.radiusSq axis (t • x):=by rw [Cylindrical.radiusSq_smul]; positivity
  rw [KSup_cylindrical hqt,KSup_cylindrical hq,Cylindrical.radiusSq_smul,Cylindrical.axis_smul]
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp

/-- The actual signed glued DSJ upper profile, including the symmetry axis. -/
def upperSigned (x:Space 7) :ℝ := if Cylindrical.radiusSq axis x≤1 then smoothCap x else outerSigned x

def upperFamily (l:ℝ) (x:Space 7) :ℝ := κ*l*max (upperSigned (l⁻¹ • x)) 0
lemma upperSigned_cap {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1) : upperSigned x=smoothCap x := ite_eq_left hq
lemma upperSigned_outer {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) : upperSigned x=outerSigned x := by
  rcases hq.eq_or_lt with h|h
  · rw [upperSigned_cap h.ge,upper_seam_agreement h.symm]
  · exact ite_eq_right (not_le.mpr h)
lemma upperFamily_nonneg {l:ℝ} (hl:0≤l) (x:Space 7) : 0≤upperFamily l x := by
  unfold upperFamily
  exact mul_nonneg (mul_nonneg κ_pos.le hl) (le_max_right _ _)

lemma upperSigned_continuous : Continuous upperSigned := by
  have hc:Continuous (Cylindrical.radiusSq axis):=(Cylindrical.radiusSq_contDiff axis (n:=1)).continuous
  have hcl:IsClosed {x:Space 7|Cylindrical.radiusSq axis x≤1}:=isClosed_le hc continuous_const
  apply continuous_if
  · intro x hx
    exact upper_seam_agreement (frontier_le_subset_eq hc continuous_const hx)
  · rw [hcl.closure_eq]
    intro x hx
    exact (smoothCap_contDiffAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hge:1≤Cylindrical.radiusSq axis x:=
      (closure_minimal (fun y hy=>le_of_lt (not_le.mp hy)) (isClosed_le continuous_const hc)) hx
    have hqp:0<Cylindrical.radiusSq axis x:=by linarith
    obtain ⟨hx0,ha⟩:=radiusSq_pos_data hqp
    exact (outerSigned_contDiffAt (n:=1) hx0 ha).continuousAt.continuousWithinAt
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation

lemma strict_increase_above_zero {f:ℝ→ℝ} {a b:ℝ} (hab:a<b)
    (hc:ContinuousOn f (Icc a b)) (ha:0<f a)
    (hd:∀t∈Ico a b, 0<f t → ∃v:ℝ, 0<v ∧ HasDerivWithinAt f v (Ici t) t) : f a<f b := by
  by_contra hn
  have hba:f b≤f a:=not_lt.mp hn
  obtain ⟨c,hcI,hmax⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hc
  have hfa:f a≤f c:=hmax ⟨le_rfl,hab.le⟩
  have hbad (t:ℝ) (ht:t∈Ico a b) (htp:0<f t) (hm:IsMaxOn f (Icc a b) t) : False := by
    obtain ⟨v,hv,hdv⟩:=hd t ht htp
    have hm':IsMaxOn f (Icc t b) t := by
      intro y hy
      exact hm (Icc_subset_Icc_left ht.1 hy)
    have hs:segment ℝ t b⊆Icc t b:=by rw [segment_eq_Icc ht.2.le]
    have hcT:=sub_mem_posTangentConeAt_of_segment_subset hs
    have hh:=hm'.localize.hasFDerivWithinAt_nonpos
      (hdv.mono Icc_subset_Ici_self).hasFDerivWithinAt hcT
    have he:v*(b-t)≤0:=by simpa only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_comm] using hh
    exact (not_le.mpr (mul_pos hv (sub_pos.mpr ht.2))) he
  rcases hfa.eq_or_lt with he|he
  · apply hbad a ⟨le_rfl,hab⟩ ha
    intro t ht
    exact (hmax ht).trans_eq he.symm
  · have hcb:c<b:=by
      rcases hcI.2.eq_or_lt with hh|hh
      · rw [hh] at he
        exact False.elim ((not_lt.mpr hba) he)
      · exact hh
    exact hbad c ⟨hcI.1,hcb⟩ (ha.trans he) hmax

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
lemma hasDerivAt_dilate {f:E→ℝ} (x:E) {l:ℝ} (hl:l≠0) (hf:DifferentiableAt ℝ f (l⁻¹ • x)) :
    HasDerivAt (fun t:ℝ=>t*f (t⁻¹ • x))
      (f (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient f (l⁻¹ • x))) l := by
  have hd:=hf.hasFDerivAt.comp_hasDerivAt l (((hasDerivAt_id l).inv hl).smul_const x)
  convert! (hasDerivAt_id l).mul hd using 1
  simp only [Function.comp_apply, Pi.inv_apply, id_eq,one_mul,ContinuousLinearMap.map_smul,smul_eq_mul]
  rw [←inner_gradient_left,real_inner_smul_left,real_inner_comm x (gradient f (l⁻¹ • x))]
  field_simp
  ring
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

def upperTrace (x:Space 7) (l:ℝ) :ℝ := κ*l*upperSigned (l⁻¹ • x)
lemma upperTrace_continuous (x:Space 7) : ContinuousOn (upperTrace x) (Ioi 0) := by
  intro l hl
  exact ((continuousAt_const.mul continuousAt_id).mul
    (upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ (ne_of_gt hl)).smul continuousAt_const))).continuousWithinAt
lemma upperFamily_eq_max {l:ℝ} (hl:0≤l) (x:Space 7) :
    upperFamily l x=max (upperTrace x l) 0 := by
  rw [upperFamily,upperTrace,mul_max_of_nonneg _ _ (mul_nonneg κ_pos.le hl),mul_zero]
lemma radiusSq_inv_smul_le_iff {l:ℝ} (hl:0<l) (x:Space 7) :
    Cylindrical.radiusSq axis (l⁻¹ • x)≤1 ↔ Cylindrical.radiusSq axis x≤l^2 := by
  rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos hl),one_mul]
lemma upperTrace_right_derivative (x:Space 7) {l:ℝ} (hl:0<l) (hp:0<upperTrace x l) :
    ∃v:ℝ, 0<v ∧ HasDerivWithinAt (upperTrace x) v (Ici l) l := by
  have hqp:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hs:(fun t:ℝ=>t⁻¹ • x) l=l⁻¹ • x:=rfl
  have hps:0<upperSigned (l⁻¹ • x):=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
  by_cases hq:Cylindrical.radiusSq axis (l⁻¹ • x)≤1
  · have hc:=smoothCap_contDiffAt hq
    let v:=κ*(smoothCap (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient smoothCap (l⁻¹ • x)))
    refine ⟨v,mul_pos κ_pos (smoothCap_radial_defect_pos hq (by rwa [upperSigned_cap hq] at hps)),?_⟩
    have hd:HasDerivAt (fun t:ℝ=>κ*(t*smoothCap (t⁻¹ • x))) v l:=
      (Foliation.hasDerivAt_dilate x hl.ne' (hc.differentiableAt (by norm_num))).const_mul κ
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos:0<t:=hl.trans_le ht
      have hqt:Cylindrical.radiusSq axis (t⁻¹ • x)≤1 := by
        rw [radiusSq_inv_smul_le_iff htpos]
        exact ((radiusSq_inv_smul_le_iff hl x).mp hq).trans ((sq_le_sq₀ hl.le htpos.le).mpr ht)
      rw [upperTrace,upperSigned_cap hqt]
      ring
    · rw [upperTrace,upperSigned_cap hq]
      ring
  · have hq1:1<Cylindrical.radiusSq axis (l⁻¹ • x):=not_le.mp hq
    have hqp':0<Cylindrical.radiusSq axis (l⁻¹ • x):=by linarith
    obtain ⟨hx0,ha⟩:=radiusSq_pos_data hqp'
    let v:=κ*(outerSigned (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient outerSigned (l⁻¹ • x)))
    refine ⟨v,?_,?_⟩
    · rw [show v=κ*(3*capAmplitude*KSup (l⁻¹ • x)) by dsimp [v]; rw [outerSigned_radial_defect hx0 ha]]
      exact mul_pos κ_pos (mul_pos (mul_pos (by norm_num) capAmplitude_pos) (KSup_pos hx0 ha))
    · have hd:HasDerivAt (fun t:ℝ=>κ*(t*outerSigned (t⁻¹ • x))) v l:=
        (Foliation.hasDerivAt_dilate x hl.ne'
          ((outerSigned_contDiffAt (n:=1) hx0 ha).differentiableAt (by norm_num))).const_mul κ
      have hcont:ContinuousAt (fun t:ℝ=>Cylindrical.radiusSq axis (t⁻¹ • x)) l:=
        (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
          ((continuousAt_id.inv₀ hl.ne').smul continuousAt_const)
      apply hd.hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [(hcont.eventually (lt_mem_nhds hq1)).filter_mono nhdsWithin_le_nhds] with t ht
        rw [upperTrace,upperSigned_outer ht.le]
        ring
      · rw [upperTrace,upperSigned_outer hq1.le]
        ring
lemma upperFamily_strict {x:Space 7} {a b:ℝ} (ha:0<a) (hab:a<b) (hp:0<upperFamily a x) :
    upperFamily a x<upperFamily b x := by
  have hb:0<b:=ha.trans hab
  rw [upperFamily_eq_max ha.le] at hp ⊢
  rw [upperFamily_eq_max hb.le]
  have hpa:0<upperTrace x a:=by simpa using hp
  have hh:=Foliation.strict_increase_above_zero hab
    ((upperTrace_continuous x).mono (fun t ht=>ha.trans_le ht.1)) hpa
    (fun t ht hpt=>upperTrace_right_derivative x (ha.trans_le ht.1) hpt)
  rw [max_eq_left hpa.le,max_eq_left (hpa.trans hh).le]
  exact hh
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma p_eq_max_f {t:ℝ} (ht:|t|<1) : p t=max (f t) 0 := by
  by_cases h:t7≤|t|
  · have hf:f t≤0 := by
      rw [←f_abs,←f_t7]
      exact f_strictAnti.antitoneOn ⟨t7_pos.le,t7_lt_one⟩ ⟨abs_nonneg t,ht⟩ h
    rw [p_eq_zero h,max_eq_right hf]
  · have hlt:|t|<t7:=lt_of_not_ge h
    rw [p_eq_f hlt.le,max_eq_left (f_pos_of_abs_lt hlt).le]
lemma U_eq_signed_pospart {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    U x=κ*max (Zsigned x) 0 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  rw [U,Z,Zsigned_eq]
  change κ*(‖x‖*p (angle x))=κ*max (‖x‖*f (angle x)) 0
  rw [p_eq_max_f ha,mul_max_of_nonneg _ _ (norm_nonneg x),mul_zero]
lemma upperFamily_outer_formula {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2≤Cylindrical.radiusSq axis x) :
    upperFamily l x=κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0 := by
  have hqp:0<Cylindrical.radiusSq axis x:=(sq_pos_of_pos hl).trans_le hq
  have hqt:1≤Cylindrical.radiusSq axis (l⁻¹ • x) := by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,le_div_iff₀ (sq_pos_of_pos hl),one_mul]
    exact hq
  rw [upperFamily,upperSigned_outer hqt,mul_assoc,mul_max_of_nonneg _ _ hl.le,mul_zero,
    outerSigned,Zsigned_smul x (inv_pos.mpr hl),KSup_smul hqp (inv_pos.mpr hl)]
  norm_num only [zpow_neg,zpow_ofNat,inv_inv]
  congr 2
  field_simp
lemma upperFamily_tendsto_zero_off_axis {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    Tendsto (fun l:ℝ=>upperFamily l x) (𝓝[>] 0) (𝓝 (U x)) := by
  have hc:ContinuousAt (fun l:ℝ=>κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0) 0:=by fun_prop
  have he:(fun l:ℝ=>upperFamily l x)=ᶠ[𝓝[>] 0]
      (fun l:ℝ=>κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0) := by
    have hsq:∀ᶠ l:ℝ in 𝓝[>] 0,l^2<Cylindrical.radiusSq axis x := by
      exact ((continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hq))).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsq,self_mem_nhdsWithin] with l hl hp
    exact upperFamily_outer_formula hp hl.le
  apply Tendsto.congr' he.symm
  simpa only [zero_pow (by norm_num:3≠0),mul_zero,zero_mul,add_zero,←U_eq_signed_pospart hq] using hc.tendsto.mono_left nhdsWithin_le_nhds
lemma U_zero_of_radiusSq_zero {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : U x=0 := by
  apply le_antisymm _ (U_nonneg x)
  by_contra hn
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp (lt_of_not_ge hn)
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  have hs:|x 6|<‖x‖ := by
    have hh:=ha.trans t7_lt_one
    rw [angle,abs_div,abs_of_pos hn,div_lt_one hn] at hh
    exact hh
  have hs2: (x 6)^2<‖x‖^2:=by nlinarith [sq_abs (x 6),abs_nonneg (x 6)]
  simp only [Cylindrical.radiusSq,Cylindrical.axis,inner_axis] at hq
  linarith
lemma smoothCap_pos_zero : 0<smoothCap 0 := by
  change 0<CapAlgebra.Y (Cylindrical.radiusSq axis 0) capB capC*
    capH (Cylindrical.axis axis 0*(CapAlgebra.V (Cylindrical.radiusSq axis 0) capB)⁻¹)
  simp only [Cylindrical.radiusSq,Cylindrical.axis,norm_zero,inner_zero_left,zero_pow (by norm_num:2≠0),sub_zero,zero_mul]
  exact mul_pos (CapAlgebra.Y_pos (by norm_num)
    (CapAlgebra.V_bounds (by norm_num) (by norm_num) capB_bounds.1 capB_bounds.2).1 capC_pos)
    ((capH_pos_iff 0).mpr (by norm_num))
lemma smoothCap_le_at_zero {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : smoothCap x ≤ smoothCap 0 := by
  have hh:∀s:ℝ,capH s≤capH 0 := by
    intro s
    rw [←capH_abs]
    exact capH_antitone (by norm_num) (abs_nonneg s) (abs_nonneg s)
  have hq0:Cylindrical.radiusSq axis (0:Space 7)=0:=by simp [Cylindrical.radiusSq,Cylindrical.axis]
  unfold smoothCap Cylindrical.lift
  rw [hq,hq0]
  simp only [Cylindrical.axis,inner_zero_left,zero_mul]
  exact mul_le_mul_of_nonneg_left (hh _) (CapAlgebra.Y_pos (by norm_num)
    (CapAlgebra.V_bounds (by norm_num) (by norm_num) capB_bounds.1 capB_bounds.2).1 capC_pos).le
lemma upperFamily_axis_bound {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) {l:ℝ} (hl:0≤l) :
    upperFamily l x≤κ*l*smoothCap 0 := by
  have hqt:Cylindrical.radiusSq axis (l⁻¹ • x)=0:=by rw [Cylindrical.radiusSq_smul,hq,mul_zero]
  rw [upperFamily,upperSigned_cap (by rw [hqt]; norm_num)]
  exact mul_le_mul_of_nonneg_left (max_le (smoothCap_le_at_zero hqt) smoothCap_pos_zero.le) (mul_nonneg κ_pos.le hl)
lemma upperFamily_tendsto_zero (x:Space 7) :
    Tendsto (fun l:ℝ=>upperFamily l x) (𝓝[>] 0) (𝓝 (U x)) := by
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with hq|hq
  · rw [U_zero_of_radiusSq_zero hq.symm]
    apply squeeze_zero' (by filter_upwards [self_mem_nhdsWithin] with l hl; exact upperFamily_nonneg hl.le x)
      (by filter_upwards [self_mem_nhdsWithin] with l hl; exact upperFamily_axis_bound hq.symm hl.le)
    have hc:ContinuousAt (fun l:ℝ=>κ*l*smoothCap 0) 0:=by fun_prop
    simpa only [mul_zero,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · exact upperFamily_tendsto_zero_off_axis hq
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma upperSigned_pos_zero :0<upperSigned 0 := by
  rw [upperSigned_cap (by simp [Cylindrical.radiusSq,Cylindrical.axis])]
  exact smoothCap_pos_zero
lemma upperFamily_parameter_continuous (x:Space 7) :
    ContinuousOn (fun l=>upperFamily l x) (Ioi 0) := by
  intro l hl
  unfold upperFamily
  exact ((continuousAt_const.mul continuousAt_id).mul
    ((upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ (ne_of_gt hl)).smul continuousAt_const)).max continuousAt_const)).continuousWithinAt
lemma upperFamily_tendsto_atTop (x:Space 7) :
    Tendsto (fun l:ℝ=>upperFamily l x) atTop atTop := by
  have hi:Tendsto (fun l:ℝ=>l⁻¹ • x) atTop (𝓝 0) := by
    simpa only [zero_smul] using (tendsto_inv_atTop_zero: Tendsto (fun l:ℝ=>l⁻¹) atTop (𝓝 0)).smul (tendsto_const_nhds (x:=x))
  have hs:Tendsto (fun l:ℝ=>max (upperSigned (l⁻¹ • x)) 0) atTop (𝓝 (upperSigned 0)) := by
    simpa only [Function.comp_apply,max_eq_left upperSigned_pos_zero.le] using
      (upperSigned_continuous.tendsto 0 |>.comp hi).max (tendsto_const_nhds (x:=(0:ℝ)))
  exact (tendsto_id.const_mul_atTop κ_pos).atTop_mul_pos upperSigned_pos_zero hs
lemma existsUnique_upper_leaf (x:Space 7) {t:ℝ} (ht:U x<t) :
    ∃! l:ℝ, 0<l ∧ upperFamily l x=t := by
  have htpos:0<t:=(U_nonneg x).trans_lt ht
  obtain ⟨a,ha,hat⟩:∃a:ℝ,0<a ∧ upperFamily a x<t := by
    have hh:∀ᶠ a:ℝ in 𝓝[>] 0,0<a ∧ upperFamily a x<t := by
      filter_upwards [self_mem_nhdsWithin,(upperFamily_tendsto_zero x).eventually (gt_mem_nhds ht)] with a ha ha1
      exact ⟨ha,ha1⟩
    exact hh.exists
  obtain ⟨b,hab,hbt⟩:∃b:ℝ,a<b ∧ t<upperFamily b x := by
    exact ((eventually_gt_atTop a).and ((upperFamily_tendsto_atTop x).eventually (eventually_gt_atTop t))).exists
  have hb:0<b:=ha.trans hab
  obtain ⟨l,hlI,hle⟩:=intermediate_value_Icc hab.le
    ((upperFamily_parameter_continuous x).mono (fun y hy=>ha.trans_le hy.1)) ⟨hat.le,hbt.le⟩
  change upperFamily l x=t at hle
  have hl:0<l:=ha.trans_le hlI.1
  refine ⟨l,⟨hl,hle⟩,?_⟩
  rintro s ⟨hs,hse⟩
  rcases lt_trichotomy s l with h|h|h
  · have hh:=upperFamily_strict hs h (by rw [hse]; exact htpos)
    rw [hse,hle] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh:=upperFamily_strict hl h (by rw [hle]; exact htpos)
    rw [hse,hle] at hh
    exact False.elim (lt_irrefl _ hh)
/-- Leaf parameter above the minimizer candidate. Its defining equation is proved
from the actual glued DSJ profiles; it is not a new foliation assumption. -/
def upperParameter (x:Space 7) (t:ℝ) :ℝ :=
  if h:U x<t then (existsUnique_upper_leaf x h).exists.choose else 0
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Spatial gradient of a smooth one-parameter family, as a joint field. -/
def spatialGradient (F:E×ℝ→ℝ) (p:E×ℝ) : E :=
  (toDual ℝ E).symm (fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ)

def divergence (V:E→E) (x:E) : ℝ :=
  ∑ i, inner ℝ (stdOrthonormalBasis ℝ E i) (fderiv ℝ V x (stdOrthonormalBasis ℝ E i))

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

/-- The actual upper foliation's spatial gradient at a point above the cone. -/
def upperCalibration (p:Space 7×ℝ) : Space 7 :=
  Foliation.spatialGradient (fun z:Space 7×ℝ=>upperFamily z.2 z.1)
    (p.1,upperParameter p.1 p.2)

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SeamCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
/-- Tangential matching gives the gradient of the one-homogeneous seam height. -/
def seamGradient (x:Space 7) : Space 7 :=
  capHP (Cylindrical.axis axis x) • axis+
    (capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)) •
      Cylindrical.transverse axis x
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.BoundedCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def upperFlux (p:Space 7×ℝ) : Space 7 :=
  if U p.1<p.2 then
    κ • (if Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1
      then gradient smoothCap ((upperParameter p.1 p.2)⁻¹ • p.1)
      else gradient outerSigned ((upperParameter p.1 p.2)⁻¹ • p.1))
  else 0
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SeamHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def seamHeight (x:Space 7):ℝ:=κ*Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH x
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LocalFluxExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def exteriorFlux (p:Space 7×ℝ):Space 7:=κ • gradient Zsigned p.1+
  ((p.2-κ*Zsigned p.1)/KSup p.1) • gradient KSup p.1
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.JointIntervalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def heightPrimitive (F:E×ℝ→G) (p:E×ℝ) : G := ∫s in (0:ℝ)..p.2,F (p.1,s)

end Bernoulli.ParametricIntegral

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.Foliation
open ParametricIntegral
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def graphPotential (A:E×ℝ→E) (u v:E→ℝ) (x:E) : E :=
  (2:ℝ) • (heightPrimitive A (x,v x)-heightPrimitive A (x,u x))
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PiecewiseFoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def splitGraphPotential (A B:E×ℝ→E) (u w v:E→ℝ) (x:E):E:=
  graphPotential A u w x+graphPotential B w v x

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedFoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def clampedHeight (u σ v:E→ℝ) (x:E):ℝ:=max (u x) (min (v x) (σ x))
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.VerticalGraphLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Primitive of the actual field between two graphs; no assigned derivative. -/
def verticalPotential (F:E×ℝ→E) (u v:E→ℝ) (x:E):E:=(2:ℝ) • (∫s in u x..v x,F (x,s))

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationBulkGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
def bulkExpression (A:E×ℝ→E) (p:E×ℝ):ℝ:=
  divergence (fun x=>A (x,p.2)) p.1+inner ℝ (A p) (deriv (fun t=>A (p.1,t)) p.2)
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.IntegratedPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

def shiftU (ε:ℝ) (x:Space 7):ℝ:=U x+ε
def ceilingGraph (ε:ℝ) (v:Space 7→ℝ) (x:Space 7):ℝ:=max (shiftU ε x) (v x)
def comparisonR (ε:ℝ) (v:Space 7→ℝ) (x:Space 7):ℝ:=
  if U x+ε<v x then ‖gradient v x‖^2+‖upperFlux (x,U x+ε)‖^2-
    2*inner ℝ (upperFlux (x,U x+ε)) (gradient U x) else 0

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLipschitzComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

def energyDifference (v:Space 7→ℝ) (x:Space 7):ℝ:=
  (‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0)-
  (‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0)

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
variable {d : ℕ}
/-- The square perspective on the nonnegative cone, with its zero value at
zero denominator. Used on actual admissible Lipschitz variations. -/
def positiveSquareRatio (v u : Space d → ℝ) (x : Space d) : ℝ :=
  if 0<u x then v x^2/u x else 0

end Bernoulli.Halfspace

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SobolevIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace Bernoulli.SobolevCalculus

def innerCut (n : ℕ) (t : ℝ) : ℝ := cutPrimitive n (t - 1/((n:ℝ)+1))
def innerSlope (n : ℕ) (t : ℝ) : ℝ := cutSlope n (t - 1/((n:ℝ)+1))

end Bernoulli.SobolevCalculus

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ThresholdRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uF

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Bernoulli.ThresholdRecovery

def ramp (ε t:ℝ) : ℝ := min (max (t/ε) 0) 1
def envelope (ε u w:ℝ) : ℝ := if 0<u then 1 else ramp ε w
end Bernoulli.ThresholdRecovery

end
end

end OAI
end


