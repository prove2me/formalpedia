-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:43.291664+00:00
-- url     : https://prove2.me/submissions/521bb957-34f2-4981-88cf-faa87b48b304

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
public import Theorems.Thm_Auto_gaussian_continuous
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_div_abs_tendsto
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_pos

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 0) := by
  let q : ℝ → ℝ := fun y => sqrtOneMinusGaussian y / |y|
  have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrtpi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrtpi_pos
  have hpi_div : Real.pi / Real.sqrt Real.pi = Real.sqrt Real.pi := by
    apply (div_eq_iff hsqrtpi_ne).2
    calc
      Real.pi = (Real.sqrt Real.pi) ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
      _ = Real.sqrt Real.pi * Real.sqrt Real.pi := by ring
  have hq : Tendsto q (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ))
      (𝓝 (Real.sqrt Real.pi)) := by
    simpa only [q] using aux_sqrtOneMinusGaussian_div_abs_tendsto
  have hpiGaussian : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
    have hcont : Continuous (fun y : ℝ => Real.pi * gaussian y) :=
      continuous_const.mul gaussian_continuous
    have h := hcont.tendsto (0 : ℝ)
    simpa [gaussian, Auto.gaussian] using h.mono_left nhdsWithin_le_nhds
  have habel : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
    have hcont : Continuous (fun y : ℝ =>
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|)) := by
      fun_prop
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hq_right : Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) hq
  have hpiGaussian_right : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 Real.pi) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) hpiGaussian
  have habel_right : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) habel
  have hquotient_right : Tendsto (fun y : ℝ =>
      (Real.pi * gaussian y) / q y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.sqrt Real.pi)) := by
    have hd := hpiGaussian_right.div hq_right hsqrtpi_ne
    rw [hpi_div] at hd
    refine hd.congr' ?_
    filter_upwards [] with y
    rfl
  have hright_raw : Tendsto (fun y : ℝ =>
      -(Real.pi * gaussian y / q y) +
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    simpa using hquotient_right.neg.add habel_right
  have hright : Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    refine hright_raw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hroot : sqrtOneMinusGaussian y ≠ 0 :=
      (aux_sqrtOneMinusGaussian_pos hy0).ne'
    have hscale : 0 < Real.sqrt Real.pi * y := mul_pos hsqrtpi_pos hy
    dsimp only [q]
    simp only [auxiliaryFunctionBDerivative, if_neg hy0, sign_pos hscale]
    rw [abs_of_pos hy]
    field_simp [hroot, hy0]
    norm_num
  have hq_left : Tendsto q (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) hq
  have hpiGaussian_left : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 Real.pi) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) hpiGaussian
  have habel_left : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) habel
  have hquotient_left : Tendsto (fun y : ℝ =>
      (Real.pi * gaussian y) / q y) (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (𝓝 (Real.sqrt Real.pi)) := by
    have hd := hpiGaussian_left.div hq_left hsqrtpi_ne
    rw [hpi_div] at hd
    refine hd.congr' ?_
    filter_upwards [] with y
    rfl
  have hleft_raw : Tendsto (fun y : ℝ =>
      Real.pi * gaussian y / q y -
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) := by
    simpa using hquotient_left.sub habel_left
  have hleft : Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) := by
    refine hleft_raw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_lt hy
    have hroot : sqrtOneMinusGaussian y ≠ 0 :=
      (aux_sqrtOneMinusGaussian_pos hy0).ne'
    have hscale : Real.sqrt Real.pi * y < 0 := mul_neg_of_pos_of_neg hsqrtpi_pos hy
    dsimp only [q]
    simp only [auxiliaryFunctionBDerivative, if_neg hy0,
      sign_neg hscale]
    rw [abs_of_neg hy]
    field_simp [hroot, hy0]
    norm_num
    ring
  rw [← Set.Iio_union_Ioi, nhdsWithin_union, tendsto_sup]
  exact ⟨hleft, hright⟩
end Auto
