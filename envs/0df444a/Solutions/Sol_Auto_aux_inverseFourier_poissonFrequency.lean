-- Prove2me | solution 1 for Auto.aux_inverseFourier_poissonFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:06.126842+00:00
-- url     : https://prove2.me/submissions/01fd594b-00f0-499d-b8e4-07717cc2ef90

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

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ)) x =
      (poissonKernel x : ℂ) := by
  let ω : ℝ := 2 * Real.pi * x
  let F : ℝ → ℂ := fun ξ =>
    Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) *
      (aux_poissonFrequency ξ : ℂ)
  let aNeg : ℂ := -1 + (ω : ℂ) * Complex.I
  let aPos : ℂ := 1 + (ω : ℂ) * Complex.I
  have hleft_eq : Set.EqOn F (fun ξ : ℝ => Complex.exp (aPos * ξ)) (Set.Iic 0) := by
    intro ξ hξ
    dsimp [F, aPos, ω, aux_poissonFrequency]
    have hξ' : ξ ≤ 0 := hξ
    rw [abs_of_nonpos hξ']
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright_eq : Set.EqOn F (fun ξ : ℝ => Complex.exp (aNeg * ξ)) (Set.Ioi 0) := by
    intro ξ hξ
    dsimp [F, aNeg, ω, aux_poissonFrequency]
    have hξ' : 0 < ξ := hξ
    rw [abs_of_pos hξ']
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleft_exp : IntegrableOn (fun ξ : ℝ => Complex.exp (aPos * ξ)) (Set.Iic 0) := by
    apply integrableOn_exp_mul_complex_Iic
    simp [aPos]
  have hright_exp : IntegrableOn (fun ξ : ℝ => Complex.exp (aNeg * ξ)) (Set.Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
    simp [aNeg]
  have hleft : IntegrableOn F (Set.Iic 0) :=
    hleft_exp.congr_fun hleft_eq.symm measurableSet_Iic
  have hright : IntegrableOn F (Set.Ioi 0) :=
    hright_exp.congr_fun hright_eq.symm measurableSet_Ioi
  have hleft_value : ∫ ξ in Set.Iic (0 : ℝ), F ξ = 1 / aPos := by
    calc
      (∫ ξ in Set.Iic (0 : ℝ), F ξ) =
          ∫ ξ in Set.Iic (0 : ℝ), Complex.exp (aPos * ξ) :=
        setIntegral_congr_fun measurableSet_Iic hleft_eq
      _ = 1 / aPos := by
        simpa using (integral_exp_mul_complex_Iic (a := aPos) (by simp [aPos]) 0)
  have hright_value : ∫ ξ in Set.Ioi (0 : ℝ), F ξ = -1 / aNeg := by
    calc
      (∫ ξ in Set.Ioi (0 : ℝ), F ξ) =
          ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (aNeg * ξ) :=
        setIntegral_congr_fun measurableSet_Ioi hright_eq
      _ = -1 / aNeg := by
        simpa using (integral_exp_mul_complex_Ioi (a := aNeg) (by simp [aNeg]) 0)
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul, Real.inner_apply]
  change (∫ ξ : ℝ, F ξ) = _
  calc
    (∫ ξ : ℝ, F ξ) = ∫ ξ in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), F ξ := by
      rw [Set.Iic_union_Ioi, setIntegral_univ]
    _ = (∫ ξ in Set.Iic (0 : ℝ), F ξ) + ∫ ξ in Set.Ioi (0 : ℝ), F ξ :=
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright
    _ = 1 / aPos + -1 / aNeg := by rw [hleft_value, hright_value]
    _ = (poissonKernel x : ℂ) := by
      have hpos : (1 + (ω : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
      have hneg : (-1 + (ω : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
      have hden : 1 + ω ^ 2 ≠ 0 := by positivity
      have hdenC : 1 + (ω : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast hden
      calc
        1 / aPos + -1 / aNeg = (2 : ℂ) / ((1 + ω ^ 2 : ℝ) : ℂ) := by
          dsimp [aPos, aNeg]
          push_cast
          field_simp [hpos, hneg, hdenC]
          ring_nf
          rw [Complex.I_sq]
          ring
        _ = (poissonKernel x : ℂ) := by
          rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div]
          congr 1
end Auto
