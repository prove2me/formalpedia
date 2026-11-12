-- Prove2me | Definitions.Def_OAIQ247J006
-- name    : OAIQ247J006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:47:20.017331+00:00
-- url     : https://prove2.me/theorems/d5cbcda0-9b23-467c-8402-832a919f6674
-- title:
--   Definitions bundle OAIQ247J006 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 202 declarations of OpenAI's Lean: 5 definitions and 197 theorems. The definitions and types are `Erdos970.I₃₇`, `Erdos970.Lf`, `Erdos970.ZetaZerosNearPoint`, `OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.FlagState`, `OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedRegeneration`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_PNT1_ComplexAnalysis`, `Erdos970_PNT2_LogDerivative`, `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Erdos970_Z0`, `Erdos970_ZetaBounds`, [`Jacobsthal_Paths_FlaggedHarmonicPaths`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/FlaggedHarmonicPaths.lean), [`Jacobsthal_Paths_PairedHitting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/PairedHitting.lean).
--
--   **Imports.** It imports the bundles `OAIQ247J000` and `OAIQ247J001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ247J008` and `OAIQ247J009`; the proof of `OAI_Erdos970_WeightedTorusJets_dirichletRealZeroBound_proof_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J000
import Definitions.Def_OAIQ247J001

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT1_ComplexAnalysis
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain

  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r_int := by
    apply Metric.mem_ball.mpr
    have h1 : ‖z - 0‖ ≤ r_z := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    simp only [sub_zero] at h1
    have h2 : ‖z‖ < r_int := lt_of_le_of_lt h1 h_r_z_lt_r_int
    rwa [dist_eq_norm, sub_zero]

  set U := Metric.ball (0 : ℂ) R_analytic

  have hc_subset : Metric.closedBall (0 : ℂ) r_int ⊆ U := by
    apply Metric.closedBall_subset_ball
    exact h_r_int_lt_R_analytic

  have hf_on_U : DifferentiableOn ℂ f U := by

    apply DifferentiableOn.mono hf_diff_U'
    calc U = Metric.ball 0 R_analytic := rfl
         _ ⊆ Metric.closedBall 0 R_analytic := Metric.ball_subset_closedBall
         _ ⊆ U' := h_subset

  have cauchy_eq := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    Metric.isOpen_ball hc_subset hf_on_U hz_in_ball

  rw [← cauchy_eq]

  congr 2
  ·                                         
    simp only [one_div]
                                  
    rfl
  ·                                               
    ext w
    rw [← inv_pow]

lemma circleMap_zero_eq_exp (r : ℝ) (t : ℝ) : circleMap 0 r t = r * Complex.exp (I * t) := by
                                                                         
  rw [circleMap]
                                                                                    
  simp only [zero_add]
                                                                          
  congr 2
  rw [mul_comm (t : ℂ) Complex.I]
                                      
  rfl

lemma lem_dw_dt_real {r_int : ℝ} (t : ℝ) :
deriv (fun (t' : ℝ) => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
                                       
  rw [deriv_const_mul]
                                             
  rw [deriv_cexp]
                                                  
  rw [deriv_const_mul]
                                                            
  rw [deriv_ofReal_eq_one]
                                                                                        
  ring
                                                                         
  · exact differentiableAt_ofReal t
  · exact (differentiableAt_const I).mul (differentiableAt_ofReal t)
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul (differentiableAt_ofReal t))

lemma deriv_circleMap_zero (r : ℝ) (t : ℝ) : deriv (circleMap 0 r) t = I * r * Complex.exp (I * t) := by
                                                            
  have h : circleMap 0 r = fun (t' : ℝ) => r * Complex.exp (I * t') := by
    ext t'
    exact circleMap_zero_eq_exp r t'

  rw [h]

  exact lem_dw_dt_real t

lemma lem_CIF_deriv_param {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
                                                               
  rw [cauchy_formula_deriv hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [circleIntegral_def_Icc]

  rw [smul_eq_mul]

  simp only [circleMap_zero_eq_exp, deriv_circleMap_zero]

  congr 2
  ext t
  simp only [smul_eq_mul]
  ring

lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [I, Complex.I_ne_zero, Real.pi_pos.ne']

lemma factor_I_from_integrand (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) :
  ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  I * ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) := by

  have h : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
           ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I • (↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t))) := by
    congr 1
    ext t
    rw [smul_eq_mul]
    ring
  rw [h]
                                                              
  rw [MeasureTheory.integral_smul]
                                                                 
  rw [smul_eq_mul]

lemma integrand_transform_div (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) (t : ℝ) :
  ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  ↑r_int * Complex.exp (I * ↑t) * f (↑r_int * Complex.exp (I * ↑t)) / (↑r_int * Complex.exp (I * ↑t) - z) ^ 2 := by
                                                              
  rw [inv_pow]
                                                                                     
  rw [← div_eq_mul_inv]
                                                
  ring

lemma lem_CIF_deriv_simplified {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
                              
  rw [lem_CIF_deriv_param hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [factor_I_from_integrand f r_int z]

  rw [← mul_assoc, complex_coeff_I_cancel]

  congr 2
  funext t
  rw [integrand_transform_div f r_int z t]

lemma lem_modulus_of_f_prime0 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                                 
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

lemma lem_integral_modulus_inequality {r_int : ℝ} {z : ℂ} {f : ℂ → ℂ} :
norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                        
  rw [complex_abs_mul]

  rw [abs_one_div_two_pi_complex]

  apply mul_le_mul_of_nonneg_left
  ·                                                                  
    have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by
      apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos
    exact abs_integral_le_integral_abs h_2pi_nonneg
  · exact le_of_lt one_div_two_pi_pos

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                           
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                        
  exact lem_integral_modulus_inequality

lemma lem_modulus_of_integrand_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (_h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
    norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) =
norm (f (r_int * Complex.exp (I * t))) * norm (r_int * Complex.exp (I * t)) := by
                                                                     
  rw [norm_mul]

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
                                                        
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
                                        
  unfold I
                                                    
  rw [Complex.mul_re]

  rw [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
                                  
  ring

lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
                                                                                            
  rw [lem_modeit]
                                                   
  rw [lem_Reit0]
                                         
  rw [lem_e01]

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
                                                              
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
                                                                      
  rw [lem_modulus_of_integrand_product2 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]
                                                                            
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  rw [lem_modulus_of_ae_it h_r_int_pos]
                                                                
  ring

lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                  
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
                                                                    
  have h_triangle := lem_reverse_triangle (r_int * Complex.exp (I * t)) z
                                     
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
r_int - r_z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                        
  have h1 : norm z ≤ r_z := by
    have h_dist : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
                                                             
  have h2 : r_int - r_z ≤ r_int - norm z := by linarith [h1]
                                                                                               
  have h3 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact le_trans h2 h3

lemma lem_zrr3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
                                                       
  have h_ineq := @lem_zrr2 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                    
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
                                                    
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
                                
  rw [pow_two, pow_two]
  exact h_sq

lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
                                             
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                               
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact lt_of_lt_of_le h1 h2

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
                                                                                  
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                  
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
                                                                   
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                    
  exact pow_ne_zero 2 h_ne_zero

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                               
  have h_neq_zero : r_int * Complex.exp (I * t) - z ≠ 0 :=
    lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                         
  have h_sq_neq_zero : (r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_self_ne_zero.mpr h_neq_zero
                                              
  rw [lem_absdiv h_sq_neq_zero]
                                                              
  rw [lem_modulus_wz]

lemma lem_modulus_of_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                                                                             
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                           
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]

lemma lem_modulus_of_product4 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
                                               
  rw [lem_modulus_of_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  apply div_le_div_of_nonneg_left
  ·                            
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _
  ·                                           
    apply pow_pos
    linarith [h_r_z_lt_r_int]
  ·                                                              
    exact h_ineq

lemma lem_bound_on_f_at_r_prime {M R_analytic r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (hr_int_pos : 0 < r_int)
    (hr_int_lt_R_analytic : r_int < R_analytic)
    (f : ℂ → ℂ)

    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ z ∈ Metric.closedBall 0 R_analytic, (f z).re ≤ M)
    (t : ℝ) :
norm (f (r_int * Complex.exp (I * t))) ≤ (2 * r_int * M) / (R_analytic - r_int) := by
                                         
  obtain ⟨U, hU_open, h_subset, hf_diff_U⟩ := hf_domain

  let z₀ := r_int * Complex.exp (I * t)

  have h_sSup_bound := thm_BorelCaratheodoryI R_analytic M hR_analytic_pos hM_pos f
                                                                   
    (by
                                        
      have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open

      rw [ballDR]
      convert (preTransparency := .instances) h_analytic_U.mono h_subset
                                                                              
      apply closure_ball
      linarith
      )
    hf0
    (by rwa [lem_ballDR R_analytic hR_analytic_pos])                         
    r_int hr_int_pos hr_int_lt_R_analytic

  have hz₀_in_ball : z₀ ∈ Metric.closedBall 0 r_int := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
                                                          
    have h_norm : ‖r_int * Complex.exp (I * t)‖ = r_int := by
      rw [norm_mul]

      have h1 : ‖(r_int : ℂ)‖ = r_int := by
        rw [Complex.norm_real]
        exact abs_of_pos hr_int_pos
                                           
      have h2 : ‖Complex.exp (I * ↑t)‖ = 1 := by
                                                               
        exact lem_modulus_of_e_it_is_one t
      rw [h1, h2]
      ring
    rw [h_norm]

  have hz₀_in_closure : z₀ ∈ closure (ballDR r_int) := by
    rw [lem_ballDR r_int hr_int_pos]
    exact hz₀_in_ball

  have h_in_image : norm (f z₀) ∈ (norm ∘ f) '' (closure (ballDR r_int)) := by
    use z₀, hz₀_in_closure
    rfl

  have h_le_sSup : norm (f z₀) ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := by
    apply le_csSup
                                            
    · use (2 * r_int / (R_analytic - r_int)) * M
      intros x hx
      obtain ⟨w, hw_in, hx_eq⟩ := hx
      rw [← hx_eq]
                                         
      have hw_in_closed : w ∈ Metric.closedBall 0 r_int := by
        rwa [← lem_ballDR r_int hr_int_pos]
                                                                   
      have hw_in_R : w ∈ Metric.closedBall 0 R_analytic := by
        have h_subset : Metric.closedBall (0 : ℂ) r_int ⊆ Metric.closedBall 0 R_analytic := by
          apply Metric.closedBall_subset_closedBall
          linarith [hr_int_lt_R_analytic]
        exact h_subset hw_in_closed
                                                  
      exact lem_BCI R_analytic M hR_analytic_pos hM_pos f
        (by
          rw [ballDR]
          have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open
          convert (preTransparency := .instances) h_analytic_U.mono h_subset
          apply closure_ball
          linarith)
        hf0
        (by rwa [lem_ballDR R_analytic hR_analytic_pos])
        r_int hr_int_pos hr_int_lt_R_analytic w
        (by aesop)
                                
    · exact h_in_image

  calc norm (f z₀)
    ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := h_le_sSup
    _ ≤ (2 * r_int / (R_analytic - r_int)) * M := h_sSup_bound
    _ = (2 * r_int * M) / (R_analytic - r_int) := by ring

lemma lem_bound_on_integrand_modulus {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z)
    (t : ℝ) :
norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                            
  have h1 := lem_modulus_of_product4 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                 
  have h2 := lem_bound_on_f_at_r_prime hM_pos hR_analytic_pos (lt_trans h_r_z_pos h_r_z_lt_r_int) h_r_int_lt_R_analytic f hf_domain hf0 hRe_f_le_M t

  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  have h_denom_nonneg : 0 ≤ (r_int - r_z) ^ 2 := by
    apply sq_nonneg

  have h3 : (r_int * norm (f (r_int * Complex.exp (I * t)))) / (r_int - r_z) ^ 2 ≤
            (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 := by
    apply div_le_div_of_nonneg_right _ h_denom_nonneg
    apply mul_le_mul_of_nonneg_left h2
    linarith [h_r_int_pos]

  have h4 : (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 =
            (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
    have h_R_sub_r_pos : 0 < R_analytic - r_int := by linarith [h_r_int_lt_R_analytic]
    have h_r_sub_r_pos : 0 < r_int - r_z := by linarith [h_r_z_lt_r_int]
    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  rw [h4] at h3
  exact le_trans h1 h3

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by

  have h1 : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal

  have h2 : Continuous (fun z : ℂ => I * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  have h3 : Continuous Complex.exp := Complex.continuous_exp

  have h4 : Continuous (fun z : ℂ => (r : ℂ) * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  apply Continuous.comp h4
  apply Continuous.comp h3
  apply Continuous.comp h2
  exact h1

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
                                                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
                                                                  
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
                                                               
    exact DifferentiableOn.continuousOn hf_on_closed

  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
                                                        
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  exact continuousOn_univ.mp hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by

  have h1 : Continuous (fun t : ℝ => r * Complex.exp (I * t) - z) := by
                                                         
    apply Continuous.sub
    ·                                                                                 
      exact continuous_real_parameterization r
    ·                                           
      exact continuous_const

  have h2 : Continuous (fun x : ℂ => x ^ 2) := continuous_pow 2

  exact Continuous.comp h2 h1

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                                             
  apply Continuous.intervalIntegrable

  apply Continuous.comp continuous_norm

  apply Continuous.div₀

  · apply Continuous.mul
                                                     
    · exact continuous_real_parameterization r_int
                                                         
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  · exact continuous_denominator_parameterized r_int z

  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma lem_f_prime_bound_by_integral_of_constant {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                                 
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  set C := (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2)

  have h_bound : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    exact lem_bound_on_integrand_modulus hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz t

  have h_eq : ∀ t, norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
    intro t
    congr 2
    ring

  have h_bound_h1 : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    rw [h_eq]
    exact h_bound t ht

  have h_integrable : IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                            
    exact interval_integrable_cauchy_integrand hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h2 := lem_integral_inequality ?_ h_integrable h_bound_h1

  have h_const_integral : ∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                       
    exact integral_const_over_interval C

  rw [h_const_integral] at h2

  have h3 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤
    (1 / (2 * Real.pi)) * (2 * Real.pi * C) := by
    apply mul_le_mul_of_nonneg_left h2
    apply div_nonneg
    · norm_num
    · linarith [Real.pi_pos]

  have h4 : (1 / (2 * Real.pi)) * (2 * Real.pi * C) = C := by
    have h_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    field_simp [h_pi_ne_zero]

  rw [h4] at h3
  exact le_trans h1 h3
  simp [Real.pi_nonneg]

lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                              
  exact lem_f_prime_bound_by_integral_of_constant hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
                                                            
  set r_prime := (r + R) / 2

  have h_intermediate := lem_r_prime_is_intermediate hr_pos hr_lt_R
  have h_r_lt_r_prime := h_intermediate.1
  have h_r_prime_lt_R := h_intermediate.2

  have h_bound := lem_f_prime_bound hM_pos hR_pos hr_pos h_r_lt_r_prime h_r_prime_lt_R hf_domain hf0 hRe_f_le_M hz

  have h_final := lem_bound_after_substitution hM_pos hr_pos hr_lt_R

  have h_combined : norm (deriv f z) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
    exact le_trans h_bound h_final

  convert (preTransparency := .instances) h_combined using 1
  all_goals try with_reducible_and_instances rfl
  ring

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped Interval

lemma def_If_z_plus_h
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, f (( (z + h).re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  simp [If_taxicab]

lemma diff_If_zh_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  classical
  intro w
                              
  let g : ℝ → ℂ := fun τ => f (((z + h).re : ℂ) + Complex.I * τ)
                                                              
  have hInt1 : IntervalIntegrable g volume (0 : ℝ) ((z + h).im) := by
    simpa [g] using
      (vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (a := z + h) hzh)
  have hInt2 : IntervalIntegrable g volume (0 : ℝ) (z.im) := by
    have hInt2' :
        IntervalIntegrable
          (fun τ : ℝ => f (((( (((z + h).re : ℂ) + Complex.I * z.im)).re : ℂ)) + Complex.I * τ))
          volume (0 : ℝ) (((((z + h).re : ℂ) + Complex.I * z.im)).im) :=
      vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf
        (a := (((z + h).re : ℂ) + Complex.I * z.im)) hw
    simpa [g, helper_re_of_w z h, helper_im_of_w z h] using hInt2'
  have hinterval :
      ((∫ τ in (0 : ℝ)..(z + h).im, g τ) - ∫ τ in (0 : ℝ)..z.im, g τ)
      = ∫ τ in z.im..(z + h).im, g τ :=
    intervalIntegral.integral_interval_sub_left (μ := volume) (f := g) hInt1 hInt2
                                          
  have h1 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ) := by
    have hzph := def_If_z_plus_h hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (z := z) (h := h) hz hzh
    simpa [g] using hzph
  have h2 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ) := by
    have hwdef := def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
    simpa [g, w] using hwdef
                                                           
  calc
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [h1, h2]
    _ = (Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - (Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = Complex.I *
          ((∫ τ in (0 : ℝ)..(z + h).im, g τ)
            - (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [helper_mul_sub_complex]
    _ = Complex.I * (∫ τ in z.im..(z + h).im, g τ) := by
      simpa using congrArg (fun t => Complex.I * t) hinterval
    _ = Complex.I * (∫ τ in z.im..(z + h).im,
          f (((z + h).re : ℂ) + Complex.I * τ)) := by
      simp [g]

lemma diff_If_w_z_initial_form
  {r1 R R0 : ℝ}
  (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..w.re, f (t : ℂ))
      + Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (w.re + Complex.I * τ) - f (z.re + Complex.I * τ))) := by
  intro w

  rw [def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
  rw [def_If_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz]

  have hw_re : w.re = (z + h).re := by simp [w]
  have hw_im : w.im = z.im := by simp [w]

  have step1 :
    ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
      - ((∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
      + Complex.I * ((∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
        - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))) := by ring
  rw [step1]

  have horizontal_integrable_zh : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) (z + h).re := by
                                                                          
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
                                                                  
    have : ‖z + h‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hzh
    have : |(z + h).re| ≤ ‖z + h‖ := Complex.abs_re_le_norm (z + h)
    have : |t| ≤ |(z + h).re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_integrable_z : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) z.re := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    have : ‖z‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hz
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have : |t| ≤ |z.re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_eq :
    (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
    = ∫ t in z.re..(z + h).re, f (t : ℂ) := by
    rw [← intervalIntegral.integral_interval_sub_left horizontal_integrable_zh horizontal_integrable_z]

  have vertical_integrable_zh : IntervalIntegrable (fun τ : ℝ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
                                                     
    rw [← hw_re, ← hw_im]
    exact vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hw

  have vertical_integrable_z : IntervalIntegrable (fun τ : ℝ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im :=
    vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz

  have vertical_eq :
    (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
      - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = ∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)) := by
    rw [← intervalIntegral.integral_sub vertical_integrable_zh vertical_integrable_z]

  rw [horizontal_eq, vertical_eq, hw_re]

lemma cauchy_for_rectangles
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r1)
    (hzw : ((w.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1)
    (hwz : ((z.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (z.im)))
    - (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (w.im)))
    + Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + Complex.I * y))
    - Complex.I * (∫ y in z.im..w.im, f ((z.re : ℂ) + Complex.I * y)) = 0 := by
  classical
                                                                                    
  have hA : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hz_eq : z = (z.re : ℂ) + Complex.I * z.im := by
      exact (lem_wReIm z)
    rwa [← hz_eq]
  have hC : ((w.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hw_eq : w = (w.re : ℂ) + Complex.I * w.im := by
      exact (lem_wReIm w)
    rwa [← hw_eq]
                                                                                                
  have h_left_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (z.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im) ((z.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (z.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hA hwz hseg
  have h_right_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (w.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((w.re : ℂ) + Complex.I * z.im) ((w.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (w.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hzw hC hseg
  have h_point_in_ball : ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im,
      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro x hx y hy
    have hL : ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_left_in_ball y hy
    have hR' : ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_right_in_ball y hy
                                                                
    obtain ⟨lam, hlam0, hlam1, hx_eq⟩ := real_between_as_convex_combination z.re w.re x (Set.mem_uIcc.mp hx)
    have hseg_horiz : (x : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
                                    
      have : (x : ℂ) + Complex.I * (y : ℂ)
          = (1 - lam) • ((z.re : ℂ) + Complex.I * (y : ℂ)) + lam • ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
        simp only [Complex.real_smul]
                                                    
        rw [hx_eq]
        simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simpa [this] using
        (convex_combination_mem_segment ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) lam hlam0 hlam1)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hL hR' hseg_horiz
                                                                
  set S := ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  have hS_subset_r1 : S ⊆ Metric.closedBall (0 : ℂ) r1 := by
    intro p hp
    have hx : p.re ∈ [[z.re, w.re]] := hp.1
    have hy : p.im ∈ [[z.im, w.im]] := hp.2
                                                              
    have : ((p.re : ℂ) + Complex.I * (p.im : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 :=
      h_point_in_ball p.re hx p.im hy
                                                                       
    have hp_eq : p = (p.re : ℂ) + Complex.I * (p.im : ℂ) := lem_wReIm p
    rwa [hp_eq]
  have hS_subset_R : S ⊆ Metric.closedBall (0 : ℂ) R :=
    fun p hp => (closedBall_mono_center0 (le_of_lt hr1_lt_R)) (hS_subset_r1 hp)
                                                                               
  have Hdiff : DifferentiableOn ℂ f S := by
    intro p hp
    have hpR : p ∈ Metric.closedBall (0 : ℂ) R := hS_subset_R hp
    exact (hf p hpR).differentiableAt.differentiableWithinAt
                                                          
  simpa [smul_eq_mul, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w Hdiff

lemma cauchy_for_horizontal_strip
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    - (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) = 0 := by
                                                                               
  let z₀ : ℂ := (z.re : ℂ)
  let w₀ : ℂ := (z + h).re + Complex.I * z.im
                         
  have hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r1 := by
    have hz_norm : ‖z‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzre_le : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm z
    have : ‖z₀‖ ≤ r1 := le_trans hzre_le hz_norm
    simpa [z₀, Metric.mem_closedBall, dist_eq_norm] using this
  have hw₀ : w₀ ∈ Metric.closedBall (0 : ℂ) r1 := hw
                                                  
  have hzw : ((w₀.re : ℂ) + Complex.I * z₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                                          
    have h1 : ((w₀.re : ℂ) + Complex.I * z₀.im) = ((z + h).re : ℂ) := by
      simp [w₀, z₀, Complex.ofReal_im, mul_zero, add_zero]
    rw [h1]
    have h2 : ‖((z + h).re : ℂ)‖ ≤ ‖z + h‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm (z + h)
    have h3 : ‖z + h‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzh
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_trans h2 h3
  have hwz : ((z₀.re : ℂ) + Complex.I * w₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                            
    have h1 : ((z₀.re : ℂ) + Complex.I * w₀.im) = z := by
      simp [z₀, w₀, Complex.ofReal_re]
      exact (lem_wReIm z).symm
    rw [h1]
    exact hz
                                   
  have H := cauchy_for_rectangles (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz₀ hw₀ hzw hwz

  rw [(show z₀.re = z.re by simp [z₀])] at H
  rw [(show z₀.im = (0 : ℝ) by simp [z₀])] at H
  rw [(show w₀.re = (z + h).re by simp [w₀])] at H
  rw [(show w₀.im = z.im by simp [w₀])] at H

  convert (preTransparency := .instances) H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.ofReal_zero, mul_zero, add_zero]

lemma integrability_from_cauchy_horizontal_strip
    {r1 R R0 : ℝ} (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r1) (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im ∧
    IntervalIntegrable (fun τ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
  constructor
  ·                                                         
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                           
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hzh
      exact le_trans (Complex.abs_re_le_norm (z + h)) hzh
    ·                                              
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
  ·                                                    
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                     
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact le_trans (Complex.abs_re_le_norm z) hz
    ·                                        
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [← lem_wReIm z]
      exact hz

lemma cauchy_rearrangement_step1
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)))
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) - (∫ t in z.re..(z + h).re, f (t : ℂ)) := by
                                   
  have H := cauchy_for_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have integrable := integrability_from_cauchy_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange := algebraic_rearrangement_four_terms
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    H

  have vertical_linearity :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ))) := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub integrable.1 integrable.2]

  rw [← vertical_linearity]
  exact rearrange

lemma diff_If_w_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by

  have initial_form := diff_If_w_z_initial_form hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange_step := cauchy_rearrangement_step1 hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have w_re_eq : (((z + h).re : ℂ) + Complex.I * z.im).re = (z + h).re := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

  simp_rw [initial_form, w_re_eq, rearrange_step]

  ring

lemma If_difference_is_L_path_integral
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
      + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by

  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im

  calc If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
       - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
     = (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩)
       + (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
          - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩) := by ring
     _ = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ))
       + (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by
       rw [diff_If_zh_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw,
           diff_If_w_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
     _ = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
       + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by ring

lemma If_diff_add_sub_identity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z) + f z)
    + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) := by
                                                                                               
  have H :=
    If_difference_is_L_path_integral (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one) hf hz hzh hw
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using H

lemma If_diff_linearity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    ((∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
     + (∫ _t in z.re..(z + h).re, f z))
    + Complex.I *
      ((∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))
       + (∫ _τ in z.im..(z + h).im, f z)) := by
                                                                                             
  have H := If_diff_add_sub_identity hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have hz_norm : ‖z‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hzh_norm : ‖z + h‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzh
  have hw_norm : ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hw

  have h_z_eq : z = (z.re : ℂ) + Complex.I * z.im := lem_wReIm z
  have h_zh_eq : z + h = ((z + h).re : ℂ) + Complex.I * (z + h).im := lem_wReIm (z + h)

  have hz_endpoint : ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1 := by rwa [← h_z_eq]
  have h_horiz_integrable := intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
    hr1_lt_R hf hz_endpoint hw_norm

  have hzh_endpoint : ‖((z + h).re : ℂ) + Complex.I * (z + h).im‖ ≤ r1 := by rwa [← h_zh_eq]
  have h_vert_integrable := intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
    hr1_lt_R hf hw_norm hzh_endpoint

  have h_const_horiz : IntervalIntegrable (fun _ => f z) volume z.re (z + h).re := intervalIntegrable_const
  have h_const_vert : IntervalIntegrable (fun _ => f z) volume z.im (z + h).im := intervalIntegrable_const

  have h_diff_horiz : IntervalIntegrable (fun t => f (t + Complex.I * z.im) - f z) volume z.re (z + h).re :=
    IntervalIntegrable.sub h_horiz_integrable h_const_horiz

  have h_diff_vert : IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ) - f z) volume z.im (z + h).im :=
    IntervalIntegrable.sub h_vert_integrable h_const_vert

  have h1 : ∫ t in z.re..(z + h).re, ((f (t + Complex.I * z.im) - f z) + f z) =
           (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)) + (∫ t in z.re..(z + h).re, f z) :=
    intervalIntegral.integral_add h_diff_horiz h_const_horiz

  have h2 : ∫ τ in z.im..(z + h).im, ((f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) =
           (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)) + (∫ τ in z.im..(z + h).im, f z) :=
    intervalIntegral.integral_add h_diff_vert h_const_vert

  rw [H, h1, h2, mul_add]

lemma If_diff_decomposition_final
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = f z * h
      + Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                                      
  have H :=
    If_diff_linearity (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one)
      (f := f) (hf := hf)
      (z := z) (h := h)
      (hz := hz) (hzh := hzh) (hw := hw)
                                                                   
  let A : ℂ := ∫ t in z.re..(z + h).re, f (t + Complex.I * z.im) - f z
  let B : ℂ := ∫ t in z.re..(z + h).re, f z
  let C : ℂ := ∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ) - f z
  let D : ℂ := ∫ τ in z.im..(z + h).im, f z
                                                                    
  have hH' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + B) + Complex.I * (C + D) := by
    simpa [A, B, C, D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H
                                                                          
  have hsplit : (A + B) + Complex.I * (C + D)
      = (A + Complex.I * C) + (B + Complex.I * D) := by ring
  have hH'' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + (B + Complex.I * D) := by
    simpa [hsplit] using hH'
                                                               
  have hBD : (B + Complex.I * D) = f z * h := by
    simpa [B, D] using
      integral_of_constant_over_L_path (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh
  have hH''' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + f z * h := by
    simpa [hBD] using hH''
                                                                
  have hH4 : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h + f z * h := by
    simpa [Err, A, C, add_comm, add_left_comm, add_assoc] using hH'''
                                                         
  simpa [Err, add_comm, add_left_comm, add_assoc] using hH4

lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
                                                          
  unfold Err
                                    
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [hI, one_mul]

  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
                                                
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
                                  
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      convert (preTransparency := .instances) (Complex.continuous_ofReal.add (continuous_const (y := Complex.I * (z.im : ℂ)))) using 1
      all_goals try with_reducible_and_instances rfl
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
                                                                  
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by

        have := horizontal_line_in_segment (a := z.im) (b₁ := z.re) (b₂ := (z + h).re)
          (t := t) (by simpa [Set.mem_uIcc] using ht)
        simpa using this
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                                        
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγ_cont.continuousOn) hmaps) using 1; rfl
                                                         
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
                                              
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
                        
      exact h_cont_sub.norm
                                            
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
                                    
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
                                           
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
                                          
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγv_cont.continuousOn) hmaps) using 1; rfl
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
                                              
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
                                           
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
                                             
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert (preTransparency := .instances) this using 1
    all_goals try with_reducible_and_instances rfl
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
                                             
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im]
  have hre : |(z + h).re - z.re| = |h.re| := by simp
  have him : |(z + h).im - z.im| = |h.im| := by simp

  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
                                 
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
                                 
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by

  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
                                                                                  
  rw [← add_mul] at h1

  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  rw [← norm_div] at h2

  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
                                                                
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
                                                                                         
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open _root_.Filter Topology

lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                                 
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
                               
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
                                        
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    simpa only [Function.comp_def, mul_zero, abs_zero] using h0.comp hS
                                            
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
                                                                      
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                 
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                                                      
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
                                                                                          
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
                                                    
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    ·                                        
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
                                      
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
                                                         
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open Classical

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by

  simp [If_taxicab]

lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                             
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
             
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                                        
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                           
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
                                                              
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
                                               
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                               
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                 
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
                                                                                
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    mem_closedBall_mono_radius (z:=w) (r:=r1) (R:=R') hw (le_of_lt hr1_lt_R')
                                                                  
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
                                           
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
                     
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
                                                        
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_right hδ_pos r1))
      simpa [R'] using this
                                       
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
                                             
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                         
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
                                
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
                                                                
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
                                                                                          
          simpa [g] using hdecomp)
        (hErr := by
                                                                         
          simpa using hErr)
                                               
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
                                                      
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
                                                  
    exact hasDerivWithinAt_congr_eqOn (f := If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
      (g := g) (s := s) (z := z) (f' := f z) hEq hz hWithin_g
                                 
  refine And.intro ?hdiff ?hderiv
  ·                                                                            
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  ·                                   
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z :=
      uniqueDiffWithinAt_closedBall_complex_of_mem (R := r1) hr1_pos (z := z) (hz := by simpa [s] using hz)
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD

open scoped Topology

lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
                                           
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.mono_closedBall R' hB hR'_lt_R
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
                                      
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := add_lt_add_right hδlt r1
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                                        
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'

  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
                                                         
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
                                                                       
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
                                                               
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
                                                                                
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
                
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
                                                           
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
                                        
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
                                                                                      
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
                                                                                     
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
                                                                                                    
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
                                                                           
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
                                           
    simpa using hHasDerivAt.deriv
                       
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz

lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
                                             
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                         
  unfold H_auxiliary at hH_const
                                          
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
                                                  
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
                                              
  rw [← heq, mul_comm]

lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                          
  simpa [norm_mul] using (congrArg norm hBform)

lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [modulus_of_exp_I hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]

lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
                                                     
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                                         
  rw [h_eq, Real.log_mul]
  ·                       
                                                                            
    simp
    apply hB_ne_zero
                                           
    rw [Metric.mem_closedBall, dist_self]
    linarith
  ·                                        
    exact Real.exp_ne_zero _

lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
                                     
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                    
  rw [h_sum]
                                                                       
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT2_LogDerivative
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ

  rw [zerosetKfR] at hρ
                                                                     
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_ofPred_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  ·                                                
    rw [← lem_ballDR R hR]
    exact lem_DRcompact R hR
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open _root_.Filter Metric _root_.Set Bornology _root_.Function

lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
                                
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
                                                                    
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
                                                  
  by_contra h_not_finite

  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
                                  
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf

  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open Classical

lemma lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ z := by
  classical
                       
  have hσ_closed_R1 : σ ∈ Metric.closedBall (0 : ℂ) R1 := hσ.1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  have hσ_closed1 : σ ∈ Metric.closedBall (0 : ℂ) 1 :=
    (Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)) hσ_closed_R1
  have hfσ : AnalyticAt ℂ f σ := h_f_analytic σ hσ_closed1
                             
  have h_order_finite : analyticOrderAt f σ ≠ ⊤ :=
    lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 σ hσ
                                                                      
  rcases (hfσ.analyticOrderAt_ne_top).mp h_order_finite with ⟨g, hgσ, hgσ_ne, h_eq⟩
                                                                                 
  have h_eq' : ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z := by
    refine h_eq.mono ?_
    intro z hz
    simpa [smul_eq_mul, analyticOrderNatAt] using hz
  exact ⟨g, hgσ, hgσ_ne, h_eq'⟩

theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
                                                                      
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                                                     
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball

theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (_hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR1
                                                  
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR1.2
                                                 
  exact h_f_zero_ne_zero h_f_zero_eq_zero

lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
                                                         
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
                                            
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros

theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
                          
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                                 
  exact lem_mod_pos_iff_ne_zero ρ h_ρ_ne_zero

lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
                                                    
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
                                                            
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                   
  have h_R1_pos : R1 > 0 := by
    linarith
                                                                   
  exact lem_inv_mono_decr (norm ρ) R1 h_abs_ρ_pos h_abs_ρ_le_R1

theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
                                             
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1

  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
                                
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                           
  linarith

lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
                                                                          
  unfold Bf
  rw [norm_mul]
                                                                                            
  rw [lem_mod_of_prod2]
                                                                                  
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
                                              
  rw [lem_mod_of_prod2]
                                                                        
  rw [div_mul_eq_mul_div]
                                                                                                    
  rw [mul_div_assoc]
                                                    
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
                                   
  rw [← norm_div, ← div_pow]
  congr 2
                                                  
  ring

lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                 
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
                                                              
  congr 2
  ext ρ
  rw [lem_abs_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                       
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
                                                                                  
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
                               
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
                                               
  congr 1
                                                         
  apply Finset.prod_congr rfl
  intro ρ hρ

  have h_ρ_ne_zero : ρ ≠ 0 := by
                                                             
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                  
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]

theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec

lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (_hR_lt_1 : R < 1) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≥ 1 := by
                                      
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                                    
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros]
                                     
  rw [hf0_eq_one, norm_one, one_mul]
                                                    
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat := by
    apply Finset.prod_le_prod
                       
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
                                            
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
                                                   
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
                                                    
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros

      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderAt f ρ).toNat
                                                          
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hR_lt_1
                                                     
  exact le_trans h_3_2_prod_ge_1 h_prod_ge
  assumption

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
                                                                              
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
                                                    
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
                                                  
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    rw [Complex.norm_div]

    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (hR1_pos.trans hR1_lt_R).ne'
      field_simp [hRne]

    rw [num_rewrite, Complex.norm_div]

    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    have hRpos : 0 < R := hR1_pos.trans hR1_lt_R
    have hnorm_denom : ‖z - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    simp [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hnorm_denom, hRpos.ne']

  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
                                        
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]

lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
                                             
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le

lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary

lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz

lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0

lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hBf0 : ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  classical
                                       
  set K := h_finite_zeros.toFinset
                                                        
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec
  have h_eval_prod :
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    rw [h_eval0, hf0_norm, one_mul]
                                             
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_ne0 ρ hρ_in)
                                          
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (fun ρ => (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ (analyticOrderAt f ρ).toNat ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat =
        ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
                                                                                       
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => (analyticOrderAt f ρ).toNat) (R/R1 : ℝ))
                                                                          
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
                                                
  set S : ℕ := ∑ ρ ∈ K, (analyticOrderAt f ρ).toNat
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
                                                     
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
                                                    
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
                                                                    
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) := by
    simp [S]
                                       
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this

lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
                                
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                      
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec hf_le_B
                                                      
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hBf0
                                                                         
  simpa using hres

lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
                                               
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)
                                    
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B)
                    
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
                                                               
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
                              
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
                           
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
             
  simpa [S, hlog_rpow] using hlog_le

lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat)) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      gcongr
      rw [mul_comm]
      exact h_div_log

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)

lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1

lemma lem_BCII {L : ℂ → ℂ} {r M r₁ : ℝ}
    (hr_pos : 0 < r)
    (hM_pos : 0 < M)
    (hr₁_pos : 0 < r₁)
    (hr₁_lt_r : r₁  < r)
    (hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U)
    (hL0 : L 0 = 0)
    (hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r₁) :
norm (deriv L z) ≤ (16 * M * r ^ 2) / ((r - r₁) ^ 3) := by
  apply borel_caratheodory_II hr_pos hM_pos hr₁_pos hr₁_lt_r hL_domain hL0 hre_L_le_M hz

lemma re_Lf_as_diff_of_log_mods
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) =
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) -
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)) := by
  intro z hz
                                                                                                                      
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw

  have h_log_exists := log_of_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_Bf_analytic h_Bf_ne_zero
  have h_choose_spec := Classical.choose_spec h_log_exists

  have h_Lf_def : Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec = Classical.choose h_log_exists := by
    unfold Lf
    simp only [B_f]

  rw [h_Lf_def]
  exact (h_choose_spec.2.2.2 z hz).symm

lemma log_Bf_le_log_B
    (B R R1 : ℝ)
    (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_pos : ∀ z, norm z ≤ R1 →
                0 < norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z))
    (h_Bf_bound : ∀ z, norm z ≤ R1 →
                  norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  intro z hz
  apply Real.log_le_log
  · exact h_Bf_pos z hz
  · exact h_Bf_bound z hz

lemma log_Bf_le_log_B2
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_bound : ∀ z, ‖z‖ ≤ R →
                  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ R1 →
      Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖) ≤ Real.log B := by
                                 
  apply log_Bf_le_log_B B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  ·                                                  
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    have hBf_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_mem
    exact norm_pos_iff.mpr hBf_ne_zero
  ·                                                    
    intro z hz
    have hz_le_R : ‖z‖ ≤ R := by linarith [hz, hR1_lt_R]
    exact h_Bf_bound z hz_le_R

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
                                                                              
  apply log_Bf_le_log_B2 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                       
  apply lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec
                                                               
  exact h_f_bound

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    0 ≤ Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖) := by
                                                          
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_Bf_ge_1 : 1 ≤ ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖ :=
    lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_log_mono := lem_log_mono_inc h_pos h_Bf_ge_1
  rw [Real.log_one] at h_log_mono
  exact h_log_mono

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) ≤ Real.log B := by
  intro z hz
                                                                                         
  rw [re_Lf_as_diff_of_log_mods r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z]
  ·                                           
                                                                 
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    linarith
  ·                                            
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)

lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r1 →
      norm (deriv (Lf (lt_trans hr1_pos hr1_lt_r : 0 < r) hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
                                        
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                                              
  let L := Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
                                                                   
  have h_analytic_nhd :=
    Lf_is_analytic r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                                             
  let U : Set ℂ :=
    { y | ∃ x ∈ Metric.closedBall (0 : ℂ) r, ∃ s : ℝ, 0 < s ∧ y ∈ Metric.ball x s ∧
        AnalyticOnNhd ℂ L (Metric.ball x s) }
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hyin, hAnaBall⟩
    have hnhds : Metric.ball x s ∈ nhds y := (Metric.isOpen_ball.mem_nhds hyin)
    exact Filter.mem_of_superset hnhds (by intro z hz; exact ⟨x, hxCB, s, hs_pos, hz, hAnaBall⟩)
  have hCB_subset : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    have hAt : AnalyticAt ℂ L x := h_analytic_nhd x hx
    rcases AnalyticAt.exists_ball_analyticOnNhd hAt with ⟨s, hs_pos, hAnaBall⟩
    have hx_in_ball : x ∈ Metric.ball x s := by
      simpa [Metric.mem_ball, dist_self] using hs_pos
    exact ⟨x, hx, s, hs_pos, hx_in_ball, hAnaBall⟩
  have hDiffU : DifferentiableOn ℂ L U := by
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hy_in, hAnaBall⟩
                                                          
    have hAt : AnalyticAt ℂ L y := hAnaBall y hy_in
    exact (AnalyticAt.differentiableAt hAt).differentiableWithinAt
                        
  have hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U :=
    ⟨U, hU_open, hCB_subset, hDiffU⟩
             
  have hL0 : L 0 = 0 := by
    simpa [L] using (Lf_at_0_is_0 r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
                                                
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound w hw'
                        
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
                                
  have hBC :=
    lem_BCII hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r hL_domain hL0 hre_L_le_M hz'
             
  simpa [L] using hBC

lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
                                                      
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
                                               
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
                                      
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
                        
  exact logDerivconst h_inv_ne_zero z

lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_sdiff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
                               
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
                                        
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
                                                                          
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
                                     
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
                              
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
                                   
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
                                            
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [abs_of_pos (hR1_pos.trans hR1_lt_R)]
                                         
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
                                                                     
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact mul_lt_mul_of_pos_right hR1_lt_R hposR
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  ·                                      
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
                                                 
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
                                                  
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
                                                       
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
                                               
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
             
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · convert (preTransparency := .instances) hdiff.pow ((analyticOrderAt f ρ).toNat) using 1
    all_goals try with_reducible_and_instances rfl

lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  ·                                
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  ·                                    
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
                                                                 
    have hdiff :=
      (DifferentiableAt.finsetProd (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
                                            
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
                 
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
                                                               
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  simpa using
    (logDerivmul (f:=f) (g:=fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) (z:=z)
      hf_diff hg_diff hf_ne hg_ne)

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
                  
  set K : Finset ℂ := h_finite_zeros.toFinset
                                                                    
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
                                                                              
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
                                                         
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
                                                           
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
                           
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
                                       
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
                                  
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
                                  
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
                               
  have hLf :=
    
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
                                   
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
                                                                              
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z) hfdiff hf_ne

  have hLf_eq_logDerivBf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by

    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
                                                               
    let B_f : ℂ → ℂ :=
      fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
    let log_exists := log_of_analytic
      (r1 := r) (R' := R1) (R := R)
      hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
      (B := B_f)
      (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
                f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
      (hB_ne_zero := by
        intro w hw
        exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
          f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
    have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
      (Classical.choose_spec log_exists).2.2.1
    have hderiv_Lf :
        deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                    h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
          = deriv B_f z / B_f z := by
                                                                            
      unfold Lf
                                                                                                       
      simpa using hderiv_all z hz_in_r
                                                  
    have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
      deriv_over_fun_is_logDeriv (g := B_f) z
               
    simpa [B_f] using hderiv_Lf.trans h_as_log

  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using
    (logDerivprod (K := h_finite_zeros.toFinset)
      (g := fun ρ w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
      (z := z) hdiff hne)

lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using
    (logDerivfunpow (g := fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) (z := z)
      (m := (analyticOrderAt f ρ).toNat) hdiff)

lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  simpa using
    (logDerivdiv (hh := hnum_diff) (hg := hden_diff) (hh_ne := hnum_nz) (hg_ne := hden_nz))

lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
                                                                         
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
                                                                     
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
                                                            
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
                                                  
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
                                                        
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
                                
  rw [h_div, h_num, h_den]

lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
                                                          
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                               
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
                                                  
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
                    
  ring

lemma rearrange_Lf_deriv :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) =
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                                               
  have h_final := Lf_deriv_final_formula hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  rw [h_final]
  ring

lemma target_inequality_setup :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
  ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := by
  intro z hz

  have hrearr := rearrange_Lf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz

  rw [hrearr]
  exact norm_sub_le _ _

lemma zerosetKfR_subset_closedBall {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} :
  zerosetKfR R1 hR1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma mem_zerosetKfR_norm_le {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) hR1 (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
                            
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 (by linarith) f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 (by linarith) f)
    exact (Iff.mp hiff) hρ
                                
  have hsum_le :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * ((analyticOrderAt f ρ).toNat : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1) (hR1 := by linarith)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (hR1 := by linarith) (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
                                          
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
                                                                              
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
                                                              
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ ((analyticOrderAt f ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderAt f ρ).toNat)
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
                                         
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
                                                  
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)))

  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz

  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
                                                  
  have h_exists : ∀ σ : ℂ, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g σ ∧ g σ ≠ 0 ∧
      (σ ∈ zerosetKfR R1 (by linarith) f →
        ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z) := by
    intro σ
    by_cases hσ : σ ∈ zerosetKfR R1 (by linarith) f
    ·                                             
      have hex := lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero σ hσ
      obtain ⟨g, hg_at, hg_ne, h_eq⟩ := hex
      exact ⟨g, hg_at, hg_ne, fun _ => h_eq⟩
    ·                                            
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · exact analyticAt_const
      · norm_num
      · intro h_contra
        contradiction
                                                 
  let h_σ : ℂ → (ℂ → ℂ) := fun σ => Classical.choose (h_exists σ)
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z := by
    intro σ hσ
    have spec := Classical.choose_spec (h_exists σ)
    exact ⟨spec.1, spec.2.1, spec.2.2 hσ⟩
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero h_f_zero h_finite_zeros h_σ h_f_bounded_alt h_σ_spec

  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec :
      ∀ σ ∈ zerosetKfR R1 (by linarith) f,
        AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ,
          f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  intro z hz

  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]

  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  have hineq :=
    target_inequality_setup hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_in_r

  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros) (h_σ := h_σ) (h_σ_spec := h_σ_spec)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    z hz_abs

  have hLf : ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by

    convert (preTransparency := .instances) h_BC using 1
                                                                                             
    ring

  exact le_trans hineq (add_le_add hLf hsum)

lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
                                                            
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
                                                                                  
  rw [← add_mul] at h_bound
  exact h_bound

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT3_RiemannZeta
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open scoped BigOperators Topology

lemma hasProd_nnreal_of_coe {i : Type*} (g : i → NNReal) (b : NNReal) (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  exact HasProd.of_coe_hasProd g b h

lemma multipliable_real_to_nnreal {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (h_mult : Multipliable f) : Multipliable (fun i => ⟨f i, le_of_lt (hpos i)⟩ : i → NNReal) := by
                                         
  obtain ⟨a, ha⟩ := h_mult
                                                            
  have ha_nonneg : 0 ≤ a := hasProd_nonneg_of_pos f hpos a ha
                                   
  let a_nnreal : NNReal := ⟨a, ha_nonneg⟩
                                                           
  have h_coe_eq : (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) = f := by
    ext i
    rfl
                                                             
  have ha_coe : HasProd (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) (a_nnreal : ℝ) := by
    rw [h_coe_eq]
    simp only [a_nnreal]
    exact ha
                                                        
  have ha_nnreal : HasProd (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal :=
    hasProd_nnreal_of_coe (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal ha_coe
                                                  
  exact ⟨a_nnreal, ha_nnreal⟩

lemma abs_zeta_inequality (t : ℝ) :
  ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤
  ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by

  have h_pos_left : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    apply add_pos zero_lt_one
                                                             
    apply Real.rpow_pos_of_pos
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))

  have h_pos_right : ∀ p : ℙ, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    intro p
    apply inv_pos.mpr
                                                            
    rw [norm_pos_iff]
    exact condp32 p t

  have h_mult_left : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹) :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)

  have h_mult_right : Multipliable (fun p : ℙ => (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹) := by
    let s := ((3 : ℝ) / 2) + t * Complex.I
    have hs : 1 < s.re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero]
      norm_num
                                               
    have h_euler := (zetaEulerprod s hs).1
    have h_nonzero : ∀ p : ℙ, 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := fun p => condp32 p t
    exact multipliable_complex_abs_inv (fun p : ℙ => ((p : ℕ) : ℂ) ^ (-s)) h_euler h_nonzero

  let f : ℙ → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : ℙ → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹, le_of_lt (h_pos_right p)⟩

  have hf : Multipliable f := multipliable_real_to_nnreal _ h_pos_left h_mult_left
  have hg : Multipliable g := multipliable_real_to_nnreal _ h_pos_right h_mult_right

  have h_pointwise : ∀ p : ℙ, f p ≤ g p := by
    intro p
    simp only [f, g]
    exact abs_term_inv_bound p t

  have h_nnreal_ineq : ∏' p, f p ≤ ∏' p, g p := prod_inequality f g hf hg h_pointwise

  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal_ineq

  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    rfl

  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    rfl

  rw [h_eq_f, h_eq_g] at h_convert
  exact h_convert

theorem zeta_lower_bound (t : ℝ) :
  norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) ≤
    norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp only [Complex.add_re, Complex.mul_I_re]
    norm_num
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := abs_zeta_ratio_eval
    _ ≤ ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ :=
          abs_zeta_inequality t
    _ = norm (riemannZeta (((3 : ℝ) / 2 : ℂ) + t * Complex.I)) := by
          simpa using (abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs).symm

lemma zeta_low_332 : ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, a ≤ norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  use norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
  exact ⟨zeta332pos, zeta_lower_bound⟩

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

open Metric _root_.Set _root_.Filter _root_.Asymptotics BigOperators

lemma zetaanalOnnot1 : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  apply DiffAtallanalOnNhd
  · apply isOpen_compl_singleton
  · exact zetadiffAtnot1

lemma zetaanalOnD1c (t : ℝ) (ht : |t| > 1) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (3/2 + I * t : ℂ) 1) := by
  apply zetaanalOnnot1.mono
  exact D1cinTt t ht

lemma re_real_add_I_mul_gt (a b : ℝ) (h : a > 1) : (a + I * b).re > 1 := by
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex_I_mul_ofReal_re]
  simp
  exact h

lemma zetacnot0 (t : ℝ) : riemannZeta (3/2 + I * t) ≠ 0 := by
  apply sigmageq1
  apply re_real_add_I_mul_gt
  norm_num

lemma fc_zeros (r : ℝ) (_h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
  (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  ext ρ'; constructor
  · intro hmem
    rcases hmem with ⟨hball, hzero⟩
                                                                     
    have hprod : f (ρ' + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using hzero
    have hnum0 : f (ρ' + c) = 0 := by
      rcases mul_eq_zero.mp hprod with hnum | hinv
      · exact hnum
      · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
        exact (this hinv).elim
    refine ⟨ρ' + c, ?_, ?_⟩
    ·                                   
      have hdist0 : dist ρ' (0 : ℂ) ≤ r := by simpa [mem_closedBall] using hball
      have hdist1 : dist (ρ' + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist0
      have hmem_ball : ρ' + c ∈ closedBall c r := by
        simpa [mem_closedBall] using hdist1
      exact And.intro hmem_ball hnum0
    ·                     
      simp
  · intro him
    rcases him with ⟨y, hy_mem, hy_eq⟩
                                           
    subst hy_eq
    rcases hy_mem with ⟨hy_ball, hy_zero⟩
    refine And.intro ?_ ?_
    ·                            
      have hdist : dist y c ≤ r := by simpa [mem_closedBall] using hy_ball
      have hdist0 : dist (y - c) (0 : ℂ) ≤ r := by
        simpa [Complex.dist_eq, sub_zero] using hdist
      simpa [mem_closedBall] using hdist0
    ·                             
      simp [sub_add_cancel, hy_zero]

lemma fc_m_order (r : ℝ) (_h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    {ρ' : ℂ} (_hρ' : ρ' ∈ zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) :
    analyticOrderAt (fun z => f (z + c) / f c) ρ' = analyticOrderAt f (ρ' + c) := by
  classical
                                     
  set g0 : ℂ → ℂ := fun z => f (z + c) with hg0
                                                                                                 
  have hconst : analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' = analyticOrderAt g0 ρ' := by
    have hne : (1 / f c) ≠ 0 := one_div_ne_zero h_nonzero
    simpa using (analyticOrderAt_mul_const_eq (f := g0) (a := (1 / f c)) (z0 := ρ') hne)
  have hconst_rewrite : analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := by
    have : (fun z => f (z + c) / f c) = (fun z => g0 z * (1 / f c)) := by
      funext z; simp [g0, div_eq_mul_inv, mul_comm]
    simp [this]
                                        
  have htrans : analyticOrderAt g0 ρ' = analyticOrderAt f (ρ' + c) := by
                                          
    by_cases hfA : AnalyticAt ℂ f (ρ' + c)
    ·                                                          
      have h_add : AnalyticAt ℂ (fun z : ℂ => z + c) ρ' := by
        simpa using! (AnalyticAt.add (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) ρ')
                                    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) ρ'))
      have hgA : AnalyticAt ℂ g0 ρ' := by
        have : AnalyticAt ℂ f ((fun z : ℂ => z + c) ρ') := by simpa using hfA
        simpa [g0, hg0] using! (AnalyticAt.comp (g := f) (f := fun z : ℂ => z + c) (x := ρ') this h_add)
                                                         
      by_cases hgez : (∀ᶠ z in nhds ρ', g0 z = 0)
      ·                                                                                      
        have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (ContinuousAt.sub (continuousAt_id : ContinuousAt (fun w : ℂ => w) (ρ' + c))
                                        (continuousAt_const : ContinuousAt (fun _ : ℂ => c) (ρ' + c)))
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hEfw : ∀ᶠ w in nhds (ρ' + c), f w = 0 := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c) = 0 := hT_sub.eventually hgez
                                       
          simpa [g0, hg0, sub_add_cancel] using this
                                                                       
        have hg_top : analyticOrderAt g0 ρ' = ⊤ :=
          (analyticOrderAt_eq_top (f := g0) (z₀ := ρ')).2 hgez
        have hf_top : analyticOrderAt f (ρ' + c) = ⊤ :=
          (analyticOrderAt_eq_top (f := f) (z₀ := ρ' + c)).2 hEfw
        simp [hg_top, hf_top]
      ·                                                                       
        have h_exists := (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hgA).mpr hgez
        rcases h_exists with ⟨n, φ, hφA, hφ_ne, hevent⟩
                                         
        have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (ContinuousAt.sub (continuousAt_id : ContinuousAt (fun w : ℂ => w) (ρ' + c))
                                        (continuousAt_const : ContinuousAt (fun _ : ℂ => c) (ρ' + c)))
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hevent_w : ∀ᶠ w in nhds (ρ' + c), f w
              = (w - (ρ' + c)) ^ n * ((fun w => φ (w - c)) w) := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c)
                    = ((w - c) - ρ') ^ n * φ (w - c) :=
            hT_sub.eventually hevent
                                                                         
          refine this.mono ?_
          intro w hw
          have hsubsimp : (w - c) - ρ' = w - (ρ' + c) := by ring
          simpa [g0, hg0, hsubsimp] using hw
                                                                               
        have hψA : AnalyticAt ℂ (fun w => φ (w - c)) (ρ' + c) := by
          have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) := by
            simpa using! (AnalyticAt.sub (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (ρ' + c))
                                        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) (ρ' + c)))
          have hφA_at : AnalyticAt ℂ φ ((fun w : ℂ => w - c) (ρ' + c)) := by simpa using hφA
          simpa using! (AnalyticAt.comp (g := φ) (f := fun w => w - c) (x := (ρ' + c)) hφA_at h_subA)
        have hψ_ne : (fun w => φ (w - c)) (ρ' + c) ≠ 0 := by
                                      
          simpa using hφ_ne
                                                                   
        have hg_eq_n : analyticOrderAt g0 ρ' = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := g0) (z₀ := ρ') hgA).mpr
            ⟨φ, hφA, hφ_ne, hevent⟩
        have hf_eq_n : analyticOrderAt f (ρ' + c) = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := f) (z₀ := ρ' + c) hfA).mpr
            ⟨(fun w => φ (w - c)), hψA, hψ_ne, hevent_w⟩
        simp [hg_eq_n, hf_eq_n]
    ·                                                                        
      have hg_not : ¬ AnalyticAt ℂ g0 ρ' := by
        intro hgA
                                                                      
        have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (AnalyticAt.sub (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (ρ' + c))
                                      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) (ρ' + c)))
        have hgA_at : AnalyticAt ℂ g0 ((ρ' + c) - c) := by simpa using hgA
        have hcomp := (AnalyticAt.comp (g := g0) (f := fun w => w - c)
                          (x := (ρ' + c)) hgA_at h_subA)
                                    
        have : AnalyticAt ℂ (fun w : ℂ => g0 (w - c)) (ρ' + c) := by simpa using! hcomp
        have : AnalyticAt ℂ f (ρ' + c) := by
          simpa [g0, hg0, sub_add_cancel] using this
        exact hfA this
                                                                       
      simp [analyticOrderAt, hfA, hg_not]
                                                                                      
  calc
    analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := hconst_rewrite
    _ = analyticOrderAt g0 ρ' := hconst
    _ = analyticOrderAt f (ρ' + c) := htrans

lemma shifted_zeros_correspondence (R1 : ℝ) (hR1 : R1 > 0) (c z : ℂ)
    (f : ℂ → ℂ) (h_nonzero : f c ≠ 0) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    (hfin_orig : (zerosetKfRc R1 c f).Finite)
    (hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)).Finite) :
    ∑ ρ ∈ hfin_orig.toFinset, ((analyticOrderAt f ρ).toNat : ℂ) / (z - ρ) =
    ∑ ρ' ∈ hfin_shift.toFinset, ((analyticOrderAt (fun u => f (u + c) / f c) ρ').toNat : ℂ) / ((z - c) - ρ') := by
                                                              
  have h_bij : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
    fc_zeros R1 hR1 c f h_nonzero h_analytic

  apply Finset.sum_bij (fun ρ _ => ρ - c)

  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ ⊢
    rw [h_bij]
    use ρ, hρ

  · intro ρ₁ hρ₁ ρ₂ hρ₂ h_eq
                                           
    have : ρ₁ = ρ₁ - c + c := by ring
    rw [this, h_eq]
    ring

  · intro ρ' hρ'
    simp only [Set.Finite.mem_toFinset] at hρ'
    rw [h_bij] at hρ'
    obtain ⟨ρ, hρ_mem, hρ_eq⟩ := hρ'
    use ρ
    simp only [Set.Finite.mem_toFinset]
    exact ⟨hρ_mem, hρ_eq⟩

  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ
                                                   
    have h_shift_mem : ρ - c ∈ zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c) := by
      rw [h_bij]
      use ρ, hρ

    have h_order := fc_m_order R1 hR1 c f h_nonzero h_analytic h_shift_mem
                            
    have h_add : (ρ - c) + c = ρ := by ring
    rw [h_add] at h_order
    rw [← h_order]
                                                               
    ring

lemma final_ineq2
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ < B)
    (hfin : (zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c)).Finite) :
    ∀ z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c),
    ‖(deriv (fun z => f (z + c) / f c) z / (f (z + c) / f c)) - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt (fun w => f (w + c) / f c) ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖f c‖) := by
  intro z hz

  let g : ℂ → ℂ := fun w => f (w + c) / f c

  have hR_pos : 0 < R := by linarith [hr1pos, hr1_lt_r, hr_lt_R1, hR1_lt_R]
  have hR1_pos : 0 < R1 := by linarith [hr1pos, hr1_lt_r, hr_lt_R1]
  have h_norm_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h_nonzero

  have h_fc_bound_at_c : ‖f c‖ < B := by
    apply h_bound
    rw [mem_closedBall, dist_self]
    exact le_of_lt hR_pos

  have h_B_div_gt_one : 1 < B / ‖f c‖ := by
    rw [one_lt_div h_norm_pos]
    exact h_fc_bound_at_c

  have h_g_analytic : ∀ w ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ g w :=
    (fc_analytic_normalized c f h_analytic h_nonzero).1

  have h_g_zero : g 0 = 1 :=
    (fc_analytic_normalized c f h_analytic h_nonzero).2

  have h_g_bound : ∀ w ∈ closedBall (0 : ℂ) R, ‖g w‖ ≤ B / ‖f c‖ := by
    apply fc_bound B hB R hR_pos hR c f h_nonzero
    intro w hw
    exact le_of_lt (h_bound w hw)

  have h_zeroset_equiv : zerosetKfRc R1 (0 : ℂ) g = zerosetKfR R1 hR1_pos g := by
    ext ρ
    simp only [zerosetKfRc, zerosetKfR, mem_ofPred_eq, mem_closedBall, Complex.dist_eq, sub_zero]

  have h_g_finite : (zerosetKfR R1 hR1_pos g).Finite := by
    rwa [← h_zeroset_equiv]

  have h_σ_exists : ∃ h_σ : ℂ → (ℂ → ℂ), ∀ σ ∈ zerosetKfR R1 hR1_pos g,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ w in nhds σ, g w = (w - σ) ^ (analyticOrderAt g σ).toNat * h_σ σ w := by
                                                                  
    classical
    let h_σ : ℂ → (ℂ → ℂ) := fun σ =>
      if hσ : σ ∈ zerosetKfR R1 hR1_pos g
      then Classical.choose (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)
      else fun _ => 0
    use h_σ
    intro σ hσ
    simp only [h_σ, dif_pos hσ]
    exact Classical.choose_spec (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)

  obtain ⟨h_σ, h_σ_spec⟩ := h_σ_exists

  have := final_ineq1 (B / ‖f c‖) h_B_div_gt_one r1 r R R1 hr1pos hr1_lt_r hr_lt_R1 hR1_lt_R hR
    g h_g_analytic h_g_zero h_g_finite h_σ_spec h_g_bound z

  have hz_domain : z ∈ closedBall (0 : ℂ) r1 \ zerosetKfR R1 hR1_pos g := by
    rw [h_zeroset_equiv] at hz
    exact hz

  exact this hz_domain

lemma log_Deriv_Expansion_Zeta (t : ℝ) (ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    let c := (3/2 : ℂ) + I * t
    ∀ B > 1, (∀ z ∈ closedBall c R, ‖riemannZeta z‖ < B) →
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
  intro c B hB h_bound hfin z hzmem
                                 
  have ht1 : |t| > 1 := lt_trans (by norm_num : (1 : ℝ) < 2) (by simpa using ht)
                                                                        
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := by
    simpa [c] using zetaanalOnD1c t ht1
  have hζ_c_ne : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
                                                                           
  have hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c)).Finite := by
    have h_bij := fc_zeros R1 hR1_pos c riemannZeta hζ_c_ne hζ_analytic
    have himg : ((fun ρ => ρ - c) '' (zerosetKfRc R1 c riemannZeta)).Finite := hfin.image _
    simpa [h_bij] using himg
                                                            
  have hz0mem : (z - c) ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c) := by
    have hiff := DminusK r1 R1 hr1_pos hR1_pos c riemannZeta hζ_analytic hζ_c_ne (z - c)
    exact (hiff).mpr (by simpa [sub_add_cancel] using hzmem)
                                                                  
  have hineq0 :=
    (final_ineq2 B hB r1 r R R1 hr1_pos hr1_lt_r hr_lt_R1 hR1_lt_R hR_lt_1 c riemannZeta
      hζ_analytic hζ_c_ne h_bound hfin_shift) (z - c) hz0mem
                                              
  rcases hzmem with ⟨hz_ball, hz_notin⟩
  have hr1_lt_R1' : r1 < R1 := lt_trans hr1_lt_r hr_lt_R1
  have hz_in_ball_R1 : z ∈ closedBall c R1 := by
    have hz_le_r1 : dist z c ≤ r1 := by simpa [mem_closedBall] using hz_ball
    have hr1_le_R1 : r1 ≤ R1 := le_of_lt hr1_lt_R1'
    have hz_le_R1 : dist z c ≤ R1 := le_trans hz_le_r1 hr1_le_R1
    simpa [mem_closedBall] using hz_le_R1
  have hzeta_ne : riemannZeta z ≠ 0 := by
    intro hz0
    exact hz_notin ⟨hz_in_ball_R1, hz0⟩
                                                    
  have hcancel_frac : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta z := by
    have hc : riemannZeta c ≠ 0 := hζ_c_ne
    have hy : riemannZeta z ≠ 0 := hzeta_ne
    simpa using (frac_cancel_const (x := deriv (fun x => riemannZeta (x + c)) (z - c))
              (y := riemannZeta z) (c := riemannZeta c) hc hy)
  have hcancel_all : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv riemannZeta z / riemannZeta z := by
    simpa [deriv_comp_add_const, sub_add_cancel] using hcancel_frac
                                                                        
  have hineq1 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin_shift.toFinset,
            ((analyticOrderAt (fun u => riemannZeta (u + c) / riemannZeta c) ρ).toNat : ℂ)
              / ((z - c) - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hcancel_all] using hineq0
                                                                
  have hsum_eq := shifted_zeros_correspondence R1 hR1_pos c z riemannZeta hζ_c_ne hζ_analytic hfin hfin_shift
                                                                        
  have hineq2 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin.toFinset,
            ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hsum_eq] using hineq1
                                                
  simpa [logDerivZeta] using hineq2

lemma zeta32lower : ∃ a > 0, ∀ t : ℝ, ‖riemannZeta (3/2 + I * t)‖ ≥ a := by
  rcases zeta_low_332 with ⟨a, ha_pos, hbound⟩
  refine ⟨a, ha_pos, ?_⟩
  intro t
  simpa [mul_comm] using! (hbound t)

lemma zeta32lower_log : ∃ A > 1, ∀ t : ℝ,
    Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) ≤ A := by
  obtain ⟨a, ha_pos, hbound⟩ := zeta32lower
  refine ⟨max (2 : ℝ) (Real.log (1 / a)), ?_, ?_⟩
  · have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (2 : ℝ) ≤ max (2 : ℝ) (Real.log (1 / a)) := by exact le_max_left _ _
    exact lt_of_lt_of_le h1 h2
  · intro t
    set x := ‖riemannZeta (3/2 + I * t)‖ with hx
    have hax : a ≤ x := by
      simpa [hx] using (hbound t)
    have hxpos : 0 < x := lt_of_lt_of_le ha_pos hax
    have hxy : 1 / x ≤ 1 / a := by
                                               
      have := one_div_le_one_div_of_le ha_pos hax
                                          
      simpa [hx] using this
    have hxpos' : 0 < 1 / x := one_div_pos.mpr hxpos
    have hlog : Real.log (1 / x) ≤ Real.log (1 / a) :=
      Real.log_le_log hxpos' hxy
    have : Real.log (1 / x) ≤ max (2 : ℝ) (Real.log (1 / a)) :=
      le_trans hlog (le_max_right _ _)
    simpa [hx] using this

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ZetaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  all_goals try with_reducible_and_instances rfl
  rw [neg_div]

open _root_.ArithmeticFunction (vonMangoldt)

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Z0
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by

  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO

  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by

    apply tendsto_inf.mpr
    constructor
    ·                                     
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
                                                             
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
                                                                     
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds

      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    ·                                                  
                                                      
      simp
                                                  
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  have h_comp := h_F_bigO.comp_tendsto h_tendsto

  convert (preTransparency := .instances) h_comp using 1
  all_goals try with_reducible_and_instances rfl
  ext delta
                                                           
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop
  all_goals rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT4_ZeroFreeRegion
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


def ZetaZerosNearPoint (t : ℝ) : Set ℂ := { ρ : ℂ | ρ ∈ zeroZ ∧ ‖ρ - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) }

lemma ZetaZerosNearPoint_finite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := by
                                  
  let c : ℂ := (3/2 : ℂ) + t * Complex.I
  let R : ℝ := (5/6 : ℝ)
  have hRpos : 0 < R := by norm_num

  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := by
                                                               
    intro s
    rcases eq_or_ne s 1 with rfl | hs
    ·                                                                                                
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                             
        filter_upwards [self_mem_nhdsWithin] with t ht
                                                                              
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                           
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) s :=
          (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta s :=
          (differentiableAt_riemannZeta hs)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hs] with u hu using by
        simp [H, Function.update_of_ne hu]

  by_cases hPoleIn : ‖1 - c‖ ≤ R
  ·                                                         
    let g : ℂ → ℂ := fun z => H (z + c)
                                                                                                   
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
                                     
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
                                                             
      exact riemannZeta_ne_zero_of_one_le_re (by
                        
        have : (1 : ℝ) < c.re := hgt
        exact le_of_lt this)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
                                                           
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
                                                             
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr (by
                                 
        exact hcne1)) hzeta_c_ne
                                                  
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                                                                        
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
                                          
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
                                                      
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
                                          
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by simp [hform, hzeroζ]
      exact ⟨hball, hzero'⟩
                                                                                                 
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
                                        
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
                                                                    
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
                                                                                    
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
                                                
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset
  ·                                             
    let g : ℂ → ℂ := fun z => H (z + c)
                                          
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hgt)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
                                      
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr hcne1) hzeta_c_ne
                                          
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                     
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
                                                   
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by
        calc
          g (ρ - c) = (ρ - 1) * riemannZeta ρ := hform
          _ = (ρ - 1) * 0 := by simp [hzeroζ]
          _ = 0 := by simp
      exact ⟨hball, hzero'⟩
                            
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset

lemma lem_sigmale1Zt (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) : rho1.re ≤ 1 := by
                                                                    
  have h1 : rho1 ∈ zeroZ := h_rho1_in_Zt.1
                                                                  
  have h2 : riemannZeta rho1 = 0 := h1
                                                       
  have h3 : rho1 = rho1.re + rho1.im * Complex.I := by simp [Complex.re_add_im]
                                         
  rw [h3] at h2
                           
  exact lem_sigmale1 rho1.re rho1.im h2

lemma zerosetKfRc_eq_ZetaZerosNearPoint (t : ℝ) :
  zerosetKfRc (5/6 : ℝ) ((3/2 : ℂ) + t * Complex.I) riemannZeta = ZetaZerosNearPoint t := by
  ext ρ; constructor
  · intro h
    rcases h with ⟨hball, hzero⟩
    refine ⟨?hz, ?hnorm⟩
    · simpa [zeroZ] using hzero
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hball
  · intro h
    rcases h with ⟨hz, hnorm⟩
    refine ⟨?hball, ?hzero⟩
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hnorm
    · simpa [zeroZ] using hz

lemma s_notin_ZetaZerosNearPoint (δ t : ℝ) (hδ_pos : 0 < δ) :
  ((1 : ℂ) + δ + t * Complex.I) ∉ ZetaZerosNearPoint t := by
  intro hmem
  have hz0 : riemannZeta ((1 : ℂ) + δ + t * Complex.I) = 0 := hmem.1
  have : ((1 : ℂ) + δ + t * Complex.I).re = 1 + δ := by simp
  have hpos : (1 : ℝ) < 1 + δ := by linarith
  have hnonzero := lem_sigmage1 (1 + δ) t hpos
  exact hnonzero (by simpa using hz0)

lemma lem_sumrho1 (t : ℝ) (δ : ℝ) (_hdelta_pos : δ > 0) (_hdelta_lt1 : δ < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
        (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
    (fun rho1 : ℂ =>
                    (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1)).re) := by
  exact lem_Realsum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) _

lemma lem_sumrho2 (t : ℝ) (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
        (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
    (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1)).re) := by
  rw [Complex.re_sum]

lemma lem_1deltatrho1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (_h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1) = ((1 : ℝ) + delta - rho1.re) + (t - rho1.im) * Complex.I := by
                                                           
  conv_lhs => rw [← Complex.re_add_im rho1]

  simp only [sub_add_eq_sub_sub]
                                                      
  ring_nf
                                                               
  simp only [Complex.ofReal_one]
  ring

lemma lem_Re1deltatrho1 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re = (1 : ℝ) + delta - rho1.re := by
                                                   
  rw [lem_1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]

  rw [Complex.add_re]
                                      
  rw [Complex.mul_I_re]
             
  simp

lemma lem_Re1delta1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 : ℝ) + delta - rho1.re ≥ delta := by
                                            
  have h_rho1_re_le_1 : rho1.re ≤ 1 := lem_sigmale1Zt t rho1 h_rho1_in_Zt
                               
  have h_nonneg : 1 - rho1.re ≥ 0 := by linarith
                                                                              
  linarith

lemma lem_Re1deltatge (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := by
                                                     
  rw [lem_Re1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]
                                                      
  exact lem_Re1delta1 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatneq0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re > 0 := by
                                                               
  have h_ge_delta : ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := lem_Re1deltatge delta hdelta t rho1 h_rho1_in_Zt
                                                                         
  linarith [hdelta]

lemma lem_Re1deltatge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 / ((1 : ℂ) + delta + t * Complex.I - rho1)).re ≥ 0 := by
                                                                      
  apply le_of_lt
  apply lem_Re1zge0
                                                          
  exact lem_Re1deltatneq0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatge0m (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (_hdelta_lt_1 : delta < 1)
  (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
    (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 0 := by
                                                     
  let n := (analyticOrderAt riemannZeta rho1).toNat
  let z := ((1 : ℂ) + delta + t * Complex.I) - rho1

  have h_eq : (n : ℂ) / z = n • (1/z) := by
    rw [nsmul_eq_mul]
    simp [div_eq_mul_inv]

  rw [h_eq, Complex.re_nsmul]

  apply nsmul_nonneg
  exact lem_Re1deltatge0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Z1split (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) (rho : ℂ)
  (_h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) =
    (((analyticOrderAt riemannZeta rho).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
    Finset.sum ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
  classical
  set s := Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)
  set f := fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re
  have hmem : rho ∈ s := by
    simpa [s, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using h_rho_in_Zt
                                                            
  have h_decomp : ∑ x ∈ s, f x = f rho + ∑ x ∈ s.erase rho, f x := by
    rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase rho s)]
    simp
  exact h_decomp

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  classical
                           
  have hsplit :=
    lem_Z1split delta hdelta_pos hdelta rho h_rho_in_zeroZ h_rho_in_Zt
                                    
  rw [hsplit]
                                       
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact hz1_ne (by simpa [h] using! h_rho_in_zeroZ)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta_of_ne_one h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ (analyticOrderAt riemannZeta rho).toNat :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa using! h_rho_in_zeroZ) hNotEv
  have ha_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho).toNat : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ (((((analyticOrderAt riemannZeta rho).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
                               
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho).toNat : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
                                        
  have hsum_nonneg :
      0 ≤ Finset.sum
        ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ =>
          (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
                                     
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
                    
    have hne1 : rho1 ≠ (1 : ℂ) := by
      intro h
      have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
      have hzero1 : riemannZeta rho1 = 0 := hZt.1
      exact hz1_ne (by simpa [h] using hzero1)
                           
    have hAnal1 : AnalyticAt ℂ riemannZeta rho1 := analyticAt_riemannZeta_of_ne_one hne1
    have hNotEv1 : ¬ (∀ᶠ z in nhds rho1, riemannZeta z = 0) :=
      riemannZeta_not_eventually_zero_of_ne_one hne1
    have hzero1 : riemannZeta rho1 = 0 := hZt.1
    have horder1 : 1 ≤ (analyticOrderAt riemannZeta rho1).toNat :=
      analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal1 hzero1 hNotEv1
    have ha1_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho1).toNat : ℝ) := by exact_mod_cast horder1
                       
    have hz1_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re :=
      lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
                                           
    have hge :
        (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≤
          (((((analyticOrderAt riemannZeta rho1).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1))).re := by
      simpa [ge_iff_le] using
        (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho1).toNat : ℝ)
          ((((1 : ℂ) + delta + rho.im * Complex.I) - rho1)) ha1_real hz1_nonneg)
                                                       
    exact le_trans hz1_nonneg hge
                           
  have h := add_le_add hfirst hsum_nonneg
                             
  simpa using h

lemma lem_1deltatrho0 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by

  calc (1 : ℂ) + delta + rho.im * Complex.I - rho
    = (1 : ℂ) + delta + rho.im * Complex.I - (rho.re + rho.im * Complex.I) := by rw [Complex.re_add_im]
  _ = (1 : ℂ) + delta - rho.re := by ring
  _ = ((1 : ℝ) + delta - rho.re : ℂ) := by norm_cast

lemma lem_1delsigReal2 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta - rho.re)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                                           
  have h_eq : (1 : ℂ) + delta - rho.re = (1 + delta - rho.re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]

  rw [h_eq]

  rw [Complex.div_ofReal_re]

  rw [Complex.one_re]

lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (hdelta : delta > 0)  (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                      
  rw [lem_1deltatrho0 delta hdelta rho h_rho_in_zeroZ]
                               
  exact lem_1delsigReal2 delta hdelta rho h_rho_in_zeroZ

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re) ≥
1 / ((1 : ℝ) + delta - rho.re) := by
                                                    
  have h1 := lem_Z1splitge delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt
                                                                                  
  have h2 := lem_re_inv_one_plus_delta_minus_rho_real delta hdelta rho h_rho_in_zeroZ
                        
  rw [← h2]
  exact h1

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I) (h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)) ).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
                                                                                   
  rw [lem_sumrho1 t delta hdelta hdelta_lt_1]

  have h_rho_im : rho.im = t := by
    rw [h_rho_eq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im]
  have h_rho_re : rho.re = sigma := by
    rw [h_rho_eq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re]

  have h_rho_in_Zt' : rho ∈ ZetaZerosNearPoint rho.im := by
    rw [h_rho_im]
    exact h_rho_in_Zt

  have h_bound := lem_Z1splitge2 delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt'

  convert (preTransparency := .instances) h_bound using 1
                                                       
  simp_rw [← h_rho_im]
                                                             
  rw [h_rho_re]

lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re

  have h : (x + y * I).re = x := by
    rw [Complex.add_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
                                                                           
  right
  exact Complex.I_re

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
                                                                                                
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    vonMangoldt_LSeriesSummable (x + y * I) h_re_gt_one

  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  exact h_hasSum_re.summable

lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
                                              
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
                                                         
  exact lem_exprule n hn (-x : ℂ) (-(y * I))

lemma LSeriesSummable_to_explicit_summable (x y : ℝ) (_hx : 1 < x) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) → Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  intro h_summable

  have h_vm_zero : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    simp

  have h_eq : ∀ n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n =
    (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
    intro n
                                                     
    rw [LSeries.term_def₀ h_vm_zero]

    rw [← Complex.cpow_eq_pow]

    by_cases hn : n = 0
    ·                                
      simp [hn]
    ·                                    
      have hn_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [lem_nxy n hn_ge x y]
      ring

  have h_term_summable : Summable (fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n) := by
    exact h_summable

  convert (preTransparency := .instances) h_term_summable using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact (h_eq n).symm

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                              
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
                                                
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  exact lem_realbw b (Complex.cpow (n : ℂ) (-(y * I)))

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
                                                   
  rw [lem_nxy n hn x y]

  rw [← mul_assoc]

  rw [RealLambdaxy n x y hn hx]

  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  rw [h_cpow, h_I]

  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
                                                                           
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
                                              
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
                                             
  convert (preTransparency := .instances) h1 using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
                                             
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
                                           
  have hO := Z0bound
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                             
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  exact le_trans hnorm_le_c (le_max_left _ _)

lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
                                                 
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
                          
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
                                                       
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg_of_nonneg hnn
                                                                                
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  ·                                        
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
             
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  ·          
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    ·                              
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
                 
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    ·                                                     
                      
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
                                                           
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
                                      
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
                                             
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
                              
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg_of_nonneg (vonMangoldt_rpow_nonneg x)
                                                                      
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
                                                                 
      have hx_ge_two : 2 ≤ x := by
                                     
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
                                                   
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            rpow_neg_antitone hn' hx_ge_two
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
                                   
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
                                                
        have h_nonneg_x : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) :=
          vonMangoldt_rpow_nonneg x
        exact tsum_le_of_nonneg_of_le h_summ_x h_summ_2 h_nonneg_x h_le_2
                                        
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
                                                                
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
                     
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C

lemma Z0boundRe_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) ≤ C := by
                                                 
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C
  constructor
  · exact hCpos
  · intro δ hδ
                                                    
    have h_bound := hC δ hδ
    exact le_trans (Complex.re_le_norm _) h_bound

lemma Z0boundRe_const2 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) ≤ C := by
                                           
  rcases Z0boundRe_const with ⟨C, hC_pos, hC⟩
  use C, hC_pos
  intro δ hδ
  have h_sub_re : ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) =
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) := by
    rw [Complex.sub_re]
    rfl
  rw [← h_sub_re]
  exact hC δ hδ

lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
                                                                        
  rcases Z0boundRe_const2 with ⟨C, hCpos, hC⟩
  use C, hCpos
  intro δ hδ
                           
  have h := hC δ hδ
                                                                  
  have h_re_eq : (-(1 / (δ : ℂ))).re = -(1 / δ) := by
    rw [Complex.neg_re, Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_ofReal]
                                          
  rwa [h_re_eq] at h

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT5_Strong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

local notation "𝓜" => MellinTransform

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
                                                     
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound: LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ := sigma1Of A T
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
                                                    
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  have log_big : 1 < Real.log T := by exact log_pos T (T_gt)
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      exact A_in.1.le
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have : σ₁ = sigma1Of A T := rfl
  have σ₁pos : 0 < σ₁ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_pos]
    calc
      A / Real.log T ≤ 1 / 2 / Real.log T := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply le_of_lt
        linarith
                                                          
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        apply le_of_lt
        refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹), ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert (preTransparency := .instances) this using 3
        all_goals try with_reducible_and_instances rfl
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
        calc
          1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
          _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
                            
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp <;> ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T) (by simp; rw [abs_of_pos Tpos]; exact T_gt) (by rw[this] at hσ; unfold sigma1Of at hσ; simp at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero]
          rw[← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
          exact hσ.2
          · refine (Real.log_pos ?_).ne.symm
            linarith
          · apply Real.log_pos
            linarith
          · linarith
          · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
        _ = C' * X / (ε * T) := by
          field_simp

lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
                                                       
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by

  obtain ⟨C, hC, i2Bound⟩ := I2Bound suppSmoothingF ContDiffSmoothingF has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
            
  change ‖I₂ SmoothingF ε T X (sigma1Of A T)‖ ≤ C * X / (ε * T) at i2Bound
  unfold sigma1Of at i2Bound
  have σ₁_eq : σ₁ = 1 - A / (Real.log T) := rfl
  rw[σ₁_eq]
  exact i2Bound

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),

        let σ₁ : ℝ := 1 - A / (Real.log T)
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
                                                      
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁                             
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1.le

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9  > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have m := log_lt_log (by linarith : 0 < (|t|)) (h2 : |t| < T )
    exact m

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 1 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 1 := by
        linarith
      linarith

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (lt_trans zero_lt_one logTgt1))
      _ = 1 := by norm_num
      _ < 2 := by norm_num

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (by linarith [logTgt1]))
      _ = 1 := by norm_num

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    rw [sub_pos]
    calc
      A / Real.log T ≤ (1/2) / Real.log T := by
        apply div_le_div_of_nonneg_right hA.2 (by linarith)
      _ ≤ (1/2) / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1/2 := by norm_num
      _ < 1 := by norm_num

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9/ t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ici (1 - A / Real.log |t|) := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    unfold σ₁
    apply mem_Ici.mpr
    ring_nf

    apply sub_le_sub_left
    have : Real.log |t| ≤ Real.log T := by
      apply Real.log_le_log (by linarith) (le_of_lt ht.2)
    exact div_le_div_of_nonneg_left (le_of_lt hA.1) (Real.log_pos (by linarith)) this

  have : ∫ (t : ℝ) in -T..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (-T : ℝ) (-3 : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo
  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact le_rfl
    · simpa only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using σ₁lt2.le
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul]
    rw[Complex.norm_I]
    simp only [one_mul]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by

      ring_nf
      simp only [norm_mul]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp [Real.pi_nonneg]
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      simp

    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3.le
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    rw [abs_of_pos pi_pos] at abs_pi_inv_le
    norm_num [abs_of_pos pi_pos] <;> linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (-T) (-3)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (-T) (-3)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (-T) (-3)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (-T) (-3), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (-T : ℝ) (-3 : ℝ)) volume := by
        have hle : -T ≤ -3 := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = -t := by
        refine abs_of_neg ?_
        linarith [ht.2]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.2]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.1]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in -T..-3, ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = -t := by
          refine abs_of_neg ?_
          linarith [ht.2]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.2]
          · linarith [ht.1]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · have : 0 ≤ Real.log |t| := by
            apply Real.log_nonneg
            linarith [tbounds1.1]
          positivity
        · positivity

        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T) = X * X ^ (- A / Real.log T) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T) * X ^ (A / Real.log T) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    simpa only [neg_div, mul_comm] using h₁.symm

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : x < 0 := by linarith[hx.2]
          have absx : |x| = -x := abs_of_neg xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.2]
            · linarith [hx.1]
          exact quotient_bound x (t_bounds x hx)
      apply le_trans this
      have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (-T) (-3) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log (-t)) ^ 9 / (-t) ^ 2 := by
          intro t ht
          have tneg : t < 0 := by linarith[ht.2]
          have : |t| = -t := abs_of_neg tneg
          rw [this, neg_sq]

        have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
              = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

        rw [this]

        have interval_to_Ioo1 : ∫ (t : ℝ) in -T..-3, Real.log (-t) ^ 9 / (-t) ^ 2
                        = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        have interval_to_Ioo2 : ∫ (t : ℝ) in (3)..(T), Real.log t ^ 9 / t ^ 2
                    = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← interval_to_Ioo1, ← interval_to_Ioo2]
        rw [intervalIntegral.integral_comp_neg (fun (t : ℝ) ↦ Real.log (t) ^ 9 / (t) ^ 2)]
        simp
      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (-T) (-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ))
  = Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp <;> norm_num

lemma I7Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2))
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, bound⟩ := I3Bound suppSmoothingF ContDiffSmoothingF hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by

  have reOne : re 1 = 1 := by exact rfl
  have imOne : im 1 = 0 := by exact rfl
  have reThree : re 3 = 3 := by exact rfl
  have imThree : im 3 = 0 := by exact rfl

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  unfold I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by exact rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        have : -3 ≠ 0 := by norm_num
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := by
          apply (NNReal.coe_le_coe).mp
          convert! (preTransparency := .instances) temp using 1; congr 2; ring
        have hp : (0 : NNReal) < ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ :=
          lt_of_lt_of_le (by norm_num) this
        convert! (preTransparency := .instances) hp using 1; congr 2; ring
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert (preTransparency := .instances) sInfPos.le using 5
      all_goals try with_reducible_and_instances rfl
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp A) (rexp (A / (1 - σ₂))))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := by exact le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb := by
      have : rexp (A / (1 - σ₂)) ≤ Tlb := by
        unfold Tlb
        apply le_max_of_le_right
        apply le_max_right
      rw[← Real.le_log_iff_exp_le] at this
      · rw[div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact logTlb_pos
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ≤ 1 - A / Real.log T := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · exact logTlb_pos
      · apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := by exact min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := by exact max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T) / ε = 1 * (C * X * X ^ (-A / Real.log T) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    apply le_of_lt
    exact lt_trans this (by norm_num)
    exact pi_nonneg
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I) =
              𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s := by exact rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]

                · have one_inv: (1⁻¹ : ℝ) = ( 1 : ℝ) := by norm_num
                  rw[zero_mul, neg_zero, Real.exp_zero, one_inv, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    rw [←div_eq_mul_inv]
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  simp only [norm_nonneg]
  norm_num

lemma I6Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4Bound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by

  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero] <;> linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  have U : σ₂ ∈ Ioo 0 1 := by
    refine mem_Ioo.mpr ?_
    · constructor
      · linarith[hσ₂.1]
      · linarith[hσ₂.2]

  clear U    C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      rw [Complex.sq_norm]; rw [Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; simp only [le_add_iff_nonneg_right]; exact zpow_two_nonneg t
      rw [Complex.sq_norm, Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add] <;> ring_nf <;> positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have T : 0 ≤ abs zeta_bound * M := by positivity
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε :=
    by
      unfold C
      ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

open _root_.Filter Topology

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairedHitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedHitting

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures

def pairedRegeneration : Set OddState := {s | s.1 ≤ 3}

end NumberTheoryLean.PairedHitting

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlaggedHarmonicPaths

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures

abbrev FlagState := CostState × Bool

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
end


