-- Prove2me | Definitions.Def_NonvacuityBSDEJExp_F000
-- name    : NonvacuityBSDEJExp_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:49:19.964197+00:00
-- url     : https://prove2.me/theorems/963c9381-a25f-4979-bafb-2cb5dc61a571
-- title:
--   Source declarations: NonvacuityBSDEJExp
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJExp. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000
import Definitions.Def_NonvacuityBSDEJ_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The explicit solution of a backward equation with the identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, the horizon is `T = 1` and the
terminal datum is the Brownian value `W_1`. Since `d(e^{1-t} W_t) = −e^{1-t} W_t dt + e^{1-t} dW_t`,
the value process is `Y_t = e^{1-t} W_t`, the Brownian integrand is the windowed weight
`e^{1-s} 1_{(0, 1]}(s)` and the jump integrand vanishes.

## Main statements

* `exists_solvesBSDEJ_expZ` — the equation is solved by `e^{1-t}` times a continuous modification
  of the Brownian motion, together with the integrand pair `(e^{1-s} 1_{(0, 1]}, 0)`.
* `energy_expZ` — the energy of `e^{1-s} 1_{(0, 1]}` on `[0, 1]` is `(e² − 1)/2`.
* `energy_eq_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand of
  energy `(e² − 1)/2` on `[0, 1]`.
* `exists_solvesBSDEJ_generator_id_energy_ne_zero` — on a probability space carrying such a
  driver the equation has this solution triple and every solution triple has Brownian integrand
  of nonzero energy.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Brownian.Ito (IsVectorItoVersion)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The test function `(t, x) ↦ e^{1-t} x` -/

/-- The `i`-th coordinate functional on `ℝ²`. -/
noncomputable def coordFun (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
/-- The value of the `i`-th coordinate functional on `ℝ²`. -/
theorem coordFun_apply (i : Fin 2) (z : Fin 2 → ℝ) : coordFun i z = z i := rfl
/-- The function `(t, x) ↦ e^{1-t} x` on `ℝ²`, with the time in coordinate `0`. -/
noncomputable def expTest (z : Fin 2 → ℝ) : ℝ := Real.exp (1 - z 0) * z 1
/-- The Fréchet derivative of `expTest`. -/
noncomputable def expTestD (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (-(Real.exp (1 - z 0) * z 1)) • coordFun 0 + Real.exp (1 - z 0) • coordFun 1
/-- The second Fréchet derivative of `expTest`. -/
noncomputable def expTestD2 (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ((Real.exp (1 - z 0) * z 1) • coordFun 0
        - Real.exp (1 - z 0) • coordFun 1).smulRight (coordFun 0)
    + ((-Real.exp (1 - z 0)) • coordFun 0).smulRight (coordFun 1)
/-- A coordinate functional is its own Fréchet derivative. -/
theorem hasFDerivAt_coordFun (i : Fin 2) (z : Fin 2 → ℝ) :
    HasFDerivAt (fun w : Fin 2 → ℝ => w i) (coordFun i) z := (coordFun i).hasFDerivAt
/-- The Fréchet derivative of the time factor `(t, x) ↦ e^{1-t}` of `expTest`. -/
theorem hasFDerivAt_expFactor (z : Fin 2 → ℝ) :
    HasFDerivAt (fun w : Fin 2 → ℝ => Real.exp (1 - w 0))
      ((-Real.exp (1 - z 0)) • coordFun 0) z := by
  refine (((hasFDerivAt_const (1 : ℝ) z).sub (hasFDerivAt_coordFun 0 z)).exp).congr_fderiv ?_
  ext v
  simp
/-- `expTestD` is the Fréchet derivative of `expTest`. -/
theorem hasFDerivAt_expTest (z : Fin 2 → ℝ) : HasFDerivAt expTest (expTestD z) z := by
  refine ((hasFDerivAt_expFactor z).mul (hasFDerivAt_coordFun 1 z)).congr_fderiv ?_
  ext v
  simp [expTestD, coordFun_apply]
  ring
/-- `expTestD2` is the Fréchet derivative of `expTestD`. -/
theorem hasFDerivAt_expTestD (z : Fin 2 → ℝ) : HasFDerivAt expTestD (expTestD2 z) z := by
  have hα : HasFDerivAt (fun w : Fin 2 → ℝ => -(Real.exp (1 - w 0) * w 1))
      ((Real.exp (1 - z 0) * z 1) • coordFun 0 - Real.exp (1 - z 0) • coordFun 1) z := by
    refine ((hasFDerivAt_expTest z).neg).congr_fderiv ?_
    ext v
    simp [expTestD, coordFun_apply]
    ring
  exact (hα.smul_const (coordFun 0)).add ((hasFDerivAt_expFactor z).smul_const (coordFun 1))
/-- `expTest` is twice continuously differentiable. -/
theorem contDiff_expTest : ContDiff ℝ 2 expTest := by
  have h0 : ContDiff ℝ 2 fun z : Fin 2 → ℝ => z 0 := (coordFun 0).contDiff
  have h1 : ContDiff ℝ 2 fun z : Fin 2 → ℝ => z 1 := (coordFun 1).contDiff
  exact (Real.contDiff_exp.comp (contDiff_const.sub h0)).mul h1
/-! ### The exponential weight -/

/-- A process that does not depend on the sample point and is continuous in time is
progressively measurable. -/
theorem progressivelyMeasurable_of_time (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {φ : ℝ → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => φ s :=
  _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f
    (MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
      (fun _ => stronglyMeasurable_const) fun _ => hφ)
/-- A constant integrand has finite energy on every bounded window. -/
theorem lintegral_sq_const_lt_top (P : Measure Ω) [IsProbabilityMeasure P] (c T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
/-- The extended norm of a nonnegative real is its image under `ENNReal.ofReal`. -/
theorem ennnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal x := by
  simp [Real.nnnorm_of_nonneg hx, ENNReal.ofReal, Real.toNNReal_of_nonneg hx]
/-- The weight `e^{1-s}` is bounded by `e` at nonnegative times. -/
theorem nnnorm_expWeight_le {s : ℝ} (hs : 0 ≤ s) :
    (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ≤ (‖Real.exp 1‖₊ : ℝ≥0∞) := by
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith)
/-- The weight `e^{1-s}` has finite energy on every bounded window. -/
theorem expWeight_sq (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (_hT : 0 < T) :
    ∫⁻ _ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hinner : ∀ _ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
    intro _
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
          exact pow_le_pow_left' (nnnorm_expWeight_le hs.1) 2
      _ = (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  refine lt_of_le_of_lt (lintegral_mono hinner) ?_
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
/-! ### The integrands of the equation -/

/-- The windowed exponential weight `e^{1-s} 1_{(0, 1]}(s)`, read as a one-dimensional Brownian
integrand. -/
noncomputable def expZ (Ω) [MeasurableSpace Ω] : ℝ → Ω → (Fin 1 → ℝ) :=
  fun s _ _ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun r => Real.exp (1 - r)) s
/-- The value of `expZ` at a time is the windowed exponential weight at that time. -/
theorem expZ_apply (s : ℝ) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun r => Real.exp (1 - r)) s := rfl
/-- `expZ` is the exponential weight times the indicator of the window `(0, 1]`. -/
theorem expZ_eq_mul (s : ℝ) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = Real.exp (1 - s) * Brownian.Ito.indIoc Ω 0 1 ω s := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [expZ, Brownian.Ito.indIoc, hs]
/-- `expZ` is dominated by the exponential weight. -/
theorem abs_expZ_le (s : ℝ) (ω : Ω) (i : Fin 1) :
    |expZ Ω s ω i| ≤ |Real.exp (1 - s)| := by
  rw [expZ_apply]
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, abs_zero]
    exact abs_nonneg _
/-- Each coordinate of `expZ` is jointly measurable. -/
theorem expZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => expZ Ω s ω i) := by
  have h : Measurable fun r : ℝ => Real.exp (1 - r) :=
    Real.continuous_exp.measurable.comp (measurable_const.sub measurable_id)
  exact (h.indicator measurableSet_Ioc).comp measurable_snd
/-- Each coordinate of `expZ` is progressively measurable for every filtration. -/
theorem expZ_prog (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (i : Fin 1) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => expZ Ω s ω i := by
  have hfun : (fun (ω : Ω) s => expZ Ω s ω i)
      = fun (ω : Ω) s => Real.exp (1 - s) * Brownian.Ito.indIoc Ω 0 1 ω s := by
    funext ω s
    exact expZ_eq_mul s ω i
  rw [hfun]
  exact (progressivelyMeasurable_of_time ℱ
      (Real.continuous_exp.comp (continuous_const.sub continuous_id))).mul
    (Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ zero_lt_one)
/-- `expZ` vanishes off the horizon `[0, 1]`. -/
theorem expZ_vanish (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : expZ Ω s ω = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  funext i
  simp [expZ, Set.indicator_of_notMem hs']
/-- Each coordinate of `expZ` is square integrable on every bounded window. -/
theorem expZ_sq_global (P : Measure Ω) [IsProbabilityMeasure P] (i : Fin 1) (T : ℝ)
    (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => abs_expZ_le s ω i) (expWeight_sq P) T hT
/-- Each coordinate of `expZ` has finite energy on the horizon `[0, 1]`. -/
theorem expZ_sq (i : Fin 1) : Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i) ≠ ⊤ :=
  (expZ_sq_global P i 1 zero_lt_one).ne
/-- The zero jump integrand is jointly measurable in the sample point, the time and the mark. -/
theorem zeroJump_meas : Measurable fun _p : Ω × ℝ × ℝ => (0 : ℝ) := measurable_const
/-- The zero jump integrand is marked progressively measurable for the augmented joint
filtration. -/
theorem zeroJump_prog (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    Probability.MarkedProgressivelyMeasurable (augJoint D)
      fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ) :=
  Poisson.Compensated.markedProgressivelyMeasurable_zero (augJoint D)
/-- The zero jump integrand has finite marked energy on the horizon `[0, 1]`. -/
theorem zeroJump_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) ≠ ⊤ := by
  simp [Poisson.Compensated.markedEnergy]
/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- A continuous adapted modification of the first Brownian coordinate is a version of the
one-dimensional vector Itô process with zero initial value, zero drift and unit diffusion. -/
theorem isVectorItoVersion_modification {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t) :
    IsVectorItoVersion D.W (augJoint D) D.isBrownianFiltration_aug
      (fun _ _ (_ : Ω) (_ : ℝ) => (1 : ℝ)) (fun _ _ => measurable_const)
      (fun _ _ => Probability.progressivelyMeasurable_const (augJoint D) (1 : ℝ))
      (fun _ _ => lintegral_sq_one_lt_top P) (fun (_ : Ω) (_ : Fin 1) => (0 : ℝ))
      (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ)) (fun t ω (_ : Fin 1) => V t ω) where
  continuous_path := fun ω => continuous_pi fun _ => hcont ω
  adapted := by
    intro t
    letI : MeasurableSpace Ω := augJoint D t
    exact (measurable_pi_lambda _ fun _ => hadapt t).stronglyMeasurable
  ae_eq := by
    intro t ht
    filter_upwards [hae t ht, Brownian.Ito.stochasticIntegralBrownian_one (D.W.W 0)
      (augJoint D) (D.isBrownianFiltration_aug 0) measurable_const
      (Probability.progressivelyMeasurable_const (augJoint D) (1 : ℝ))
      (lintegral_sq_one_lt_top P) ht] with ω h1 h2
    funext m
    simp only [Brownian.Ito.vectorItoProcess, Brownian.Ito.vectorItoMartingale,
      Brownian.Ito.coordItoIntegral, Fin.sum_univ_one, integral_zero, zero_add, add_zero]
    rw [h1, ← h2]
/-- The multidimensional Itô integral of `expZ` is the one-dimensional Itô integral of its
single coordinate. -/
theorem multidim_expZ_eq (t : ℝ) (ω : Ω) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
        D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
        (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω
      = Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) (augJoint D)
        (D.isBrownianFiltration_aug 0) (fun ω' s => expZ Ω s ω' 0) (expZ_meas 0)
        (expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing expZ_vanish expZ_sq 0) t ω := by
  simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, Fin.sum_univ_one]
  rfl
end Version

/-! ### The solution triple -/

/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


