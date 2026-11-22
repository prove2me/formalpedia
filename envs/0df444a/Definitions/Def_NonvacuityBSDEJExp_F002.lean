-- Prove2me | Definitions.Def_NonvacuityBSDEJExp_F002
-- name    : NonvacuityBSDEJExp_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:21:15.904245+00:00
-- url     : https://prove2.me/theorems/3ee192a2-b4be-43c5-81f1-2aa3cbf60e82
-- title:
--   Source declarations: NonvacuityBSDEJExp
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJExp. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJExp_F000
import Definitions.Def_SourceProof_cdebc989955e2f6003b4385b

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

/-! ### The exponential weight -/

/-! ### The integrands of the equation -/

/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Version

/-! ### The solution triple -/

/-! ### The energy of the Brownian integrand -/

/-- The integral of `e^{2-2s}` over the window `(0, 1]`. -/
theorem integral_expWeight_sq :
    ∫ s in Set.Ioc (0 : ℝ) 1, Real.exp (2 - 2 * s) = (Real.exp 2 - 1) / 2 := by
  have hfun : Continuous fun s : ℝ => Real.exp (2 - 2 * s) :=
    Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => -(1 / 2 : ℝ) * Real.exp (2 - 2 * r))
      (Real.exp (2 - 2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => 2 - 2 * r) (-2 : ℝ) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).const_sub (2 : ℝ)
    refine (h1.exp.const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    ring
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun x _ => hd x) (hfun.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at hsub
  rw [hsub]
  norm_num
  ring
/-- The energy of a path of `expZ` on the horizon `[0, 1]`. -/
theorem lintegral_expZ_sq (ω : Ω) (i : Fin 1) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  have hsq : ∀ r : ℝ, Real.exp (1 - r) ^ 2 = Real.exp (2 - 2 * r) := by
    intro r
    rw [sq, ← Real.exp_add]
    ring_nf
  have hpt : ∀ s : ℝ, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2
      = Set.indicator (Set.Ioc (0 : ℝ) 1)
        (fun r => ENNReal.ofReal (Real.exp (2 - 2 * r))) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
    · rw [expZ_apply, Set.indicator_of_mem hs, Set.indicator_of_mem hs,
        ennnorm_of_nonneg (Real.exp_nonneg _), ← ENNReal.ofReal_pow (Real.exp_nonneg _), hsq]
    · rw [expZ_apply, Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
      simp
  simp only [hpt]
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self]
  have hio : IntegrableOn (fun s : ℝ => Real.exp (2 - 2 * s)) (Set.Ioc (0 : ℝ) 1) volume :=
    Continuous.integrableOn_Ioc
      (Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_id)))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun s : ℝ => Real.exp (2 - 2 * s) :=
    Filter.Eventually.of_forall fun s => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hio hnn, integral_expWeight_sq]
/-- The energy of `expZ` on the horizon `[0, 1]` is `(e² − 1)/2`. -/
theorem energy_expZ (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i)
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  rw [Brownian.Ito.energy]
  simp [lintegral_expZ_sq]
/-- The real number `(e² − 1)/2` is positive. -/
theorem ofReal_expWeight_ne_zero : ENNReal.ofReal ((Real.exp 2 - 1) / 2) ≠ 0 := by
  have h2 : (3 : ℝ) < Real.exp 2 := by
    have := Real.add_one_lt_exp (x := (2 : ℝ)) (by norm_num)
    linarith
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith
/-- The energy of `expZ` on the horizon `[0, 1]` is nonzero. -/
theorem energy_expZ_ne_zero (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i) ≠ 0 := by
  rw [energy_expZ]
  exact ofReal_expWeight_ne_zero
/-- The Brownian integrand of a solution of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` has energy `(e² − 1)/2` on `[0, 1]`. -/
theorem energy_eq_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0)
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ y _ _ => y) (L := 1) zero_le_one
    measurable_generator_id lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
  have hzero := (huniq Y' Y Z' (expZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmE : Measurable (Function.uncurry fun (ω : Ω) s => expZ Ω s ω 0) := expZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - expZ Ω s ω 0) := hmZ.sub hmE
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - expZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ => Z' p.2 p.1 0)
      =ᵐ[Brownian.Ito.energyMeasure P 1] fun p : Ω × ℝ => expZ Ω p.2 p.1 0 := by
    filter_upwards [hae] with p hp
    have hp' : Z' p.2 p.1 0 - expZ Ω p.2 p.1 0 = 0 := hp
    linarith
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmZ 1, eLpNorm_congr_ae hae2,
    ← Brownian.Ito.energy_eq_eLpNorm_sq hmE 1]
  exact energy_expZ 0
/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` whose value process is `e^{1-t} W_t`,
whose Brownian integrand is `e^{1-s} 1_{(0, 1]}`, of energy `(e² − 1)/2` on the horizon, and
whose jump integrand vanishes; the Brownian integrand of every solution triple of that equation
has nonzero energy on the horizon. -/
theorem exists_solvesBSDEJ_generator_id_energy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y (expZ Ω)
              (fun _ _ _ => (0 : ℝ)) ∧
            ∀ t, Y t =ᵐ[P] fun ω => Real.exp (1 - t) * (D.W.W 0).W t ω) ∧
        Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω 0)
            = ENNReal.ofReal ((Real.exp 2 - 1) / 2) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b D, energy_expZ 0,
    fun _ _ _ h => ?_⟩
  rw [energy_eq_of_solvesBSDEJ D h]
  exact ofReal_expWeight_ne_zero
end LevyStochCalc.Examples.Nonvacuity


