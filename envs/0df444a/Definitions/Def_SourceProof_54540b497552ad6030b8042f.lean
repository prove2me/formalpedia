-- Prove2me | Definitions.Def_SourceProof_54540b497552ad6030b8042f
-- name    : SourceProof_54540b497552ad6030b8042f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:56:38.714272+00:00
-- url     : https://prove2.me/theorems/b7111091-865c-45c6-bb21-7e289b4d5075
-- title:
--   LevyStochCalc source module: SourceProof_54540b497552ad6030b8042f
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.expIto_identity` comes from the `NonvacuityBSDEJExp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJExp_F000
import Definitions.Def_SourceProof_01f7c70491ce7157ce54880f
import Definitions.Def_SourceProof_c2510fef121a9f6103ef8e5e

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


theorem _root_.Prove2MeSourceProof.h_54540b497552ad6030b8042f {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂P, Real.exp (1 - t) * V t ω
      = -(∫ s in Set.Ioc (0 : ℝ) t, Real.exp (1 - s) * V s ω)
        + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
            (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω := by
  classical
  have hver := LevyStochCalc.Examples.Nonvacuity.isVectorItoVersion_modification D hcont hadapt hae
  have hcoordD : ∀ (q : Fin 1) (ω : Ω) (s : ℝ),
      coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω)
        = Real.exp (1 - s) := by
    intro q ω s
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    simp [coordDeriv, LevyStochCalc.Examples.Nonvacuity.expTestD, coordFun_apply, Brownian.Ito.timeAugProcess]
  have hfun : ∀ (q : Fin 1) (k : Fin 1),
      (fun (ω : Ω) (s : ℝ) => coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ))
        = fun (_ : Ω) (s : ℝ) => Real.exp (1 - s) := by
    intro q k
    funext ω s
    rw [hcoordD q ω s, mul_one]
  have hmg : ∀ (q : Fin 1) (k : Fin 1), Measurable (Function.uncurry
      fun (ω : Ω) (s : ℝ) => coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD q.succ
        (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ)) := by
    intro q k
    rw [hfun q k]
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.sub measurable_id)).comp measurable_snd
  have hpg : ∀ (q : Fin 1) (k : Fin 1), Probability.ProgressivelyMeasurable (augJoint D)
      fun (ω : Ω) (s : ℝ) => coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD q.succ
        (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ) := by
    intro q k
    rw [hfun q k]
    exact LevyStochCalc.Examples.Nonvacuity.progressivelyMeasurable_of_time (augJoint D)
      (Real.continuous_exp.comp (continuous_const.sub continuous_id))
  have hqg : ∀ (q : Fin 1) (k : Fin 1) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω)
        * (1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro q k T' hT'
    simp only [hcoordD, mul_one]
    exact LevyStochCalc.Examples.Nonvacuity.expWeight_sq P T' hT'
  have hform := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_01f7c70491ce7157ce54880f (C := 1) p2mMethodArg0 p2mMethodArg1 hver) zero_le_one (fun _ _ _ _ => by norm_num)
    (fun _ => measurable_const) (fun _ => measurable_const) (B := 0) le_rfl
    (fun _ _ _ => by norm_num)
    (fun _ _ _ T' _ => LevyStochCalc.Examples.Nonvacuity.lintegral_sq_const_lt_top P ((1 : ℝ) + 1) T')
    LevyStochCalc.Examples.Nonvacuity.hasFDerivAt_expTest LevyStochCalc.Examples.Nonvacuity.hasFDerivAt_expTestD LevyStochCalc.Examples.Nonvacuity.contDiff_expTest hmg hpg hqg ht0
  have hexpTest : ∀ (r : ℝ) (ω : Ω),
      LevyStochCalc.Examples.Nonvacuity.expTest (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω)
        = Real.exp (1 - r) * V r ω := by
    intro r ω
    simp [LevyStochCalc.Examples.Nonvacuity.expTest, Brownian.Ito.timeAugProcess]
  have hcoord0 : ∀ (r : ℝ) (ω : Ω), coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD 0
      (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω)
        = -(Real.exp (1 - r) * V r ω) := by
    intro r ω
    simp [coordDeriv, LevyStochCalc.Examples.Nonvacuity.expTestD, coordFun_apply, Brownian.Ito.timeAugProcess]
  have hcoord2 : ∀ (q q' : Fin 1) (r : ℝ) (ω : Ω), coordDeriv₂ LevyStochCalc.Examples.Nonvacuity.expTestD2
      q.succ q'.succ (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω) = 0 := by
    intro q q' r ω
    have hq : q = 0 := Subsingleton.elim _ _
    have hq' : q' = 0 := Subsingleton.elim _ _
    subst hq
    subst hq'
    simp [coordDeriv₂, LevyStochCalc.Examples.Nonvacuity.expTestD2, coordFun_apply]
  have hagree : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      coordDeriv LevyStochCalc.Examples.Nonvacuity.expTestD (0 : Fin 1).succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ)
        = LevyStochCalc.Examples.Nonvacuity.expZ Ω s ω 0 := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with s hs0 hs
    have hsne : s ≠ 0 := by simpa using hs0
    have hs' : s ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsne), hs.2.trans ht1⟩
    rw [hcoordD 0 ω s, mul_one, LevyStochCalc.Examples.Nonvacuity.expZ_apply, Set.indicator_of_mem hs']
  have hSI := _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e (D.W.W 0) (augJoint D)
    (D.isBrownianFiltration_aug 0) (hmg 0 0) (hpg 0 0) (hqg 0 0) (LevyStochCalc.Examples.Nonvacuity.expZ_meas 0)
    (LevyStochCalc.Examples.Nonvacuity.expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing LevyStochCalc.Examples.Nonvacuity.expZ_vanish LevyStochCalc.Examples.Nonvacuity.expZ_sq 0) ht0 hagree
  filter_upwards [hform, hSI, hae 0 le_rfl, (D.W.W 0).initial_zero] with ω h1 h2 h3 h4
  have hV0 : V 0 ω = 0 := h3.trans h4
  simp only [Fin.sum_univ_one] at h1
  rw [h2] at h1
  simp only [hexpTest, hcoord0, hcoord2, mul_zero, zero_mul, integral_zero, integral_neg,
    add_zero, hV0, sub_zero] at h1
  rw [LevyStochCalc.Examples.Nonvacuity.multidim_expZ_eq D t ω]
  linarith [h1]
end Version

/-! ### The solution triple -/

/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


