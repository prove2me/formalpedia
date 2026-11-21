-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointPRPProcess_F000
-- name    : LevyStochCalc_Driver_JointPRPProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:59:55.405896+00:00
-- url     : https://prove2.me/theorems/89d4156f-aa03-4aa9-b63f-634d9033e122
-- title:
--   Source declarations: LevyStochCalc.Driver.JointPRPProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointPRPProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint integral of a Lévy driver as a process

The Itô integral against a Brownian coordinate and the compensated integral against a Poisson
random measure are martingales for the right-continuous filtration, so each integral over the
horizon `[0, T]` conditions at a time `t ≤ T` to the integral over `[0, t]`. Summing the
coordinates and adding the compensated part turns the joint integral
`∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ` into the process `t ↦ ∑ i ∫₀ᵗ Gⁱ dWⁱ + ∫₀ᵗ ∫ K dÑ`, whose value
at `t` is the conditional expectation of the joint integral before the horizon. Together with
the predictable representation of a square-integrable weight of mean zero, this writes the
conditional expectations of such a weight as joint integrals over the shorter horizons.

## Main statements

* `LevyStochCalc.Driver.condExp_stochasticIntegralBrownian_rightCont`: the Itô integral over
  `[0, T]` conditions at `t ≤ T` to the Itô integral over `[0, t]`.
* `LevyStochCalc.Driver.condExp_stochasticIntegralCompensated_rightCont`: the compensated
  integral over `[0, T]` conditions at `t ≤ T` to the compensated integral over `[0, t]`.
* `LevyStochCalc.Driver.LevyDriver.jointIntegralProcess`: the joint integral over `[0, t]` of
  coordinate integrands and a marked integrand, as a process in the time `t`.
* `LevyStochCalc.Driver.LevyDriver.jointIntegralProcess_horizon`: at the horizon the process is
  the joint integral.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointIntegral_rightCont`: the joint integral over
  `[0, T]` conditions at `t ≤ T` to the joint integral process at `t`.
* `LevyStochCalc.Driver.LevyDriver.exists_jointIntegralProcess_augFiltration_of_mean_zero`: a
  square-integrable weight of mean zero measurable before `T` is a joint integral, and its
  conditional expectations before `T` are the joint integrals over the shorter horizons.

## References

* Jacod, J. and Shiryaev, A. N., *Limit Theorems for Stochastic Processes*, 2nd ed.,
  Springer 2003, Theorem III.4.34.
* Applebaum, D., *Lévy Processes and Stochastic Calculus*, 2nd ed., Cambridge 2009, §5.3.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open Brownian.Ito Poisson.Compensated

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

section Components

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T t : ℝ}

/-- The Itô integral over `[0, T]` conditions at a time `t ≤ T` to the Itô integral over
`[0, t]`. -/
theorem condExp_stochasticIntegralBrownian_rightCont (W : Brownian.BrownianMotion P)
    (hℱ : Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ S : ℝ, 0 < S → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) S,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (htT : t ≤ T) :
    P[Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T | ℱ.rightCont t]
      =ᵐ[P] Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t :=
  (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H hm hp
    hq).condExp_ae_eq htT
/-- The compensated integral over `[0, T]` conditions at a time `t ≤ T` to the compensated
integral over `[0, t]`. -/
theorem condExp_stochasticIntegralCompensated_rightCont
    (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (hℱ : Poisson.IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ S : ℝ, 0 < S → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) S, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (htT : t ≤ T) :
    P[Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq T | ℱ.rightCont t]
      =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t :=
  (Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ φ hm hp
    hq).condExp_ae_eq htT
/-- The Itô integral of an admissible integrand over `[0, t]`, as a process in the time `t`. -/
noncomputable def horizonProcess (W : Brownian.BrownianMotion P)
    (hℱ : Brownian.IsBrownianFiltration W ℱ) (G : HorizonIntegrand P ℱ T) : ℝ → Ω → ℝ :=
  fun t => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global t
/-- The compensated integral of an admissible marked integrand over `[0, t]`, as a process in
the time `t`. -/
noncomputable def markedHorizonProcess (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (hℱ : Poisson.IsPoissonFiltration N ℱ) (K : MarkedHorizonIntegrand P ν ℱ T) : ℝ → Ω → ℝ :=
  fun t => Poisson.Compensated.stochasticIntegral N ℱ hℱ K.toFun K.measurable_uncurry
    K.progressive K.sq_int_global t
end Components

namespace LevyDriver

open Brownian.Multidim.MultidimBrownianMotion

section Process

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

/-- The joint integral over `[0, t]` of coordinate integrands and a marked integrand, as a
process in the time `t`. -/
noncomputable def jointIntegralProcess (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) : ℝ → Ω → ℝ :=
  fun t ω => (∑ i : Fin d, horizonProcess (D.W.W i) (hcoord i) (G i) t ω)
    + markedHorizonProcess D.N hℱN K t ω
/-- At the horizon the joint integral process is the joint integral. -/
theorem jointIntegralProcess_horizon (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) :
    jointIntegralProcess hcoord hℱN G K T = jointIntegral hcoord hℱN G K := rfl
/-- The joint integral over `[0, T]` conditions at a time `t ≤ T` to the joint integral over
`[0, t]`. -/
theorem condExp_jointIntegral_rightCont (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) {t : ℝ} (htT : t ≤ T) :
    P[jointIntegral hcoord hℱN G K | ℱ.rightCont t]
      =ᵐ[P] jointIntegralProcess hcoord hℱN G K t := by
  have hBint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable ((G i).integral (D.W.W i) (hcoord i)) P := fun i _ =>
    (HorizonIntegrand.memLp (D.W.W i) (hcoord i) (G i)).integrable (by norm_num)
  have hNint : Integrable (K.integral D.N hℱN) P :=
    (MarkedHorizonIntegrand.memLp D.N hℱN K).integrable (by norm_num)
  have hdecomp : jointIntegral hcoord hℱN G K
      = (∑ i : Fin d, (G i).integral (D.W.W i) (hcoord i)) + K.integral D.N hℱN := by
    funext ω
    rw [Pi.add_apply, Finset.sum_apply]
    rfl
  have hsum := MeasureTheory.condExp_finsetSum hBint (ℱ.rightCont t)
  have hterm : ∀ i : Fin d, P[(G i).integral (D.W.W i) (hcoord i) | ℱ.rightCont t]
      =ᵐ[P] horizonProcess (D.W.W i) (hcoord i) (G i) t := fun i =>
    condExp_stochasticIntegralBrownian_rightCont (D.W.W i) (hcoord i) (G i).toFun
      (G i).measurable_uncurry (G i).progressive (G i).sq_int_global htT
  have hKterm : P[K.integral D.N hℱN | ℱ.rightCont t]
      =ᵐ[P] markedHorizonProcess D.N hℱN K t :=
    condExp_stochasticIntegralCompensated_rightCont D.N hℱN K.toFun K.measurable_uncurry
      K.progressive K.sq_int_global htT
  rw [hdecomp]
  refine (MeasureTheory.condExp_add (integrable_finsetSum' _ hBint) hNint
    (ℱ.rightCont t)).trans ?_
  filter_upwards [hsum, hKterm, Filter.eventually_all.2 hterm] with ω e1 e2 e3
  have hs : ∑ i : Fin d, P[(G i).integral (D.W.W i) (hcoord i) | ℱ.rightCont t] ω
      = ∑ i : Fin d, horizonProcess (D.W.W i) (hcoord i) (G i) t ω :=
    Finset.sum_congr rfl fun i _ => e3 i
  rw [Pi.add_apply, e1, Finset.sum_apply, hs, e2]
  rfl
end Process

section Representation

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The process form of the predictable representation property of a Lévy driver.** A
square-integrable weight of mean zero that is measurable before `T` for the augmented joint
filtration is a joint integral over `[0, T]`, and its conditional expectation at a time `t ≤ T`
for the right-continuous augmented joint filtration is the joint integral over `[0, t]` of the
same integrands. -/
theorem exists_jointIntegralProcess_augFiltration_of_mean_zero (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
          D.isPoissonFiltration_aug G K ∧
        ∀ t, t ≤ T → P[Z | (Brownian.augFiltration D.filtration P).rightCont t] =ᵐ[P]
          jointIntegralProcess (fun k => D.isBrownianFiltration_aug k)
            D.isPoissonFiltration_aug G K t := by
  obtain ⟨G, K, hZeq⟩ := exists_jointIntegral_augFiltration_of_mean_zero D hT hZ2 hZm hZ0
  refine ⟨G, K, hZeq, fun t htT => ?_⟩
  exact (MeasureTheory.condExp_congr_ae hZeq).trans
    (condExp_jointIntegral_rightCont (fun k => D.isBrownianFiltration_aug k)
      D.isPoissonFiltration_aug G K htT)
end Representation

end LevyDriver

end LevyStochCalc.Driver


