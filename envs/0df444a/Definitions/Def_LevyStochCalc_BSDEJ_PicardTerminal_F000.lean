-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardTerminal_F000
-- name    : LevyStochCalc_BSDEJ_PicardTerminal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:58:05.100597+00:00
-- url     : https://prove2.me/theorems/f5b65bfe-ce6f-46b2-9d8a-da4e4da2ba45
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardTerminal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardTerminal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F001
import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F002
import Definitions.Def_LevyStochCalc_BSDEJ_Integrands_F000
import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The terminal datum of a Picard step and its martingale representation

A Picard step of a backward equation with jumps is driven by the variable `ξ + ∫_0^T b_s ds`,
where `ξ` is the terminal value and `b` the generator frozen along the previous iterate:
`terminalDatum` is that variable. It is square integrable and measurable before the horizon as
soon as `ξ` is and `b` is progressive of finite energy; progressivity for the right-continuous
filtration already suffices when `b` vanishes off the horizon. `centred` subtracts the mean, and the
predictable representation property of a Lévy driver writes the centred terminal datum as the
sum of a multidimensional Itô integral and a compensated integral over the horizon, whose
integrands carry the measurability, progressivity, vanishing and energy fields the backward
equation is written with.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The terminal datum of a Picard step -/

/-- The terminal datum of a Picard step: the terminal value plus the time integral of the
frozen generator over the horizon `[0, T]`. -/
noncomputable def terminalDatum (ξ : Ω → ℝ) (b : Ω → ℝ → ℝ) (T : ℝ) : Ω → ℝ :=
  fun ω => ξ ω + ∫ s in Set.Icc (0 : ℝ) T, b ω s
omit [IsProbabilityMeasure P] in
/-- The terminal datum of a square-integrable terminal value and a drift of finite energy is
square integrable. -/
theorem memLp_terminalDatum {ξ : Ω → ℝ} {b : Ω → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hξ2 : MemLp ξ 2 P) (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    MemLp (terminalDatum ξ b T) 2 P :=
  hξ2.add (Ito.SecondMoment.memLp_two_setIntegral hbm hT (lt_top_iff_ne_top.mpr hbq))
/-- The terminal datum of a terminal value measurable before the horizon and a progressive
drift is measurable before the horizon. -/
theorem aestronglyMeasurable_terminalDatum (D : Driver.LevyDriver.{u, v, w} P d ν)
    {ξ : Ω → ℝ} {b : Ω → ℝ → ℝ} {T : ℝ} (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    (hbp : Probability.ProgressivelyMeasurable (augJoint D) b) :
    AEStronglyMeasurable[augJoint D T] (terminalDatum ξ b T) P :=
  hξm.add ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self
    volume).aestronglyMeasurable)
/-- The terminal datum of a terminal value measurable before the horizon and a drift of finite
energy vanishing off the horizon is measurable before the horizon already when the drift is
progressive for the right-continuous augmented joint filtration. -/
theorem aestronglyMeasurable_terminalDatum_of_rightCont (D : Driver.LevyDriver.{u, v, w} P d ν)
    {ξ : Ω → ℝ} {b : Ω → ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hξm : AEStronglyMeasurable[augJoint D T] ξ P) (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hbp : Probability.ProgressivelyMeasurable (augJoint D).rightCont b) :
    AEStronglyMeasurable[augJoint D T] (terminalDatum ξ b T) P :=
  hξm.add ⟨driftLeg b T T,
    _root_.Prove2MeSourceProof.h_95eaf7edddd1af971f664384 hbm hbp hbz hbq
      (fun _s hs h0 => D.measurableSet_augFiltration_of_null hs h0) hT.le,
    (driftLeg_ae_eq hbm hbq T).symm⟩
/-! ### Centring -/

/-- A variable with its mean under `P` subtracted. -/
noncomputable def centred (P : Measure Ω) (ζ : Ω → ℝ) : Ω → ℝ :=
  fun ω => ζ ω - ∫ ω', ζ ω' ∂P
/-- The centring of an integrable variable has mean zero. -/
theorem integral_centred {ζ : Ω → ℝ} (hζ : Integrable ζ P) :
    ∫ ω, centred P ζ ω ∂P = 0 := by
  have h : ∫ ω, centred P ζ ω ∂P
      = (∫ ω, ζ ω ∂P) - ∫ _ω : Ω, (∫ ω', ζ ω' ∂P) ∂P :=
    integral_sub hζ (integrable_const _)
  rw [h, integral_const]
  simp
omit [SigmaFinite ν] in
/-- The centring of a square-integrable variable is square integrable. -/
theorem memLp_centred {ζ : Ω → ℝ} (hζ2 : MemLp ζ 2 P) : MemLp (centred P ζ) 2 P :=
  hζ2.sub (memLp_const _)
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The centring of a variable measurable before a time of a filtration is measurable before
that time. -/
theorem aestronglyMeasurable_centred {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {t : ℝ}
    {ζ : Ω → ℝ} (hζm : AEStronglyMeasurable[ℱ t] ζ P) :
    AEStronglyMeasurable[ℱ t] (centred P ζ) P :=
  hζm.sub aestronglyMeasurable_const
/-! ### The martingale representation of the centred terminal datum -/

section Representation

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- The centred terminal datum of a Picard step is the sum of a multidimensional Itô integral
and a compensated integral over the horizon, taken along integrands that are measurable,
progressive for the augmented joint filtration, vanishing off the horizon and of finite
energy. -/
theorem exists_picard_integrands (D : Driver.LevyDriver.{u, v, w} P d ν) {T : ℝ} (hT : 0 < T)
    {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable (augJoint D) b)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∃ (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
      (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
      (hZp : ∀ i : Fin d, Probability.ProgressivelyMeasurable (augJoint D)
        fun ω s => Z s ω i)
      (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      (hZq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
      (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
      (hUp : Probability.MarkedProgressivelyMeasurable (augJoint D) fun ω s e => U s ω e)
      (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
      (hUq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤),
      centred P (terminalDatum ξ b T) =ᵐ[P] fun ω =>
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug Z hZm hZp (sq_int_global_of_vanishing hZv hZq) T ω
          + Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
            (fun ω' s e => U s ω' e) hUm hUp (marked_sq_int_global_of_vanishing hUv hUq) T ω := by
  have h2 : MemLp (terminalDatum ξ b T) 2 P := memLp_terminalDatum hT.le hξ2 hbm hbq
  obtain ⟨G, K, hrep⟩ :=
    Driver.LevyDriver.exists_jointIntegral_augFiltration_of_mean_zero D hT (memLp_centred h2)
      (aestronglyMeasurable_centred (aestronglyMeasurable_terminalDatum D hξm hbp))
      (integral_centred (h2.integrable (by norm_num)))
  exact ⟨coordOfHorizonIntegrand G, processOfMarkedHorizonIntegrand K,
    measurable_coordOfHorizonIntegrand G, progressive_coordOfHorizonIntegrand G,
    coordOfHorizonIntegrand_vanish G, energy_coordOfHorizonIntegrand_ne_top G,
    measurable_processOfMarkedHorizonIntegrand K, progressive_processOfMarkedHorizonIntegrand K,
    processOfMarkedHorizonIntegrand_vanish K,
    markedEnergy_processOfMarkedHorizonIntegrand_ne_top K, hrep⟩
end Representation

end LevyStochCalc.BSDEJ.Solves


