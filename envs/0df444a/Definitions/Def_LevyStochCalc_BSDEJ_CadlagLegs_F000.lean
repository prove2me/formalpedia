-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CadlagLegs_F000
-- name    : LevyStochCalc_BSDEJ_CadlagLegs_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:05:12.322176+00:00
-- url     : https://prove2.me/theorems/c2bc9870-414d-4ba6-907f-f3a2284c5b00
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.CadlagLegs
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.CadlagLegs. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Integrands_F000
import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F002
import Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
import Definitions.Def_LevyStochCalc_Driver_AugJointUsualConditions_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedNonpos_F000
import Definitions.Def_SourceProof_6293e0a2c6bb1095b807c809

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The two càdlàg martingale legs over the augmented joint filtration

The backward equation of `SolvesBSDEJ` is written with the two canonical stochastic integrals
of a Lévy driver, neither of which carries path regularity. Over the augmented joint filtration
`augJoint D` the usual conditions hold, so each leg has a version whose every path is
right-continuous with left limits: for the Brownian leg the coordinatewise càdlàg modifications
of `exists_everywhere_cadlag_vectorIntegral`, for the compensated Poisson leg the modification
`Poisson.Compensated.cadlagIntegral`. Both versions are martingales for `(augJoint D).rightCont`,
vanish almost surely at non-positive times, and — by Doob's `L²` maximal inequality applied to
the `L²` bound on the leg at the horizon — have finite `S²` seminorm on `[0, T]`.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.exists_cadlag_brownianLeg` — the Brownian leg of an integrand
  satisfying the `Z` fields of `SolvesBSDEJ` has an everywhere-càdlàg martingale version of
  finite `S²` seminorm.
* `LevyStochCalc.BSDEJ.Solves.exists_cadlag_poissonLeg` — the same for the compensated Poisson
  leg and the `U` fields of `SolvesBSDEJ`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.3, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Second moments -/

/-- A square-integrable real random variable has finite second moment. -/
theorem lintegral_sq_lt_top_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ < ⊤ := by
  rw [← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf.eLpNorm_lt_top.ne
/-! ### The Brownian leg -/

/-- The multidimensional Itô integral of a progressive integrand of finite energy on every
horizon has, under the usual conditions, a version that is adapted to the right-continuous
filtration, jointly measurable, càdlàg at every sample point, a martingale, almost surely zero
at non-positive times and of finite `S²` seminorm on `[0, T]`. -/
theorem exists_cadlag_vectorIntegral_supBound
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ i : Fin d, Brownian.IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hq : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P]
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z hm hp hq t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M ℱ.rightCont P ∧ (∀ t : ℝ, t ≤ 0 → M t =ᵐ[P] 0) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  classical
  obtain ⟨M, hadapt, hmeas, hae, hcadlag, hmart⟩ :=
    _root_.Prove2MeSourceProof.h_6293e0a2c6bb1095b807c809
      W ℱ hℱW Z hm hp hq hℱ0 hnull
  have hzero : ∀ t : ℝ, t ≤ 0 → M t =ᵐ[P] 0 := fun t ht =>
    (hae t).trans
      (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos
        W ℱ hℱW Z hm hp hq ht)
  have hmemI : MemLp (fun ω => ∑ i : Fin d,
      Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i) (fun ω' s => Z s ω' i) (hm i) (hp i)
        (hq i) T ω) 2 P :=
    memLp_finsetSum Finset.univ fun i _ =>
      Brownian.Ito.stochasticIntegralBrownian_memLp (W.W i) ℱ (hℱW i) (fun ω' s => Z s ω' i)
        (hm i) (hp i) (hq i) T
  have hmemM : MemLp (M T) 2 P := MemLp.ae_eq (hae T).symm hmemI
  refine ⟨M, hadapt, hmeas, hae, hcadlag, hmart, hzero, ?_⟩
  refine lt_of_le_of_lt (SupBound.lintegral_biSup_sq_le_of_martingale hmart hT
    (Eventually.of_forall fun ω t => (hcadlag ω t).1)) ?_
  exact ENNReal.mul_lt_top (by norm_num) (lintegral_sq_lt_top_of_memLp hmemM)
/-- The Brownian leg of a BSDEJ integrand over the augmented joint filtration has a version
that is adapted to `(augJoint D).rightCont`, jointly measurable, càdlàg at every sample point,
a martingale, almost surely zero at non-positive times and of finite `S²` seminorm on
`[0, T]`. -/
theorem exists_cadlag_brownianLeg (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (T : ℝ) (hT : 0 ≤ T) (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i)
    (hvan : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    ∃ M : ℝ → Ω → ℝ, Adapted (augJoint D).rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P]
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug Z hm hp (sq_int_global_of_vanishing hvan hsq) t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M (augJoint D).rightCont P ∧ (∀ t : ℝ, t ≤ 0 → M t =ᵐ[P] 0) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
  exists_cadlag_vectorIntegral_supBound D.W (augJoint D) D.isBrownianFiltration_aug Z hm hp
    (sq_int_global_of_vanishing hvan hsq) D.hF0_augFiltration_rightCont
    (fun _s hs h0 => D.measurableSet_augFiltration_of_null hs h0) T hT
/-! ### The compensated Poisson leg -/

/-- The compensated Itô–Lévy integral of a marked progressive integrand of finite marked energy
on every horizon has, under the usual conditions, a version that is adapted to the
right-continuous filtration, jointly measurable, càdlàg at every sample point, a martingale,
almost surely zero at non-positive times and of finite `S²` seminorm on `[0, T]`. -/
theorem exists_cadlag_compensatedIntegral_supBound
    (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M ℱ.rightCont P ∧ (∀ t : ℝ, t ≤ 0 → M t =ᵐ[P] 0) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  classical
  have hadapt := Poisson.Compensated.cadlagIntegral_adapted N ℱ hℱ φ hm hp hq hℱ0 hnull
  have hright := Poisson.Compensated.cadlagIntegral_rightContinuous N ℱ hℱ φ hm hp hq hℱ0 hnull
  have hleft := Poisson.Compensated.cadlagIntegral_exists_leftLim N ℱ hℱ φ hm hp hq hℱ0 hnull
  have hae := Poisson.Compensated.cadlagIntegral_ae_eq N ℱ hℱ φ hm hp hq hℱ0 hnull
  have hmart : Martingale
      (Poisson.Compensated.cadlagIntegral N ℱ hℱ φ hm hp hq hℱ0 hnull) ℱ.rightCont P :=
    LevyStochCalc.Martingale.martingale_of_ae_eq
      (Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ φ hm hp hq)
      hadapt.stronglyAdapted hae
  have hmemM : MemLp
      (Poisson.Compensated.cadlagIntegral N ℱ hℱ φ hm hp hq hℱ0 hnull T) 2 P :=
    MemLp.ae_eq
      ((hae T).trans
        (Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq T)).symm
      (Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq T)
  refine ⟨Poisson.Compensated.cadlagIntegral N ℱ hℱ φ hm hp hq hℱ0 hnull, hadapt,
    Probability.measurable_uncurry_of_rightContinuous hadapt hright, hae,
    fun ω t => ⟨hright ω t, hleft ω t⟩, hmart,
    fun t ht => Poisson.Compensated.cadlagIntegral_ae_zero_of_nonpos N ℱ hℱ φ hm hp hq
      hℱ0 hnull ht, ?_⟩
  refine lt_of_le_of_lt (SupBound.lintegral_biSup_sq_le_of_martingale hmart hT
    (Eventually.of_forall fun ω t => hright ω t)) ?_
  exact ENNReal.mul_lt_top (by norm_num) (lintegral_sq_lt_top_of_memLp hmemM)
/-- The compensated Poisson leg of a BSDEJ integrand over the augmented joint filtration has a
version that is adapted to `(augJoint D).rightCont`, jointly measurable, càdlàg at every sample
point, a martingale, almost surely zero at non-positive times and of finite `S²` seminorm on
`[0, T]`. -/
theorem exists_cadlag_poissonLeg (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (T : ℝ) (hT : 0 ≤ T) (U : ℝ → Ω → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable (augJoint D) fun ω s e => U s ω e)
    (hvan : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    ∃ M : ℝ → Ω → ℝ, Adapted (augJoint D).rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N (augJoint D)
        D.isPoissonFiltration_aug (fun ω s e => U s ω e) hm hp
        (marked_sq_int_global_of_vanishing hvan hsq) t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M (augJoint D).rightCont P ∧ (∀ t : ℝ, t ≤ 0 → M t =ᵐ[P] 0) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
  exists_cadlag_compensatedIntegral_supBound D.N (augJoint D) D.isPoissonFiltration_aug
    (fun ω s e => U s ω e) hm hp (marked_sq_int_global_of_vanishing hvan hsq)
    D.hF0_augFiltration_rightCont
    (fun _s hs h0 => D.measurableSet_augFiltration_of_null hs h0) T hT
end LevyStochCalc.BSDEJ.Solves


