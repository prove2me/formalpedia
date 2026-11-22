-- Prove2me | Definitions.Def_SourceProof_63d33904140915cafacf5d43
-- name    : SourceProof_63d33904140915cafacf5d43
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:02:37.839076+00:00
-- url     : https://prove2.me/theorems/93e2afe3-ae71-4a52-ab71-fe8e2ec8df4e
-- title:
--   LevyStochCalc source module: SourceProof_63d33904140915cafacf5d43
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_setIntegral_mark_le` comes from the `LevyStochCalc.Ito.TruncatedContinuousPart` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F000
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F001
import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The continuous part of a path with the jumps of a mark set removed

Subtracting from the drift of a coefficient bundle the compensator, over a mark set of finite
intensity, of the jump coefficient read at the left limits of a path leaves a drift that is
jointly measurable, progressively measurable and square-integrable on every bounded window. With
the diffusion coefficient along the path it therefore builds a vector Itô process, and that
process has a continuous adapted version: the continuous part to which the finite-activity
splitting adds the left-limit jump sum.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.ae_forall_coord_eq`,
  `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.ae_forall_tendsto_nhdsGT` — the coordinatewise
  and right-continuity forms of a continuous adapted version.
* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_continuousDriftLeftAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_continuousDriftLeftAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_continuousDriftLeftAt_lt_top` — the drift
  carrying the left-limit compensator is an admissible Itô drift.
* `LevyStochCalc.Ito.JumpSplitting.exists_continuousPart` — a continuous adapted version of the
  vector Itô process built from that drift and the diffusion coefficient along the path.
* `LevyStochCalc.Ito.BigJump.ae_forall_bigJumpPath_eq_add_jumpSumLeftAt` — the path with the
  jumps of a mark set removed is its continuous part plus the jump sum over the complement.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {V : ℝ → Ω → Fin n → ℝ}

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Drift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_63d33904140915cafacf5d43 {A : Set E} (hAν : ν A ≠ ⊤) (f : Ω → ℝ → E → ℝ)
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A := by
  haveI hfin : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hslice : ∀ (ω : Ω) (s : ℝ), Measurable fun e => f ω s e := fun ω s =>
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2
        ≤ (∫⁻ e, (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A := by
    intro ω s
    have h1 : ‖∫ e in A, f ω s e ∂ν‖ₑ
        ≤ (∫⁻ e in A, ‖f ω s e‖ₑ ^ 2 ∂ν) ^ (2 : ℝ)⁻¹
          * (ν.restrict A) Set.univ ^ (2 : ℝ)⁻¹ :=
      le_trans (enorm_integral_le_lintegral_enorm _)
        (LevyStochCalc.Ito.JumpSplitting.lintegral_enorm_le_rms _ (hslice ω s).stronglyMeasurable.aestronglyMeasurable)
    refine le_trans (LevyStochCalc.Ito.JumpSplitting.sq_le_of_le_mul_rpow h1) ?_
    rw [Measure.restrict_apply_univ]
    exact mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (∫⁻ e, (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) * ν A ∂P :=
        lintegral_congr fun ω => lintegral_mul_const' _ _ hAν
    _ = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A :=
        lintegral_mul_const' _ _ hAν
end Drift

section ContinuousPart

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

end ContinuousPart

end LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.BigJump

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end LevyStochCalc.Ito.BigJump


