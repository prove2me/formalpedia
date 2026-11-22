-- Prove2me | Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001
-- name    : LevyStochCalc_Ito_TruncatedContinuousPart_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:07:40.464151+00:00
-- url     : https://prove2.me/theorems/eb6d70ce-26cc-45b0-90b5-30a8e8563c56
-- title:
--   Source declarations: LevyStochCalc.Ito.TruncatedContinuousPart
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.TruncatedContinuousPart. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F000
import Definitions.Def_SourceProof_63d33904140915cafacf5d43
import Definitions.Def_SourceProof_e40bf0e3e05fd6503919f765

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

omit [IsProbabilityMeasure P] in
/-- A square-integrable process minus the integral over a mark set of finite intensity of a
square-integrable marked process has finite energy on every bounded window. -/
theorem lintegral_sq_sub_setIntegral_mark_lt_top {A : Set E} (hAν : ν A ≠ ⊤) (b : Ω → ℝ → ℝ)
    (f : Ω → ℝ → E → ℝ) (hbm : Measurable (Function.uncurry b))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)
    (hfq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖f ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b ω s - ∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set M : Ω × ℝ → ℝ≥0∞ := fun p => (‖b p.1 p.2‖₊ : ℝ≥0∞) ^ 2 with hMdef
  set C : Ω × ℝ → ℝ≥0∞ := fun p => (‖∫ e in A, f p.1 p.2 e ∂ν‖₊ : ℝ≥0∞) ^ 2 with hCdef
  have hMmeas : Measurable M :=
    (ENNReal.continuous_coe.measurable.comp hbm.nnnorm).pow_const 2
  have hCmeas : Measurable C :=
    (ENNReal.continuous_coe.measurable.comp
      (stronglyMeasurable_setIntegral_mark A f hf).measurable.nnnorm).pow_const 2
  have hbound : ∀ (ω : Ω) (s : ℝ),
      (‖b ω s - ∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (M (ω, s) + C (ω, s)) := by
    intro ω s
    exact le_trans (pow_le_pow_left' enorm_sub_le 2) (sq_add_le_four_mul _ _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume :=
    fun ω => lintegral_add_left (hMmeas.comp measurable_prodMk_left) _
  have houter : ∫⁻ ω, ((∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume) ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P :=
    lintegral_add_left (hMmeas.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))) _
  have hCfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_63d33904140915cafacf5d43 hAν f hf T) ?_
    exact ENNReal.mul_lt_top (hfq T hT) (lt_top_iff_ne_top.mpr hAν)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖b ω s - ∫ e in A, f ω s e ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (M (ω, s) + C (ω, s)) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hbound ω s
    _ = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume ∂P := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        exact lintegral_congr fun ω => lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)
    _ = 4 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P) := by
        rw [lintegral_congr hinner, houter]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hbq T hT, hCfin⟩)
/-- The compensator over a mark set of the jump coefficient read at the left limits of a path is
strongly measurable in the sample point and the time. -/
theorem stronglyMeasurable_markIntegralLeftAt (A : Set E) (i : Fin n)
    (hγmL : Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i) :
    StronglyMeasurable fun p : Ω × ℝ =>
      ∫ e in A, coeffs.γ p.2 (leftLimPathAt Xp p.2 p.1) e i ∂ν :=
  stronglyMeasurable_setIntegral_mark A
    (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) hγmL
/-- The drift of a bundle along a path with the left-limit compensator over a mark set subtracted
is jointly measurable. -/
theorem measurable_uncurry_continuousDriftLeftAt (A : Set E) (i : Fin n)
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hγmL : Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i) :
    Measurable (Function.uncurry (continuousDriftLeftAt coeffs ν Xp A i)) :=
  hμm.sub (stronglyMeasurable_markIntegralLeftAt A i hγmL).measurable
/-- The drift of a bundle along a path with the left-limit compensator over a mark set subtracted
is progressively measurable. -/
theorem progressivelyMeasurable_continuousDriftLeftAt (A : Set E) (i : Fin n)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hμp : Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (Xp s ω) i)
    (hγpL : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) :
    Probability.ProgressivelyMeasurable ℱ (continuousDriftLeftAt coeffs ν Xp A i) :=
  hμp.sub (_root_.Prove2MeSourceProof.h_36f7727cdf4c604558c9da84 A ℱ hγpL)
omit [IsProbabilityMeasure P] in
/-- The drift of a bundle along a path with the left-limit compensator over a mark set of finite
intensity subtracted has finite energy on every bounded window. -/
theorem lintegral_sq_continuousDriftLeftAt_lt_top {A : Set E} (hAν : ν A ≠ ⊤) (i : Fin n)
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖continuousDriftLeftAt coeffs ν Xp A i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sub_setIntegral_mark_lt_top hAν (fun ω s => coeffs.μ s (Xp s ω) i)
    (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) hμm hμq hγmL hγqL T hT
end Drift

section ContinuousPart

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

/-- **The continuous part of a path exists**: a continuous adapted version of the vector Itô
process with the diffusion coefficient along the path and the drift carrying the left-limit
compensator over a mark set of finite intensity. -/
theorem exists_continuousPart (S : BigJump.SdeData X) {A : Set E} (hAν : ν A ≠ ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ V : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W S.ℱ S.isBrownian
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν X.X A) V :=
  _root_.Prove2MeSourceProof.h_e40bf0e3e05fd6503919f765 W S.ℱ S.isBrownian
    (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq hℱ0 hnull0
    (X₀ := fun _ => x₀) (fun _ => measurable_const) (continuousDriftLeftAt coeffs ν X.X A)
    (fun i => measurable_uncurry_continuousDriftLeftAt A i (hμm i) (hγmL i))
    (fun i => progressivelyMeasurable_continuousDriftLeftAt A i S.ℱ (hμp i) (hγpL i))
    (fun i T hT => lintegral_sq_continuousDriftLeftAt_lt_top hAν i (hμm i) (hμq i)
      (hγmL i) (hγqL i) T hT)
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


