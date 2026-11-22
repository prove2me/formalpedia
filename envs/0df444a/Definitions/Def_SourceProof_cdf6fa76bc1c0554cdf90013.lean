-- Prove2me | Definitions.Def_SourceProof_cdf6fa76bc1c0554cdf90013
-- name    : SourceProof_cdf6fa76bc1c0554cdf90013
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:07:13.833728+00:00
-- url     : https://prove2.me/theorems/ca8b8e40-320b-4227-8606-a26552a6e344
-- title:
--   LevyStochCalc source module: SourceProof_cdf6fa76bc1c0554cdf90013
-- statement:
--   The original source theorem `LevyStochCalc.Ito.BigJump.ae_forall_bigJumpPath_eq_add_jumpSumLeftAt` comes from the `LevyStochCalc.Ito.TruncatedContinuousPart` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F000
import Definitions.Def_SourceProof_ae75084e913ed280513dd96a

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


theorem _root_.Prove2MeSourceProof.h_cdf6fa76bc1c0554cdf90013 (S : SdeData X) {A : Set E}
    (hA : MeasurableSet A)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hAν : ν Aᶜ ≠ ⊤)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Filter.Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (V : ℝ → Ω → Fin n → ℝ)
    (hV : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W S.ℱ S.isBrownian
      (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
      (continuousDriftLeftAt (coeffs.markCutγ Aᶜ) ν X.X Aᶜ) V) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      bigJumpPath S hA hℱ0 hnull0 t ω i
        = V t ω i + jumpSumLeftAt (coeffs.markCutγ Aᶜ) N X.X Aᶜ t ω i := by
  have hpredL : ∀ i : Fin n, LevyStochCalc.Probability.MarkedPredictable S.ℱ ν
      (LevyStochCalc.Ito.JumpFormula.zeroExtPos fun ω s e =>
        (coeffs.markCutγ Aᶜ).γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i) := by
    intro i
    have hbase : LevyStochCalc.Probability.MarkedPredictable S.ℱ ν
        (LevyStochCalc.Ito.JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i) :=
      LevyStochCalc.Ito.JumpSplitting.markedPredictable_zeroExtPos_jumpCoeff_leftLimPathAt (ν := ν) X.X S.ℱ i hXadapt hXleft
        ((measurable_pi_apply i).comp hγmeas)
    have hrw : (fun (ω : Ω) (s : ℝ) (e : E) =>
        (coeffs.markCutγ Aᶜ).γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i)
        = LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i :=
      LevyStochCalc.Ito.BigJump.pathJumpCoeff_markCutγ Aᶜ (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X) i
    rw [hrw]
    exact LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_markCut hbase hA.compl
  have hγmLc : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      LevyStochCalc.Ito.SmallJump.pathJumpCoeff (coeffs.markCutγ Aᶜ) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X) i p.1 p.2.1 p.2.2 := by
    intro i
    rw [LevyStochCalc.Ito.BigJump.pathJumpCoeff_markCutγ]
    exact LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl
  have hγpLc : ∀ i : Fin n, LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ
      (LevyStochCalc.Ito.SmallJump.pathJumpCoeff (coeffs.markCutγ Aᶜ) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X) i) := by
    intro i
    rw [LevyStochCalc.Ito.BigJump.pathJumpCoeff_markCutγ]
    exact (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl
  have hγqLc : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Ito.SmallJump.pathJumpCoeff (coeffs.markCutγ Aᶜ) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X) i ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ := by
    intro i
    rw [LevyStochCalc.Ito.BigJump.pathJumpCoeff_markCutγ]
    exact fun T hT => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T hT
  have hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => LevyStochCalc.Ito.BigJump.bigJumpPath S hA hℱ0 hnull0 s ω) (𝓝[>] t)
        (𝓝 (LevyStochCalc.Ito.BigJump.bigJumpPath S hA hℱ0 hnull0 t ω)) := by
    filter_upwards [LevyStochCalc.Ito.BigJump.bigJumpPath_ae_cadlag S hA hℱ0 hnull0] with ω hω t ht
    exact (hω t ht).1
  exact _root_.Prove2MeSourceProof.h_2afb1f68a5c9c19e7519fbb0 (coeffs.markCutγ Aᶜ) N X.X x₀ S.ℱ S.isBrownian
    S.σ_meas S.σ_prog S.σ_sq S.isPoisson
    (fun i => LevyStochCalc.Ito.BigJump.measurable_pathJumpCoeff_markCutγ_compl S hA i)
    (fun i => LevyStochCalc.Ito.BigJump.markedProg_pathJumpCoeff_markCutγ_compl S hA i)
    (fun i => LevyStochCalc.Ito.BigJump.sq_pathJumpCoeff_markCutγ_compl (A := A) S i) hγmLc hγpLc hγqLc
    (LevyStochCalc.Ito.BigJump.bigJumpPath S hA hℱ0 hnull0) X.cadlag_paths hZright
    (fun t ht => MeasureTheory.ae_all_iff.mpr fun i =>
      (_root_.Prove2MeSourceProof.h_ae75084e913ed280513dd96a S hA hℱ0 hnull0 i).decomposition t ht)
    hA.compl hAν (LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ_eq_zero coeffs Aᶜ) hpredL hμm hμq V
    hV.ae_forall_coord_eq hV.ae_forall_tendsto_nhdsGT
end LevyStochCalc.Ito.BigJump


