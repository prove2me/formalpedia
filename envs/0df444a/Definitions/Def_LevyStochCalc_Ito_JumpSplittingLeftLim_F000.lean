-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplittingLeftLim_F000
-- name    : LevyStochCalc_Ito_JumpSplittingLeftLim_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:54:29.478663+00:00
-- url     : https://prove2.me/theorems/efbfff2f-708e-4313-bbf7-25f801b56da7
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSplittingLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSplittingLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002
import Definitions.Def_SourceProof_e3c42a21d6369475ce8bd189

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting along the left limits of the path

The jump coefficient of a jump diffusion can be evaluated along the left limits of the path
instead of along the path itself. The two integrands agree off a countable set of times, so they
have the same compensated integral, while the pathwise integral against the random measure and
the compensator against the reference intensity are both taken with the left-limit integrand.
The drift carrying the compensator of the left-limit integrand agrees with the drift carrying
that of the path integrand at almost every time of every horizon, so the two build the same
vector Itô process.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPath` — the left limits of the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeft` — the pathwise sum of the jumps carried by a mark
  set over a time window, with the jump coefficient evaluated at the left limits of the path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeft` — the drift of a jump diffusion with the
  compensator of the left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSumLeft_nhdsWithin_Ioi` — the left-limit jump sum
  over `(0, ·]` is right-continuous in time.
* `LevyStochCalc.Ito.JumpSplitting.ae_ae_restrict_continuousDriftLeft_eq` and
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_vectorItoProcess_continuousDriftLeft_eq` — the two
  drifts agree at almost every time of every horizon, hence build the same vector Itô process.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section WindowContinuity

variable {E : Type v} [MeasurableSpace E]

end WindowContinuity

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left limits of the path of a jump diffusion. -/
noncomputable def leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (s : ℝ) (ω : Ω) :
    Fin n → ℝ :=
  Function.leftLim (fun r => X.X r ω) s
/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`, with the
jump coefficient evaluated at the left limits of the path. -/
noncomputable def jumpSumLeft (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (t : ℝ)
    (ω : Ω) (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i ∂(N.N ω)
/-- The drift of a jump diffusion with the compensator of the jumps carried by `A` subtracted,
the jump coefficient being evaluated at the left limits of the path. -/
noncomputable def continuousDriftLeft (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  coeffs.μ s (X.X s ω) i - ∫ e in A, coeffs.γ s (leftLimPath X s ω) e i ∂ν
/-- The left-limit jump sum over the degenerate window vanishes. -/
theorem jumpSumLeft_zero (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (ω : Ω)
    (i : Fin n) : jumpSumLeft X A 0 ω i = 0 := by
  simp [jumpSumLeft]
section Cadlag

/-- A path converging in each coordinate along the filter of times strictly below a given time
has that limit as its left limit there. -/
theorem leftLimPath_eq_of_tendsto {X : Setting.JumpDiffusion W N coeffs x₀} {ω : Ω} {t : ℝ}
    {L : Fin n → ℝ} (hL : ∀ i : Fin n, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 (L i))) :
    leftLimPath X t ω = L := by
  change Function.leftLim (fun r => X.X r ω) t = L
  exact leftLim_eq_of_tendsto (tendsto_pi_nhds.mpr hL)
/-- A path with left limits in each coordinate at a given time converges there to its left
limits. -/
theorem tendsto_nhdsLT_leftLimPath {X : Setting.JumpDiffusion W N coeffs x₀} {ω : Ω} {t : ℝ}
    (h : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 (leftLimPath X t ω i)) := by
  classical
  choose L hL using h
  rw [leftLimPath_eq_of_tendsto hL]
  exact hL i
/-- The path of a jump diffusion almost surely meets its left limits at all but countably many
positive times. -/
theorem ae_countable_setOf_pos_ne_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) :
    ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ leftLimPath X s ω ≠ X.X s ω}.Countable := by
  filter_upwards [X.cadlag_paths] with ω hω
  refine Set.Countable.mono ?_ (_root_.Prove2MeSourceProof.h_27ffb6837c072f81fc480f19
    (f := fun s => X.X s ω) (g := fun s => leftLimPath X s ω)
    (fun t ht => (hω t ht).1) (fun t ht i => tendsto_nhdsLT_leftLimPath (hω t ht.le).2 i))
  intro s hs
  exact ⟨hs.1, fun h => hs.2 h.symm⟩
/-- The drift carrying the left-limit compensator meets the drift carrying the point-evaluated
compensator at almost every time of every horizon. -/
theorem ae_ae_restrict_continuousDriftLeft_eq (X : Setting.JumpDiffusion W N coeffs x₀)
    (A : Set E) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      continuousDriftLeft X A i ω s = continuousDrift X A i ω s := by
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPath X] with ω hω T
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  simp only [continuousDriftLeft, continuousDrift, hs]
end Cadlag

section Window

/-- The left-limit jump sum over `(0, ·]` is right-continuous in time along a path whose
left-limit jump coefficient is integrable over every bounded window. -/
theorem tendsto_jumpSumLeft_nhdsWithin_Ioi (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {i : Fin n}
    (hγmL : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
    {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Tendsto (fun s => jumpSumLeft X A s ω i) (𝓝[>] t) (𝓝 (jumpSumLeft X A t ω i)) := by
  have hfm : Measurable fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i :=
    hγmL.comp measurable_prodMk_left
  exact _root_.Prove2MeSourceProof.h_e3c42a21d6369475ce8bd189 hA hfm hint t
end Window

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The vector Itô processes built from the two drifts agree at every nonnegative time. -/
theorem ae_forall_vectorItoProcess_continuousDriftLeft_eq (A : Set E) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ) (i : Fin n),
      LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
          (continuousDriftLeft X A) t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
          (continuousDrift X A) t ω i := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
    ae_ae_restrict_continuousDriftLeft_eq X A i] with ω hω
  intro t i
  simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
  rw [integral_congr_ae (hω i t)]
end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


