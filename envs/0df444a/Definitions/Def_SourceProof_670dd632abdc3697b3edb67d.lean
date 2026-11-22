-- Prove2me | Definitions.Def_SourceProof_670dd632abdc3697b3edb67d
-- name    : SourceProof_670dd632abdc3697b3edb67d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:35:55.827656+00:00
-- url     : https://prove2.me/theorems/d7fc4e44-1dad-480e-9a25-29f26f4e97ce
-- title:
--   LevyStochCalc source module: SourceProof_670dd632abdc3697b3edb67d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` comes from the `LevyStochCalc.Ito.JumpFormulaLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The small-jump limit of the Itô–Lévy formula

The finite-activity Itô–Lévy formula applies to a jump diffusion whose jump coefficient is cut to
a set of marks. Along a family `A : ℕ → Set E` of small-jump sets with `ν`-null intersection the
cut coefficients restore the original ones, and the formula is passed to the limit term by term:
the increment of the state function and the drift, diffusion and compensated jump terms converge
along the truncated paths, and the compensator-drift term converges by dominated convergence on
the product of the time window with the intensity. The identity of the limits is then the
uniqueness of the limit of a real sequence, read on the two sides of the formula.

Cutting the jump coefficient to a set of marks leaves the drift integrand `∂_t u + 𝓛u` unchanged
— it reads only `μ` and `σ` — and turns the compensator-drift integrand into its restriction to
that set. The two presentations of the drift differ by the first-order term `∑ᵢ ∂ᵢu ∫ γᵢ dν`,
which is finite only when the jump coefficient is `ν`-integrable: for a jump coefficient that is
merely square-integrable near the small marks, the first-order term and the mark integral of the
jump increment `u(x + γ) − u(x)` each diverge and only their difference, the compensator-drift
integrand `u(x + γ) − u(x) − γᵀ∇u`, is integrable. The limit statements below are therefore
carried by the compensator-drift integrand; the first-order term is passed to the limit
separately only under an integrability hypothesis on the jump coefficient itself.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.markTruncCoeffs` — the coefficient bundle with the jump
  coefficient cut to a set of marks.
* `LevyStochCalc.Ito.JumpFormula.firstOrderIntegrand` — the first-order term `∑ᵢ γᵢ ∂ᵢu` of the
  compensator-drift integrand.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_of_antitone`,
  `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp` — almost every mark eventually lies
  outside an antitone family of mark sets with null intersection, also along a subsequence.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` — dominated convergence for
  the mark integral over the complements of the family, integrated over a time window.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_compensatorDrift` — the compensator-drift
  integrals over the complements of the family converge to the compensator-drift integral over
  the whole mark space along the limit path.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_firstOrder` — the same for the first-order
  term, under integrability of the jump coefficient against the intensity.
* `LevyStochCalc.Ito.JumpFormula.driftIntegrand_markTruncCoeffs`,
  `LevyStochCalc.Ito.JumpFormula.integral_compensatorDriftIntegrand_markTruncCoeffs` — cutting
  the jump coefficient leaves the drift integrand unchanged and restricts the compensator-drift
  integral to the cut.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_sub_of_markTruncCoeffs` — the Itô–Lévy identity for cut
  coefficients, in the vocabulary of the uncut ones.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto` — the two sides of an identity of
  real sequences have equal limits, pointwise and almost surely.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_terms` — the Itô–Lévy identity along
  the limit path, from the identities along the truncated paths with the drift and
  compensator-drift terms given as arbitrary sequences, and the convergence of the five terms.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_integrals` — the same with the drift
  and compensator-drift terms given as the integrals along the truncated paths, the latter over
  the complements of the truncated mark sets.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., 2009, Theorem 4.4.7, step (II).
-/

open MeasureTheory Filter Topology
open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section MarkSets

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

end MarkSets

section Dominated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_670dd632abdc3697b3edb67d
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by
  classical
  have hwin : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      p.1 ∈ Set.Icc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hevp : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ∀ᶠ m in atTop, p.2 ∉ A m :=
    Measure.quasiMeasurePreserving_snd.ae hev
  have hSm : ∀ m, MeasurableSet {p : ℝ × E | p.2 ∈ (A m)ᶜ} := fun m =>
    measurable_snd (hA m).compl
  set F : ℕ → ℝ × E → ℝ :=
    fun m => {p : ℝ × E | p.2 ∈ (A m)ᶜ}.indicator (fun q => fs m q.1 q.2) with hF
  have hFmeas : ∀ m, AEStronglyMeasurable (F m)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    fun m => (hmeas m).indicator (hSm m)
  have hbound : ∀ m, ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖F m p‖ ≤ g p.1 p.2 := by
    intro m
    filter_upwards [hwin] with p hp
    have hle : |fs m p.1 p.2| ≤ g p.1 p.2 := hdom m p.1 hp p.2
    by_cases hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ}
    · rw [hF]
      simp only [Set.indicator_of_mem hpS, Real.norm_eq_abs]
      exact hle
    · rw [hF]
      simp only [Set.indicator_of_notMem hpS, norm_zero]
      exact le_trans (abs_nonneg _) hle
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      Tendsto (fun m => F m p) atTop (𝓝 (f p.1 p.2)) := by
    filter_upwards [hwin, hevp] with p hp hpe
    refine Tendsto.congr' ?_ (hconv p.1 hp p.2)
    filter_upwards [hpe] with m hm
    have hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ} := hm
    rw [hF]
    simp only [Set.indicator_of_mem hpS]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) (F := F)
    (f := fun p : ℝ × E => f p.1 p.2) (fun p : ℝ × E => g p.1 p.2)
    hFmeas hg hbound hlim
  have hLHS : ∀ m, ∫ p, F m p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν := by
    intro m
    have hint : Integrable (F m) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
      hg.mono' (hFmeas m) (hbound m)
    rw [integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change ∫ e, F m (s, e) ∂ν = ∫ e in (A m)ᶜ, fs m s e ∂ν
    have hfun : (fun e => F m (s, e)) = ((A m)ᶜ).indicator (fun e => fs m s e) := by
      funext e
      by_cases he : e ∈ (A m)ᶜ
      · rw [hF]
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (show (s, e) ∈
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
      · rw [hF]
        simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem (show (s, e) ∉
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
    rw [hfun, integral_indicator (hA m).compl]
  have hmlim : AEStronglyMeasurable (fun p : ℝ × E => f p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hblim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖f p.1 p.2‖ ≤ g p.1 p.2 := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hbound, hlim] with p hb hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hb)
  have hRHS : ∫ p, f p.1 p.2 ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν :=
    integral_prod _ (hg.mono' hmlim hblim)
  simp_rw [hLHS] at hDCT
  rwa [hRHS] at hDCT
end Dominated

section Continuity

variable {n : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}
  {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end Continuity

section CompensatorDriftLimit

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end CompensatorDriftLimit

section MarkTruncation

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ}

end MarkTruncation

section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Assembly

end LevyStochCalc.Ito.JumpFormula


