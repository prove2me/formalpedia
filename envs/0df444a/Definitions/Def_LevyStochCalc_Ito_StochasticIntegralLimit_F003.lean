-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F003
-- name    : LevyStochCalc_Ito_StochasticIntegralLimit_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:55:56.639609+00:00
-- url     : https://prove2.me/theorems/53a79907-ce72-4b69-bc98-124ad2811813
-- title:
--   Source declarations: LevyStochCalc.Ito.StochasticIntegralLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.StochasticIntegralLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000
import Definitions.Def_SourceProof_6043a31a9e304448bc837b3a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Compensated

section MarkCut

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m))

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark cut to the complement of a set differs from the integrand by the mark cut to the
set itself. -/
theorem markCut_compl_sub (S : Set E) (ψ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut Sᶜ ψ ω s e - ψ ω s e = -markCut S ψ ω s e := by
  by_cases h : e ∈ S <;> simp [markCut, h]
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An antitone family of mark sets whose intersection is null eventually misses almost every
mark. -/
theorem ae_eventually_notMem_of_antitone (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) :
    ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m := by
  have hset : {a : E | ¬ (a ∉ ⋂ m, A m)} = ⋂ m, A m := by
    ext a
    simp
  have hae : ∀ᵐ e ∂ν, e ∉ ⋂ m, A m := by
    rw [MeasureTheory.ae_iff, hset]
    exact hnull
  filter_upwards [hae] with e he
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, e ∉ A m₀ := by
    by_contra hcon
    exact he (Set.mem_iInter.mpr fun m => not_not.mp fun h => hcon ⟨m, h⟩)
  filter_upwards [Filter.eventually_ge_atTop m₀] with m hm
  exact fun hmem => hm₀ (hanti hm hmem)
include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of a family of
mark sets that eventually misses almost every mark converge in `L²` to the compensated
Itô–Lévy integral of the integrand. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_compl
    (hout : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m)ᶜ φ)
          (measurable_markCut h_meas (hA m).compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m).compl)
          (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') T ω
        - stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hmcut : ∀ m, Measurable fun p : Ω × ℝ × E => markCut (A m)ᶜ φ p.1 p.2.1 p.2.2 :=
    fun m => measurable_markCut h_meas (hA m).compl
  have hgm : Measurable fun p : Ω × ℝ × E => ‖φ p.1 p.2.1 p.2.2‖ := h_meas.norm
  have hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => markCut (A m)ᶜ φ ω s e) atTop (𝓝 (φ ω s e)) := by
    refine Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s => ?_
    filter_upwards [hout] with e he
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [he] with m hm
    simp [markCut, hm]
  have hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖markCut (A m)ᶜ φ ω s e‖ ≤ ‖φ ω s e‖ := by
    intro m
    refine Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s =>
      Filter.Eventually.of_forall fun e => ?_
    rcases Classical.em (e ∈ A m) with hm | hm
    · have hz : markCut (A m)ᶜ φ ω s e = 0 := by simp [markCut, hm]
      rw [hz, norm_zero]
      exact norm_nonneg _
    · have hid : markCut (A m)ᶜ φ ω s e = φ ω s e := by simp [markCut, hm]
      rw [hid]
  have hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖‖φ ω s e‖‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    simpa using h_sq T hT
  refine (_root_.Prove2MeSourceProof.h_6043a31a9e304448bc837b3a (φ := fun m => markCut (A m)ᶜ φ)
    (φ₀ := φ) (g := fun ω s e => ‖φ ω s e‖) hmcut h_meas hgm hpt hdom hg).congr fun m => ?_
  exact (itoIsometry_diff_compensated N ℱ hℱ (markCut (A m)ᶜ φ) φ (hmcut m) h_meas
    ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m).compl) h_progMeas
    (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') h_sq T hT).symm
include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of an antitone
family of mark sets whose intersection is null converge in `L²` to the compensated Itô–Lévy
integral of the integrand. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_compl_of_antitone
    (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m)ᶜ φ)
          (measurable_markCut h_meas (hA m).compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m).compl)
          (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') T ω
        - stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  tendsto_lintegral_sq_stochasticIntegral_markCut_compl N ℱ hℱ φ h_meas h_progMeas h_sq A hA
    (ae_eventually_notMem_of_antitone A hanti hnull) hT
end MarkCut

end LevyStochCalc.Ito.IntegralLimit


