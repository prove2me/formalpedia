-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
-- name    : KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:09:32.342989+00:00
-- url     : https://prove2.me/theorems/c5dc833c-d393-4ec9-b0f6-398fed4c30d8
-- title:
--   Finite-sum compensated step integrals
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `stepIntegral` is the finite sum of the compensated integrals of a family of `SimplePredictable` integrands, for a probability measure $P$ and sigma-finite mark measure $\nu$. Under strong measurability of the coefficients at their partition endpoints and an `IsPoissonFiltration` hypothesis, `martingale_stepIntegral_compensated` states that this finite-sum process is a martingale. `compensated_inter_add_diff_ae` gives almost-everywhere additivity of compensated masses over $B\cap C$ and $B\setminus C$ when both sets are measurable and the reference intensity of $B$ is finite, with the required `toReal` conversions.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensityStepIntegral.lean#L34-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedDensityStepIntegral`, definition bundle `KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensityStepIntegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- The compensated integral of a **finite family** of simple predictable
integrands: `∑ⱼ ∫ φⱼ dÑ`. -/
noncomputable def stepIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j, simpleIntegral N (Φ j) t ω
/-- A finite family of adapted simple predictables integrates to a martingale on the
natural filtration (the finite sum of the per-piece compensated martingales). -/
lemma martingale_stepIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((Φ j).partition i.castSucc))
        ((Φ j).ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => stepIntegral N Φ t)
      ℱ P := by
  have hfun : (fun t : ℝ => stepIntegral N Φ t)
      = ∑ j : Fin k, (fun t : ℝ => simpleIntegral N (Φ j) t) := by
    funext t ω
    simp only [stepIntegral, Finset.sum_apply]
  rw [hfun]
  have hmart : ∀ s : Finset (Fin k),
      MeasureTheory.Martingale (∑ j ∈ s, fun t : ℝ => simpleIntegral N (Φ j) t)
        ℱ P := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        exact MeasureTheory.martingale_zero ℝ _ P
    | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (martingale_simpleIntegral_compensated N ℱ hℱ (Φ j) (h_adapt j)).add ih
  exact hmart Finset.univ
/-- **Compensated additivity over `inter`/`diff`** (a.e.). For measurable `B` with
finite intensity and measurable `C`, `Ñ(B) = Ñ(B ∩ C) + Ñ(B ∖ C)` a.e. (where the
`ℕ`-valued count `N(·,B)` is finite). Measure additivity (`measure_inter_add_diff`)
in `toReal`. -/
lemma compensated_inter_add_diff_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated B ω)
      =ᵐ[P] (fun ω => N.compensated (B ∩ C) ω + N.compensated (B \ C) ω) := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hBfin : N.N ω B ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hint_ne : N.N ω (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.inter_subset_left)
  have hdiff_ne : N.N ω (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.sdiff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hrefdiff : LevyStochCalc.Poisson.referenceIntensity ν (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  rw [show N.N ω B = N.N ω (B ∩ C) + N.N ω (B \ C) from
        (measure_inter_add_sdiff (μ := N.N ω) B hC).symm,
      show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C)
            + LevyStochCalc.Poisson.referenceIntensity ν (B \ C) from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hC).symm,
      ENNReal.toReal_add hint_ne hdiff_ne, ENNReal.toReal_add hrefint hrefdiff]
  ring
end Compensated
end Poisson
end LevyStochCalc


