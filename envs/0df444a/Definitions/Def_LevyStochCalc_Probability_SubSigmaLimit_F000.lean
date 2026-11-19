-- Prove2me | Definitions.Def_LevyStochCalc_Probability_SubSigmaLimit_F000
-- name    : LevyStochCalc_Probability_SubSigmaLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:09:30.998536+00:00
-- url     : https://prove2.me/theorems/3b03ed42-7081-4a85-bdf8-f16a4405c583
-- title:
--   Source declarations: LevyStochCalc.Probability.SubSigmaLimit
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.SubSigmaLimit, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere limits for a sub-σ-algebra

The set on which a sequence of functions converges is measurable for the σ-algebra the functions
are measurable for, so the limit taken there and `0` elsewhere is an everywhere-limit of
functions measurable for that σ-algebra. An almost-everywhere pointwise limit of functions
strongly measurable for a sub-σ-algebra is therefore almost everywhere equal to a function
strongly measurable for it.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

variable {Ω E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
variable {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- The set on which a sequence of functions converges. -/
def convSet (g : ℕ → Ω → E) : Set Ω := {x | ∃ c, Tendsto (fun n => g n x) atTop (𝓝 c)}
omit [CompleteSpace E] in
theorem mem_convSet {g : ℕ → Ω → E} {ω : Ω} :
    ω ∈ convSet g ↔ ∃ c, Tendsto (fun n => g n ω) atTop (𝓝 c) := Iff.rfl
/-- The limit of a sequence of functions where it converges, and `0` elsewhere. -/
noncomputable def limitOn (g : ℕ → Ω → E) : Ω → E :=
  (convSet g).indicator fun x => limUnder atTop fun n => g n x
omit [CompleteSpace E] in
theorem tendsto_indicator_limitOn (g : ℕ → Ω → E) (ω : Ω) :
    Tendsto (fun n => (convSet g).indicator (g n) ω) atTop (𝓝 (limitOn g ω)) := by
  by_cases hω : ω ∈ convSet g
  · obtain ⟨c, hc⟩ := mem_convSet.mp hω
    have hval : limitOn g ω = c := by
      simp only [limitOn, Set.indicator_of_mem hω]
      exact hc.limUnder_eq
    have hind : ∀ n, (convSet g).indicator (g n) ω = g n ω :=
      fun n => Set.indicator_of_mem hω (g n)
    rw [hval]
    simpa only [hind] using hc
  · have hind : ∀ n, (convSet g).indicator (g n) ω = 0 :=
      fun n => Set.indicator_of_notMem hω (g n)
    have hval : limitOn g ω = 0 := Set.indicator_of_notMem hω _
    rw [hval]
    simpa only [hind] using tendsto_const_nhds
theorem stronglyMeasurable_limitOn {g : ℕ → Ω → E} (hg : ∀ n, StronglyMeasurable[m] (g n)) :
    StronglyMeasurable[m] (limitOn g) := by
  have hC : MeasurableSet[m] (convSet g) :=
    MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hg
  exact stronglyMeasurable_of_tendsto atTop (fun n => (hg n).indicator hC)
    (tendsto_pi_nhds.mpr (tendsto_indicator_limitOn g))
/-- **An almost-everywhere limit for a sub-σ-algebra.** An almost-everywhere pointwise limit of
functions strongly measurable for `m` is almost everywhere equal to an `m`-strongly-measurable
function. -/
theorem aestronglyMeasurable_of_tendsto_ae_sub {g : ℕ → Ω → E}
    (hg : ∀ n, StronglyMeasurable[m] (g n)) {f : Ω → E}
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (f ω))) :
    AEStronglyMeasurable[m] f μ := by
  refine ⟨limitOn g, stronglyMeasurable_limitOn hg, ?_⟩
  filter_upwards [hlim] with ω hω
  have hmem : ω ∈ convSet g := ⟨f ω, hω⟩
  simp only [limitOn, Set.indicator_of_mem hmem]
  exact hω.limUnder_eq.symm
end LevyStochCalc.Probability


