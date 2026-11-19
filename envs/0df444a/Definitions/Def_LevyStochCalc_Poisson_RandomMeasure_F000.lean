-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
-- name    : LevyStochCalc_Poisson_RandomMeasure_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:48:49.880109+00:00
-- url     : https://prove2.me/theorems/bcb722a9-42bb-41f1-83de-11978d21869c
-- title:
--   Source declarations: LevyStochCalc.Poisson.RandomMeasure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.RandomMeasure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Basic_F000
import Definitions.Def_LevyStochCalc_Basic_F001
import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson random measure on `[0, ∞) × E`

A *Poisson random measure* on the time-space `[0, ∞) × E` (where `E` is a
measurable mark space with σ-finite intensity `ν`), defined over a
probability space `(Ω, P)`, is a measurable family

  `N : Ω → Measure (ℝ × E)`

with the following properties:

* For each measurable `B ⊆ ℝ × E` with `(volume.restrict [0,∞) ⊗ ν)(B) < ∞`,
  `N(·, B) ~ Poisson` with mean equal to that intensity.
* For any pairwise-disjoint family of such sets, the random variables
  `(N(·, B_i))_i` are independent under `P`.

This is the time-aware structure required for the *compensated* integral
`∫_0^t ∫_E φ(s, e) Ñ(ds, de)` to be well-defined.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009, §2.3, Thm 2.3.1.
* Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion Processes*,
  North-Holland 1989, §I.8.
* Sato, *Lévy Processes and Infinitely Divisible Distributions*,
  Cambridge 1999, §19.

## Construction

The intensity is `volume.restrict (Set.Ici 0) ⊗ ν` (Lebesgue restricted to `[0, ∞)` tensor `ν`
on the mark space). `PoissonRandomMeasure.exists_of_sigmaFinite` builds a Poisson random
measure by the Poisson recipe: the time-space is cut into the cells `[n, n+1) × sₘ` of a
σ-finite decomposition, each cell of positive intensity carries a Poisson number of
independent marks distributed according to the normalised intensity, and the cells are
superposed (`LevyStochCalc.Poisson.superposition`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Poisson distribution `Poisson(μ)` viewed as a measure on `ℝ≥0∞` (via
the natural inclusion `ℕ ↪ ℝ≥0∞`). Convenience for stating
`P.map (N · A) = …` since `N(·, A) : Ω → ℝ≥0∞` (an extended-real count). -/
noncomputable def poissonMeasureENN (μ : ℝ≥0) : Measure ℝ≥0∞ :=
  (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))
/-- The reference intensity on `ℝ × E`: Lebesgue on `[0, ∞)` tensor `ν` on
the mark space. -/
noncomputable def referenceIntensity {E : Type v} [MeasurableSpace E]
    (ν : Measure E) : Measure (ℝ × E) :=
  (volume.restrict (Set.Ici (0 : ℝ))).prod ν
/-- A *Poisson random measure on `[0, ∞) × E`* with intensity
`volume.restrict [0,∞) ⊗ ν`, defined over a probability space `(Ω, P)`.

The Applebaum (2009) Definition 2.3.1 properties are: (a) `N(·, A)` is
Poisson-distributed (captured by `poisson_law`); (b) disjoint-family values
are independent (captured by `independent_disjoint`); (c) `N(ω, ·)` is an
integer-valued atomic measure.

Of (c) the fields below record only the following. For each fixed region of
finite intensity, `integer_valued` gives an almost surely integer value, with an
exceptional null set that depends on that region; there is therefore no single
null set outside which `N ω` is integer-valued on every region at once.
Atomicity is not a field. The simultaneous integer-valued statement on a window
of finite intensity is `Poisson.ae_isIntegerValued_restrict`, and the matching
atomicity — a finite sum of Dirac masses — is `Poisson.ae_exists_eq_sum_dirac`,
both in `Poisson/Atomic.lean` and both under additional countable-generation
hypotheses on the mark space. -/
structure PoissonRandomMeasure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν] where
  /-- The underlying ω-indexed family of measures on `ℝ × E`. -/
  N : Ω → Measure (ℝ × E)
  /-- For each measurable `B ⊆ ℝ × E`, the map `ω ↦ N(ω, B)` is measurable. -/
  measurable_eval : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    Measurable (fun ω => N ω B)
  /-- **Applebaum 2.3.1(c), finite-intensity case.** For measurable `B` with
  finite intensity, `N(·, B)` is a.s. `ℕ`-valued (in the natural embedding
  `ℕ ↪ ℝ≥0∞`). Follows from `poisson_law` since the Poisson distribution
  is supported on `ℕ`. Exposed as a structural field so downstream code
  can use it without re-deriving through the Poisson-law characterisation. -/
  integer_valued : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    ∀ᵐ ω ∂P, ∃ n : ℕ, N ω B = n
  /-- **Applebaum 2.3.1(c), infinite-intensity case.** For measurable `B` with
  INFINITE intensity, `N(·, B) = ∞` almost surely. This completes the Applebaum
  2.3.1(c) encoding — `integer_valued` covers only the finite-intensity branch.
  Under the literature Poisson recipe construction,
  this is automatic: an infinite-intensity set decomposes into countably
  many finite-intensity pieces, each contributing Poisson(λ_n) atoms, with
  total count = ∑_n Poisson(λ_n) which is a.s. infinite when ∑_n λ_n = ∞. -/
  infinite_at_infinite_intensity : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B = ⊤ → ∀ᵐ ω ∂P, N ω B = ⊤
  /-- `N(·, B)` has `Poisson` law with mean `(referenceIntensity ν)(B)` under
  `P`, for every measurable `B` with finite intensity. -/
  poisson_law : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    P.map (fun ω => N ω B) = poissonMeasureENN (referenceIntensity ν B).toNNReal
  /-- For any pairwise-disjoint countable family of measurable subsets of
  `ℝ × E`, the family of evaluation random variables `(ω ↦ N(ω, B_i))_i` is
  independent under `P`.

  The `[Countable ι]` hypothesis matches the literature: standard PRM
  independence (Kallenberg 3.5.1 / Applebaum 2.3.1(b)) is for COUNTABLE
  pairwise-disjoint families. Allowing uncountable `ι` would invoke
  Mathlib's `iIndepFun` at uncountable index types, a more delicate notion
  that does not match Applebaum's formulation. -/
  independent_disjoint :
    ∀ {ι : Type*} [Countable ι] (B : ι → Set (ℝ × E)),
      (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      ProbabilityTheory.iIndepFun (fun (i : ι) (ω : Ω) => N ω (B i)) P
  /-- **σ-algebra-level past/future independence.** The σ-algebra generated by
  `{N(·, B) : B ⊆ (−∞, s] × E, B measurable}` (the "past at time `s`") is
  independent of `σ(N(·, (s, t] × A))` (a future increment).

  This is strictly stronger than `independent_disjoint` (which is iIndepFun
  for finite/countable families) and is needed to apply
  `MeasureTheory.condExp_indep_eq` in the compensated stochastic-integral
  proofs. For PRMs it follows from joint independence on disjoint subsets;
  packaged as a structural hypothesis in the same spirit as
  `BrownianMotion.joint_increment_independent`. -/
  joint_past_future_independent :
    ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ {A : Set E}, MeasurableSet A → ν A ≠ ⊤ →
      ProbabilityTheory.Indep
        (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N ω B) inferInstance)
        (MeasurableSpace.comap
          (fun ω => N ω (Set.Ioc s t ×ˢ A)) inferInstance)
        P
/-- The compensated random measure: `Ñ(B) := N(B) − ν̂(B)` where
`ν̂ := referenceIntensity ν`. Returns a real number when `ν̂(B) < ∞`. -/
noncomputable def PoissonRandomMeasure.compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) : ℝ :=
  (N.N ω B).toReal - (referenceIntensity ν B).toReal
/-- **Step 1: σ-finite decomposition of the intensity.** A σ-finite measure `ν`
on `E` decomposes as a sequence of pairwise-disjoint measurable sets each of
finite mass covering all of `E`. Built from `MeasureTheory.spanningSets` +
`Set.disjointed`. -/
lemma sigmaFinite_decomposition
    (E : Type v) [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] :
    ∃ s : ℕ → Set E,
      (∀ n, MeasurableSet (s n)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧
      (∀ n, ν (s n) < ⊤) ∧
      (⋃ n, s n) = Set.univ := by
  refine ⟨disjointed (MeasureTheory.spanningSets ν), ?_, ?_, ?_, ?_⟩
  · intro n
    exact MeasurableSet.disjointed (MeasureTheory.measurableSet_spanningSets ν) n
  · exact disjoint_disjointed _
  · intro n
    refine lt_of_le_of_lt ?_ (MeasureTheory.measure_spanningSets_lt_top ν n)
    exact MeasureTheory.measure_mono (disjointed_subset _ _)
  · rw [iUnion_disjointed]
    exact MeasureTheory.iUnion_spanningSets ν
end LevyStochCalc.Poisson


