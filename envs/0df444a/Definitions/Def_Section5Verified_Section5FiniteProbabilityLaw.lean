-- Prove2me | Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
-- name    : Section5Verified_Section5FiniteProbabilityLaw
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:08.372017+00:00
-- url     : https://prove2.me/theorems/e0e23c18-68b3-532c-b82e-137e468e52b1
-- title:
--   Section5FiniteProbabilityLaw — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5FiniteProbabilityLaw; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Finite real probability weights as an actual probability measure, with
exact finite-sum integral and event-probability formulas. -/

namespace Section5FiniteProbability

open MeasureTheory

variable {Ω : Type*} [Fintype Ω]

noncomputable def mass (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) : PMF Ω :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x),hs]
    simp)



noncomputable def law [MeasurableSpace Ω] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x=1) : Measure Ω := (mass p hp hs).toMeasure

instance law_probability [MeasurableSpace Ω] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x=1) : IsProbabilityMeasure (law p hp hs) :=
  inferInstanceAs (IsProbabilityMeasure (mass p hp hs).toMeasure)





end Section5FiniteProbability

end


