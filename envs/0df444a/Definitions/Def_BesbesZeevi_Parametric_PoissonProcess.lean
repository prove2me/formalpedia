-- Prove2me | Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
-- name    : BesbesZeevi_Parametric_PoissonProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:22:32.442808+00:00
-- url     : https://prove2.me/theorems/963fb11e-266b-46f7-983d-8c1bcfd7bea6
-- title:
--   Unit-rate Poisson process
-- statement:
--   A unit-rate Poisson process $N$ is a measurable, increasing, right-continuous counting process with $N(0)=0$. On any finite sequence of disjoint consecutive intervals, its increments are independent, and an interval of length $t-s$ has a Poisson increment with mean $t-s$.
--
--   $$N(t)-N(s)\sim\operatorname{Poisson}(t-s),\qquad 0\le s\le t.$$
--
--   This supplies the randomness used by every scaled pricing policy. **Formalization Note** The process is carried by an arbitrary probability space; its joint measurability is recorded so that evaluation at the policy's random final clock is measurable.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 7 (PDF p. 9), Eq. (1) and the preceding paragraph

import Mathlib

namespace BesbesZeevi.Parametric

open MeasureTheory ProbabilityTheory

/-- A unit-rate Poisson counting process on a probability space. Time is real and only
nonnegative times are used by the pricing model. -/
structure PoissonProcess (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  prob : IsProbabilityMeasure P
  count : ℝ → Ω → ℕ
  zero : ∀ ω, count 0 ω = 0
  mono : ∀ (ω : Ω) {s t : ℝ}, 0 ≤ s → s ≤ t → count s ω ≤ count t ω
  rightContinuous : ∀ (ω : Ω) (t : ℝ), 0 ≤ t →
    ContinuousWithinAt (fun s => count s ω) (Set.Ici t) t
  measurable : ∀ t : ℝ, Measurable (count t)
  jointMeasurable : Measurable (fun z : ℝ × Ω => count z.1 z.2)
  incrementLaw : ∀ (s t : ℝ) (_ : 0 ≤ s) (hst : s ≤ t),
    Measure.map (fun ω => count t ω - count s ω) P =
      poissonMeasure ⟨t - s, sub_nonneg.mpr hst⟩
  independent : ∀ (m : ℕ) (t : Fin (m + 1) → ℝ),
    0 ≤ t 0 → (∀ i : Fin m, t (Fin.castSucc i) < t i.succ) →
    iIndepFun (fun i : Fin m => fun ω =>
      count (t i.succ) ω - count (t (Fin.castSucc i)) ω) P

end BesbesZeevi.Parametric


