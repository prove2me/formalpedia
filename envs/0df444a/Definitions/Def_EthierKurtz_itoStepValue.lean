-- Prove2me | Definitions.Def_EthierKurtz_itoStepValue
-- name    : EthierKurtz_itoStepValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:48:03.78564+00:00
-- url     : https://prove2.me/theorems/1f753f26-3eb3-4c24-8be8-5d6762b3be19
-- title:
--   Dyadic predictable step integrand
-- statement:
--   The bounded predictable step function on a uniform dyadic partition with coefficients measurable at left endpoints.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 2, printed pp. 280, 282–283, 286 (PDF pp. 289, 291–292, 295).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- An elementary predictable integrand on the uniform partition of [0,t].
Its coefficient a k is measurable at the LEFT endpoint k*t/2^n. -/
noncomputable def itoStepValue (t : ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ)
    (u : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    if (k : ℝ) * t.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n then a k ω else 0

end EthierKurtz


