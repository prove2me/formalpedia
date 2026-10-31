-- Prove2me | Definitions.Def_LeGallBrownianMap_IsLeftIncreaseTime
-- name    : LeGallBrownianMap_IsLeftIncreaseTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:54.823959+00:00
-- url     : https://prove2.me/theorems/f8661675-e0cf-4049-9e87-32c0b621ceea
-- title:
--   Left-increase times
-- statement:
--   A time $t\in(0,1]$ is a **left-increase time** of a path $f$ on $[0,1]$ if there is $\varepsilon\in(0,t)$ with $f(s)\ge f(t)$ for every $s\in[t-\varepsilon,t]$.
--
--   For the excursion $e$, $t$ is neither a left- nor a right-increase time iff its $\sim_e$-class is a singleton (a leaf of the CRT).
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.14

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.14:
"We say that t ∈ (0, 1] is a left-increase time of e, respectively of Z, if there exists
ε ∈ (0, t) such that e_s ≥ e_t, respectively Z_s ≥ Z_t, for every s ∈ [t − ε, t]."

`IsLeftIncreaseTime f t` is this property of a path `f : [0,1] → ℝ` at `t`. -/
def IsLeftIncreaseTime (f : unitInterval → ℝ) (t : unitInterval) : Prop :=
  0 < (t : ℝ) ∧ ∃ ε : ℝ, 0 < ε ∧ ε < t ∧
    ∀ s : unitInterval, (t : ℝ) - ε ≤ s → s ≤ t → f t ≤ f s

end LeGallBrownianMap


