-- Prove2me | Definitions.Def_LeGallBrownianMap_IsRightIncreaseTime
-- name    : LeGallBrownianMap_IsRightIncreaseTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:57.21823+00:00
-- url     : https://prove2.me/theorems/cf8b6f20-6a88-41b6-9294-b5ca1d0be184
-- title:
--   Right-increase times
-- statement:
--   A time $t\in[0,1)$ is a **right-increase time** of a path $f$ on $[0,1]$ if there is $\varepsilon\in(0,1-t)$ with $f(s)\ge f(t)$ for every $s\in[t,t+\varepsilon]$.
--
--   **Formalization Note** The paper defines left-increase times and says right-increase times are defined "similarly"; this is the mirror image under $s\mapsto1-s$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.14

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.14:
"We similarly define the notion of a right-increase time" (after the definition of a
left-increase time: "t ∈ (0, 1] is a left-increase time of e, respectively of Z, if there exists
ε ∈ (0, t) such that e_s ≥ e_t, respectively Z_s ≥ Z_t, for every s ∈ [t − ε, t]").

`IsRightIncreaseTime f t`: `t ∈ [0, 1)` and there is `ε ∈ (0, 1 − t)` with `f s ≥ f t` for every
`s ∈ [t, t + ε]`.

**Formalization Note.** The mirror image of the left-increase definition under `s ↦ 1 − s`
(the paper says only "similarly"). -/
def IsRightIncreaseTime (f : unitInterval → ℝ) (t : unitInterval) : Prop :=
  (t : ℝ) < 1 ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 - t ∧
    ∀ s : unitInterval, t ≤ s → (s : ℝ) ≤ t + ε → f t ≤ f s

end LeGallBrownianMap


