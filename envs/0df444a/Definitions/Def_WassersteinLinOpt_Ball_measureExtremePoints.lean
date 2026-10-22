-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_measureExtremePoints
-- name    : WassersteinLinOpt_Ball_measureExtremePoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:39:53.850178+00:00
-- url     : https://prove2.me/theorems/d1f86a4b-a97f-4b5f-8138-9c30fe9aefb8
-- title:
--   Extreme points $\mathrm{ext}(\mathcal F)$ of a set of measures
-- statement:
--   For a set $\mathcal F$ of measures on a measurable space $Z$, a measure $\gamma\in\mathcal F$ is an **extreme point** of $\mathcal F$ if it is not a proper convex combination of two other members: whenever
--
--   $$\gamma=t\,\gamma_1+(1-t)\,\gamma_2,\qquad \gamma_1,\gamma_2\in\mathcal F,\ t\in(0,1),$$
--
--   then $\gamma_1=\gamma_2=\gamma$. $\mathrm{ext}(\mathcal F)$ is the set of extreme points.
--
--   **Formalization Note.** Measures form a cone over $[0,\infty]$, not a real vector space, so Mathlib's `Set.extremePoints ℝ` does not apply; the definition is written out with `t : ℝ≥0`, `0 < t < 1`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1120 (definition of ext(𝓕) below problem (11))

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- `ext(𝓕)` (p. 1120): the extreme points of a set `𝓕` of measures. `γ ∈ 𝓕` is extreme if
`γ = t γ₁ + (1 − t) γ₂` with `γ₁, γ₂ ∈ 𝓕` and `t ∈ (0, 1)` forces `γ₁ = γ₂ = γ`. Measures form
a cone, not a real vector space, so this is written out instead of using `Set.extremePoints ℝ`. -/
def measureExtremePoints {Z : Type*} [MeasurableSpace Z] (F : Set (Measure Z)) :
    Set (Measure Z) :=
  {γ | γ ∈ F ∧ ∀ γ₁ ∈ F, ∀ γ₂ ∈ F, ∀ t : ℝ≥0, 0 < t → t < 1 →
      γ = t • γ₁ + (1 - t) • γ₂ → γ₁ = γ ∧ γ₂ = γ}

end WassersteinLinOpt.Ball


