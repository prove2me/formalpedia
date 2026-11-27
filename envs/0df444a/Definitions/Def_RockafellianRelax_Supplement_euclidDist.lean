-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_euclidDist
-- name    : RockafellianRelax_Supplement_euclidDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:10:55.206799+00:00
-- url     : https://prove2.me/theorems/2a22731b-8493-422b-8fc0-2fe1a45e5e00
-- title:
--   Euclidean point-to-set distance
-- statement:
--   For $\bar x \in \mathbb R^\iota$, with $\iota$ finite, and $C \subseteq \mathbb R^\iota$, the **point-to-set distance** is
--
--   $$
--   \operatorname{dist}(\bar x, C) = \inf\{\|x - \bar x\|_2 \mid x \in C\}\quad (C \ne \emptyset), \qquad \operatorname{dist}(\bar x,\emptyset) = \infty .
--   $$
--
--   It is the left-hand side of the error bound (4.5).
--
--   **Formalization Note** The value is an extended nonnegative real (`Metric.infEDist` in Euclidean space), so the distance to the empty set is $+\infty$, as in the paper.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §4.1, p.12 (point-to-set distance)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **Euclidean point-to-set distance.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §4.1, p.12: "dist(x̄, C) = inf{‖x − x̄‖₂ | x ∈ C} if
C ≠ ∅ and dist(x̄, C) = ∞ otherwise."

**Formalization Note.** The value is in `ℝ≥0∞`: `Metric.infEDist` in `EuclideanSpace ℝ ι`, which is
`⊤` on the empty set. `Metric.infDist`, which is `0` there, is not used. -/
noncomputable def euclidDist {ι : Type*} [Fintype ι] (x : ι → ℝ) (C : Set (ι → ℝ)) : ENNReal :=
  Metric.infEDist (WithLp.toLp 2 x : EuclideanSpace ℝ ι)
    ((fun c => (WithLp.toLp 2 c : EuclideanSpace ℝ ι)) '' C)

end RockafellianRelax.Supplement


