-- Prove2me | Definitions.Def_ConstrSOSP_IsProj
-- name    : ConstrSOSP_IsProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:30.558201+00:00
-- url     : https://prove2.me/theorems/ce43147b-81ac-43d3-846a-6efdc479d1b6
-- title:
--   Euclidean projection $\pi_{\mathcal X}(v)$
-- statement:
--   A point $w$ is a **Euclidean projection** of $v$ onto $\mathcal X$ if $w\in\mathcal X$ and $\|w-v\|\le\|w'-v\|$ for every $w'\in\mathcal X$, i.e. $w\in\arg\min_{w\in\mathcal X}\|w-v\|^2=\pi_{\mathcal X}(v)$.
--
--   **Formalization Note** Stated as a relation, without choosing a minimizer; for a nonempty closed convex $\mathcal X$ the projection exists and is unique.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), (Prox-Gradient), p.19

import Mathlib
import Definitions.Def_ApproxVI_euclNorm

namespace ConstrSOSP

/-- **Euclidean projection** (arXiv:2604.02285, 2 Nov 2026, (Prox-Gradient), p.19:
"π_X(v) := arg min_{w∈X} ‖w − v‖²").

`IsProj X v w` says that `w` is a nearest point of `X` to `v` in the Euclidean norm: `w ∈ X` and
`‖w − v‖ ≤ ‖w' − v‖` for every `w' ∈ X`.

**Formalization Note** Stated as a relation, without a choice of minimizer. For a nonempty closed
convex `X` (every nonempty polytope) the nearest point exists and is unique, so the relation is
the paper's function `π_X`. -/
def IsProj {d : ℕ} (X : Set (Fin d → ℝ)) (v w : Fin d → ℝ) : Prop :=
  w ∈ X ∧ ∀ w' ∈ X, ApproxVI.euclNorm (w - v) ≤ ApproxVI.euclNorm (w' - v)

end ConstrSOSP


