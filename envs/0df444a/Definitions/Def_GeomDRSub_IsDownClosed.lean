-- Prove2me | Definitions.Def_GeomDRSub_IsDownClosed
-- name    : GeomDRSub_IsDownClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:08.247277+00:00
-- url     : https://prove2.me/theorems/ef8f6270-02d7-4a2a-a72c-6019ea3fe988
-- title:
--   Down-closed set
-- statement:
--   A set $K\subseteq\mathbb R^d$ is **down-closed** if $x\in K$ and $0\le y\le x$ imply $y\in K$, where the vector inequalities are coordinatewise: $0\le y_i\le x_i$ for every $i$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8

import Mathlib

namespace GeomDRSub

/-- **Down-closed set.** Aggarwal–Lu, arXiv:2610.00545, Section 3.1, p.8: `K` is down-closed,
"meaning that `x ∈ K` and `0 ≤ y ≤ x` imply `y ∈ K`".

**Formalization Note.** The vector inequalities are coordinatewise (p.8), written out over
`Fin d`. -/
def IsDownClosed {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ K, ∀ y : EuclideanSpace ℝ (Fin d), (∀ i, 0 ≤ y i ∧ y i ≤ x i) → y ∈ K

end GeomDRSub


