-- Prove2me | Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
-- name    : Kakutani1941_FixedPoint_UpperSemicontinuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:49.609067+00:00
-- url     : https://prove2.me/theorems/da12374f-1284-4f27-b405-ab3268cd2ad0
-- title:
--   Section 1 — sequential upper semi-continuity of a point-to-set mapping
-- statement:
--   Let $S$ be a subset of a real normed vector space and let $\Phi$ assign a set of points to each point. The mapping is **upper semi-continuous on $S$** in Kakutani's sequential sense if, for sequences $x_n\in S$ and $y_n\in\Phi(x_n)$,
--
--   $$x_n\to x_0\in S,\qquad y_n\to y_0\quad\Longrightarrow\quad y_0\in\Phi(x_0).$$
--
--   This condition is the continuity assumption shared by Theorem 1 and the Corollary. It also makes the graph closed when the underlying domain is closed.
--
--   **Formalization Note** The map is represented by a total function on the ambient space; its values outside $S$ are irrelevant. Sequences and their limits are explicitly restricted to $S$ as on the page.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 457, Section 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- The sequential upper semicontinuity condition stated on p. 457. -/
def IsUpperSemicontinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (Φ : E → Set E) : Prop :=
  ∀ (x y : ℕ → E) (x₀ y₀ : E), (∀ n, x n ∈ S) → x₀ ∈ S →
    Filter.Tendsto x Filter.atTop (nhds x₀) → (∀ n, y n ∈ Φ (x n)) →
    Filter.Tendsto y Filter.atTop (nhds y₀) → y₀ ∈ Φ x₀

end Kakutani1941.FixedPoint


