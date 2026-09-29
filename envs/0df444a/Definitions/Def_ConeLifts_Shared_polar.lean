-- Prove2me | Definitions.Def_ConeLifts_Shared_polar
-- name    : ConeLifts_Shared_polar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:48.457739+00:00
-- url     : https://prove2.me/theorems/38bdb63f-03a9-403a-bd81-9cbd6cb8e817
-- title:
--   Polar of a set: $C^\circ = \{y : \langle x, y\rangle \le 1 \ \forall x \in C\}$
-- statement:
--   For a set $C \subseteq \mathbb R^n$, its **polar** is
--
--   $$
--   C^\circ = \{\, y \in \mathbb R^n : \langle x, y\rangle \le 1 \ \text{ for all } x \in C \,\},
--   $$
--
--   where $\langle\cdot,\cdot\rangle$ is the Euclidean inner product. The slack operator of a convex body $C$ pairs the extreme points of $C$ with those of $C^\circ$; for a polytope with the origin in its interior, the extreme points of $C^\circ$ are in bijection with the facets of $C$, which is how slack matrices are indexed.
--
--   This definition is shared by three missions of this series: I (the factorization theorem: slack operator and Definition 2.2, pp. 3–4, and the proof of Theorem 2.4, pp. 4–5), II (nonnegative-rank bounds: slack operator, p. 3; Definition 4.3, p. 13; Definition 4.10 and Theorem 4.11, p. 15) and III (stable set polytopes without psd lifts: Definition 3.1 and Theorem 3.3, p. 9).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. This is the one-sided polar. Mathlib's `LinearMap.polar` and `StrongDual.polar` are the absolute polar $\{y : |\langle x,y\rangle| \le 1\ \forall x\in C\}$, which differs for non-symmetric $C$ and is not used.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 (polar of a convex set)

import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.Shared

/-- The **polar** of a set `C ⊆ ℝⁿ` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §2, p. 3):
`C° = {y ∈ ℝⁿ : ⟨x, y⟩ ≤ 1 for all x ∈ C}`, with `⟨·,·⟩` the Euclidean inner product of
`EuclideanSpace ℝ (Fin n)`.

This is the one-sided polar; it is not Mathlib's `LinearMap.polar` / `StrongDual.polar`, which
use the absolute value `‖⟨x, y⟩‖ ≤ 1`. -/
def polar {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ C, ⟪x, y⟫_ℝ ≤ 1}

end ConeLifts.Shared


