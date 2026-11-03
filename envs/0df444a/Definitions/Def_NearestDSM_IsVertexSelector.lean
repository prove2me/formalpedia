-- Prove2me | Definitions.Def_NearestDSM_IsVertexSelector
-- name    : NearestDSM_IsVertexSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:18.129215+00:00
-- url     : https://prove2.me/theorems/d504b671-7545-4774-b1ba-630a8589afa7
-- title:
--   Vertex selectors (step 3 of Algorithm 3.1)
-- statement:
--   A **vertex selector** is a map $\sigma:\mathbb R^{2n-1}\to\mathbb R^{2n-1}$ such that, for every $y$,
--   $$
--   \sigma(y)\in\operatorname{ext}[y],
--   $$
--   the set of vertices (extreme points) of the polyhedron $[y]$. Step 3 of Algorithm 3.1 finds a vertex $\tilde y^k$ of $[y^k]$ by the procedure of Theorem 3.15; the convergence proof only uses that $\tilde y^k$ is a vertex.
--
--   Lemma 3.12 (every class has a vertex) guarantees that vertex selectors exist.
--
--   **Formalization Note** A vertex is an extreme point in Mathlib's sense.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Algorithm 3.1 step 3, p.20; proof of Theorem 3.17, p.24

import Mathlib
import Definitions.Def_NearestDSM_equivClass

namespace NearestDSM

/-- A **vertex selector**: a map `σ` sending every `y` to a vertex (extreme point) of its
equivalence class `[y]`. Step 3 of Algorithm 3.1, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, p.20, is "Find a vertex `ỹ^k`
of `[y^k]` using Theorem 3.15"; the proof of Theorem 3.17, p.24, lets `ỹ^k` be "any vertex of
`[y^k]`".

**Formalization Note.** A vertex of a polyhedron is an extreme point (`Set.extremePoints ℝ`).
Lemma 3.12 (every class has a vertex) makes such maps exist. -/
def IsVertexSelector {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Dual n → Dual n) : Prop :=
  ∀ y, σ y ∈ Set.extremePoints ℝ (equivClass Xh y)

end NearestDSM


