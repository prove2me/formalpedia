-- Prove2me | Definitions.Def_ChvatalPolytopes_Separation_IsFacet
-- name    : ChvatalPolytopes_Separation_IsFacet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:16:40.294156+00:00
-- url     : https://prove2.me/theorems/e336a0df-2be0-45a1-9c78-954eda994995
-- title:
--   Facet of a polytope, via defining linear systems (§1)
-- statement:
--   Let $V$ be a finite set and $P\subseteq\mathbb R^V$. A finite system of linear inequalities
--   $$\sum_{u\in V}A_{ju}x_u\le B_j\qquad(j\in J)$$
--   is a **defining linear system** of $P$ if a vector $x\in\mathbb R^V$ satisfies all of its inequalities exactly when $x\in P$.
--
--   An inequality $\sum_{u\in V}a_ux_u\le b$ is a **facet** of $P$ if and only if every defining linear system of $P$ includes, for some positive $t$, the inequality
--   $$\sum_{u\in V}t\,a_ux_u\le t\,b.$$
--
--   Thus a facet is an inequality that no linear description of $P$ can avoid, up to a positive scaling. This is the notion in which Theorem 4.2 is stated.
--
--   **Formalization Note** Defining systems are indexed by an arbitrary finite type $J$ (in `Type`), with real coefficients; nonnegativity inequalities, if present, are ordinary rows. The definition is the paper's, not the characterization by $|V|$ affinely independent tight points (which agrees with it only for full-dimensional $P$).
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 138, §1 (definitions of defining linear system and facet)

import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Facet** (Chvátal 1975, p. 138). A finite linear system
`Σ (A_{ju} x_u : u ∈ V) ≤ B_j (j ∈ J)` is a *defining linear system* of `P ⊆ ℝ^V` when its set
of solutions is exactly `P`. The inequality `Σ (a_u x_u : u ∈ V) ≤ b` is a *facet* of `P` if and
only if every defining linear system of `P` includes, for some positive `t`, the inequality
`Σ (t a_u x_u : u ∈ V) ≤ t b`.

Defining systems are indexed by an arbitrary finite index type `J`, with real coefficients and
no separate nonnegativity rows (a nonnegativity inequality, if present, is one of the rows). -/
def IsFacet {V : Type*} [Fintype V] (P : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ (J : Type) [Fintype J] (A : J → V → ℝ) (B : J → ℝ),
    {x : V → ℝ | ∀ j, ∑ u, A j u * x u ≤ B j} = P →
      ∃ j : J, ∃ t : ℝ, 0 < t ∧ (∀ u, A j u = t * a u) ∧ B j = t * b

end ChvatalPolytopes.Separation


