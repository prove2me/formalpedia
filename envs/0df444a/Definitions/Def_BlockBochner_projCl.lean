-- Prove2me | Definitions.Def_BlockBochner_projCl
-- name    : BlockBochner_projCl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:29.512742+00:00
-- url     : https://prove2.me/theorems/79b3a343-ad88-411a-8be5-1c7763d64871
-- title:
--   Orthogonal projection onto (the closure of) a subspace
-- statement:
--   For a subspace $K$ of a real Hilbert space $H$, $P_{\overline K}$ is the orthogonal projection onto the closure of $K$. For closed $K$ it is the orthogonal projection $P_K$ of Sec. 2.1. The paper's projections onto sums of subspaces, such as $\tilde Q_a$ onto $\sum_{i\in T_a}\tilde W_i$, are projections onto the closure of the sum.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.1, p.13; Sec. 3.2, p.21

import Mathlib

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Orthogonal projection onto (the closure of) a subspace.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.1, p.13: `P_U` is the
orthogonal projection onto a closed subspace `U`; Sec. 3.2, p.21: `Q̃_a`, `P̃` are "the orthogonal
projection onto `Σ_{i∈T_a} W̃_i`", resp. `Σ_{i∈T} W̃_i`.

**Formalization Note** The projection onto the topological closure of `K`; for a closed `K` it is
the orthogonal projection onto `K`. A sum of closed subspaces need not be closed, and the projection
"onto" it is the projection onto its closure. -/
noncomputable def projCl (K : Submodule ℝ H) : H →L[ℝ] H :=
  K.topologicalClosure.starProjection

end BlockBochner


