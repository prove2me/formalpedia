-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_SubtreeMarginal
-- name    : IsingLTL_FreeEntropy_SubtreeMarginal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:09.503104+00:00
-- url     : https://prove2.me/theorems/55059e3b-e02d-445a-9b9f-6b3da011496b
-- title:
--   Boundary $\partial_*U$ of a subtree, hanging subtrees $T_u$ and the effective field $\mathrm{atanh}\langle x_u\rangle_W$ (Lemma 4.1)
-- statement:
--   Let $T$ be a finite tree on the vertex set $V$ and $U$ a subtree, $W=V\setminus U$. Then $\partial_*U$ is the set of vertices of $U$ joined by an edge to $W$. For $u\in\partial_*U$, $T_u$ is the maximal subtree of $W\cup\{u\}$ containing $u$ (the vertices reachable from $u$ by a path whose vertices after $u$ lie in $W$), rooted at $u$. Given $\beta$, fields $\underline B$ and a set of pinned vertices, $\langle x_u\rangle_W$ is the root magnetization of the Ising model on $T_u$, and the **effective field** at $u$ is
--   $$B'_u=\operatorname{atanh}\big(\langle x_u\rangle_W\big).$$
--   Lemma 4.1 states that the marginal on $U$ of the Ising measure on $T$ is the Ising measure on $U$ with the fields $B'_u$ at $u\in\partial_*U$.
--
--   **Formalization Note** $\operatorname{atanh}$ is Mathlib's `Real.artanh`, the true inverse hyperbolic tangent on $(-1,1)$; $|\langle x_u\rangle_W|<1$ whenever $u$ is not pinned.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.FreeEntropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a vertex set `U` of a finite graph `G`, `∂_*U`: the vertices of `U` joined by an edge to
`W = V \ U` (Dembo–Montanari, arXiv:0804.4726v3, Lemma 4.1, p. 10). -/
noncomputable def outerBoundary (G : SimpleGraph V) (U : Finset V) : Finset V := by
  classical
  exact U.filter (fun u => ∃ w, w ∉ U ∧ G.Adj u w)

/-- For `u ∈ ∂_*U`, the vertex set of `T_u`, the maximal subtree of `W ∪ {u}` containing `u`
(`W = V \ U`): the vertices `v` joined to `u` by a walk whose vertices after `u` all lie in `W`
(arXiv:0804.4726v3, Lemma 4.1, p. 10). -/
noncomputable def hangingSubtree (G : SimpleGraph V) (U : Finset V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk u v, ∀ w ∈ p.support.tail, w ∉ U)

/-- The effective field `B′_u = atanh(⟨x_u⟩_W)` of Lemma 4.1 (arXiv:0804.4726v3, p. 10), where
`⟨x_u⟩_W` is the root magnetization of the Ising model (inverse temperature `β`, fields `B`,
pins `S`) on the subtree `T_u`.

Formalization Note: `atanh` is Mathlib's `Real.artanh`, `artanh x = log √((1 + x)/(1 − x))`; it is
the true inverse hyperbolic tangent on `(−1, 1)`, and `|⟨x_u⟩_W| < 1` whenever `u` is not pinned. -/
noncomputable def cavityField (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (B : V → ℝ)
    (S U : Finset V) (u : V) : ℝ :=
  Real.artanh (magOn (hangingSubtree G U u) (isingOn G β B S (hangingSubtree G U u)) u)

end IsingLTL.FreeEntropy


