-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_SubtreeMarginal
-- name    : IsingLTL_BeliefProp_SubtreeMarginal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:15.25711+00:00
-- url     : https://prove2.me/theorems/eed809f4-f3bc-41b0-a9d1-0337a9102289
-- title:
--   The outer boundary $\partial_*U$, the hanging subtrees $\mathsf T_u$ and the effective fields $\operatorname{atanh}\langle x_u\rangle_W$ of Lemma 4.1
-- statement:
--   Let $T$ be a finite graph (in Lemma 4.1, a tree) and $U$ a set of its vertices, $W=T\setminus U$.
--
--   1. $\partial_*U$ is the set of vertices of $U$ joined by an edge to $W$.
--   2. For $u\in\partial_*U$, $\mathsf T_u$ is the maximal subtree of $W\cup\{u\}$ containing $u$: the vertices that can be reached from $u$ by a path whose vertices after $u$ all lie in $W$.
--   3. $\langle x_u\rangle_W$ is the root magnetization of the Ising model on $\mathsf T_u$ (inverse temperature $\beta$, fields $B$, pinned vertices $S$), and the **effective field** at $u$ is
--   $$B'_u=\operatorname{atanh}\big(\langle x_u\rangle_W\big).$$
--
--   These objects state Lemma 4.1: the marginal on a subtree of an Ising measure on a tree is an Ising measure with the fields at $\partial_*U$ replaced by $B'_u$.
--
--   **Formalization Note** $\operatorname{atanh}$ is Mathlib's `Real.artanh`, $\operatorname{artanh}x=\log\sqrt{(1+x)/(1-x)}$, the inverse hyperbolic tangent on $(-1,1)$. When $u$ is not pinned, $|\langle x_u\rangle_W|<1$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 10, Lemma 4.1 (and p. 11, its proof)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

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

end IsingLTL.BeliefProp


