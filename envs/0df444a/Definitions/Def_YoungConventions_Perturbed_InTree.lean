-- Prove2me | Definitions.Def_YoungConventions_Perturbed_InTree
-- name    : YoungConventions_Perturbed_InTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:34.364221+00:00
-- url     : https://prove2.me/theorems/77ad7999-cdb0-4284-b1cb-9ccb1817c02b
-- title:
--   In-trees by parent maps and the Markov chain tree weight $p'_z$
-- statement:
--   Let $V$ be a set and $j \in V$. A **$j$-tree** on $V$ is a spanning tree of directed edges such that from every vertex $i \ne j$ there is exactly one directed path to $j$ (an in-tree, or arborescence converging on the root $j$). Equivalently, every vertex $i \ne j$ has exactly one outgoing edge $(i, \tau(i))$, and following these edges from any vertex eventually reaches $j$.
--
--   For a Markov chain $P'$ on a finite set $X$ and a state $z \in X$, the **tree weight** of $z$ is
--   $$p'_z = \sum_{T \in \mathcal T_z} \prod_{(x,y) \in T} P'_{xy},$$
--   where $\mathcal T_z$ is the set of $z$-trees on the complete directed graph with vertex set $X$.
--
--   The $z$-trees are the combinatorial objects of the Markov chain tree formula of Freidlin and Wentzell, which expresses the stationary distribution of an irreducible chain as $\mu'_z = p'_z / \sum_x p'_x$; Young (1993) uses them for both the state graph $G$ and the graph $\mathcal G$ of recurrent classes.
--
--   **Formalization Note** A $j$-tree is encoded by its parent map $\tau : V \to V$ with $\tau(j) = j$ and, for every $v$, some iterate $\tau^{n}(v) = j$; its edges are $(v, \tau(v))$ for $v \ne j$, pointing toward the root. Trees through a zero entry of $P'$ are included in the sum and contribute $0$. For two states this gives $p'_1 = P'_{21}$ and $p'_2 = P'_{12}$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 78 (j-trees, z-trees) and proof of Lemma 1, p. 79 (p′_z) (PDF pp. 23–24)

import Mathlib

open Finset

namespace YoungConventions.Perturbed

/-!
In-trees (arborescences converging on a root), encoded by parent maps, and the Markov chain tree
weight `p′_z` of Freidlin and Wentzell.
Young (1993), *The Evolution of Conventions*, Econometrica 61:57–84, Appendix, p. 78 (definitions
of j-trees and z-trees) and p. 79 (the weights `p′_z`), PDF pp. 23–24.
-/

/-- `τ` is an in-tree on the vertex set `V` rooted at `root` (a "`root`-tree", Young 1993,
Appendix, p. 78, PDF p. 23): a spanning tree such that from every vertex `v ≠ root` there is
exactly one directed path to `root`.

**Formalization Note.** The tree is given by its parent map: `τ v` is the head of the unique
edge leaving `v ≠ root`, so the edge set is `{(v, τ v) | v ≠ root}`. The conditions `τ root = root`
and "every vertex reaches `root` by iterating `τ`" say the parent pointers have no cycle, so
every vertex `v ≠ root` has exactly one outgoing edge and its unique directed path to the root
follows the parent pointers. Edges point **toward** the root (in-tree / arborescence converging
on the root), as in the paper. Fixing `τ root = root` makes the parent maps correspond one to one
with the trees. -/
def IsInTree {V : Type*} (root : V) (τ : V → V) : Prop :=
  τ root = root ∧ ∀ v : V, ∃ n : ℕ, τ^[n] v = root

variable {X : Type*} [Fintype X] [DecidableEq X]

open Classical in
/-- The Markov chain tree weight of `z` (Young 1993, proof of Lemma 1, p. 79, PDF p. 24):
$$p'_z = \sum_{T \in \mathcal T_z} \prod_{(x,y) \in T} P'_{xy},$$
the sum over all `z`-trees `T` on the complete directed graph with vertex set `X` of the product
of the transition probabilities along the edges of `T`.

**Formalization Note.** Trees are parent maps `T : X → X` with `IsInTree z T`; the edges of
`T` are `(x, T x)` for `x ≠ z`. Trees through a zero entry of `A` are included and contribute
`0`, so this equals the paper's sum over trees in the graph of positive entries. -/
noncomputable def treeWeight (A : Matrix X X ℝ) (z : X) : ℝ :=
  ∑ T ∈ (univ : Finset (X → X)).filter (fun T => IsInTree z T),
    ∏ x ∈ univ.erase z, A x (T x)

end YoungConventions.Perturbed


