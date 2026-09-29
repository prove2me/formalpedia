-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
-- name    : RobertsonSeymour1986_GM5_TreewidthLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:54:09.143686+00:00
-- url     : https://prove2.me/theorems/5294b37a-0ecf-4bdc-a9db-803bcc905ada
-- title:
--   Tree-width at most $w$
-- statement:
--   The **width** of a tree-decomposition $(T,(X_t))$ is $\max_{t\in V(T)}(|X_t|-1)$, and the **tree-width** of $G$ is the minimum $w\ge0$ such that $G$ has a tree-decomposition of width $\le w$.
--
--   This file defines "$G$ has tree-width at most $w$": there is a tree-decomposition of $G$ in which every bag has at most $w+1$ vertices.
--
--   Every graph with $n$ vertices has tree-width at most $n-1$ (a single bag); forests are the graphs of tree-width at most $1$.
--
--   **Formalization Note** Because the tree-width is a minimum over $w\ge 0$, "tree-width $\le w$" is equivalent to the existence of a decomposition of width $\le w$. The predicate is stated that way, and no infimum is taken.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 93 (PDF p. 2), definition of width and tree-width; DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

namespace RobertsonSeymour1986.GM5

/-- `TreewidthLE G w`: the graph `G` has tree-width at most `w`, i.e. `G` has a tree-decomposition
of width `≤ w`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, p. 93 (PDF p. 2), unnumbered: "The *width* of the tree-decomposition is
max(|X_t| − 1 : t ∈ V(T)); and the *tree-width* of G is the minimum w ≥ 0 such that G has a
tree-decomposition of width ≤ w."

**Formalization Note** Width `≤ w` is `|X_t| ≤ w + 1` for every node `t`. Since the tree-width is
the least `w ≥ 0` admitting such a decomposition, "tree-width at most `w`" is exactly the existence
of a decomposition of width `≤ w`; no `sInf` is taken. The tree lives on a finite type `T : Type`. -/
def TreewidthLE {V : Type} [DecidableEq V] (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T) (X : T → Finset V),
    IsTreeDecomposition G t X ∧ ∀ s : T, (X s).card ≤ w + 1

end RobertsonSeymour1986.GM5


