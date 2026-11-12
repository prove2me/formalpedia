-- Prove2me | Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
-- name    : CayleyErdosGyarfas_HasSymmetricFigureEight
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T02:09:57.152315+00:00
-- url     : https://prove2.me/theorems/ecb36ff5-c969-4e7d-aa09-0583a98390c0
-- title:
--   Symmetric figure-eight in a Cayley graph
-- statement:
--   Let $G$ be a group and $S \subseteq G$. The Cayley graph $\operatorname{Cay}(G,S)$ has vertex set $G$, and distinct $g, h \in G$ are adjacent when $h = gs$ or $g = hs$ for some $s \in S$. A cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   $\operatorname{Cay}(G,S)$ **contains a symmetric figure-eight** if there are $n \ge 2$, a vertex $v \in G$, an element $g \in G$ and two cycles of length $2^n$ based at $v$,
--
--   $$\alpha = (v, a_1, \dots, a_{2^n} = v), \qquad \beta = (v, b_1, \dots, b_{2^n} = v),$$
--
--   such that
--
--   1. the sequence $(b_1, \dots, b_{2^n})$ is a cyclic rotation of $(g a_1, \dots, g a_{2^n})$, so that $\beta$ is the left translate $g\alpha$ up to the choice of starting vertex; and
--   2. $v$ is the only vertex lying on both $\alpha$ and $\beta$.
--
--   This is the paper's symmetric figure-eight: a pair of power-of-two-length simple cycles that meet in exactly one vertex, one a $G$-translate of the other up to change of basepoint. It is the configuration that Lemma 1.2 lifts through quotients by abelian normal subgroups, and either of its cycles is a cycle of power-of-two length.
--
--   **Formalization Note** The graph is Mathlib's `SimpleGraph.mulCayley S` and the cycles are walks satisfying `SimpleGraph.Walk.IsCycle`. Basing both cycles at their common vertex loses no generality. For a cycle, `support.tail` lists each vertex once in traversal order, and the translate condition is `List.IsRotated (α.support.tail.map (g * ·)) β.support.tail`. Only rotations are allowed, not reversals; the reverse of a cycle is a cycle on the same vertices, so this does not change which graphs contain a figure-eight. The bound $n \ge 2$ is redundant, since cycles have length at least $3$, and is kept to match the paper. The declaration is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.HasSymmetricFigureEight` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015. The paper uses this notion only for finite $G$ and inverse-closed generating sets $S \subseteq G \setminus \{1\}$ (§1.1); the predicate is stated for an arbitrary group and subset, agrees with the paper's notion in that setting, and the theorems that use it carry those conventions as hypotheses.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 1: definition of a symmetric figure-eight (paragraph following Theorem 1.1); conventions of §1.1 Preliminaries, p. 2. Lean declaration as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Symmetric figure-eights in Cayley graphs

Michael C. Burkhart, *Odd-ordered Cayley graphs satisfy Erdős–Gyárfás*,
arXiv:2611.05060v1, §1, p. 1 (the paragraph after Theorem 1.1).

`SimpleGraph.mulCayley S` is Mathlib's Cayley graph on the group `G`: distinct
vertices `g` and `h` are adjacent exactly when `h = g * s` or `g = h * s` for some
`s ∈ S`. A closed walk `c` with `c.IsCycle` is a simple cycle, `c.length` counts its
edges, and `c.support` lists its vertices in traversal order, the base vertex
appearing at both ends.
-/

namespace CayleyErdosGyarfas

/-- Two simple cycles of length `2 ^ n`, based at their unique common vertex `v`.
Left multiplication by `g` carries the first to the second up to a cyclic change of
basepoint: for a simple cycle, `support.tail` lists its vertices in traversal order
with one occurrence of each vertex, and `List.IsRotated` allows the traversal of the
translate to start at a different vertex. -/
def HasSymmetricFigureEight {G : Type*} [Group G] (S : Set G) : Prop :=
  ∃ (n : ℕ) (v : G) (α β : (SimpleGraph.mulCayley S).Walk v v),
    2 ≤ n ∧ α.IsCycle ∧ β.IsCycle ∧
    α.length = 2 ^ n ∧ β.length = 2 ^ n ∧
    (∃ g : G, List.IsRotated (α.support.tail.map (g * ·)) β.support.tail) ∧
    ∀ w : G, (w ∈ α.support ∧ w ∈ β.support) ↔ w = v

end CayleyErdosGyarfas


