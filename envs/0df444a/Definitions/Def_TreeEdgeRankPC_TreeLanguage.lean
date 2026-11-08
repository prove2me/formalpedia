-- Prove2me | Definitions.Def_TreeEdgeRankPC_TreeLanguage
-- name    : TreeEdgeRankPC_TreeLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:09.135753+00:00
-- url     : https://prove2.me/theorems/4982c078-db43-4ada-b0ed-88331e18761a
-- title:
--   The languages Tree-Edge-Ranking and Tree-Edge-Ranking for diameter at most six
-- statement:
--   **Tree-Edge-Ranking** is the decision problem: given a tree $T$ and an integer $K\ge 0$, is $\mathrm{er}(T)\le K$? **Its diameter-six restriction** asks the same for trees of diameter at most six, where a tree has diameter $D$ when its longest simple path has $D$ edges.
--
--   These are the two languages of the goal theorem. A string that encodes no instance is not in them, and neither is a tree of larger diameter in the restricted language.
--
--   **Formalization Note** `encTree T K` is $n$ in unary, a separator, the $n^2$ adjacency bits in row-major order, then $K$ in binary (least significant bit first, no trailing zero). It is injective, and $K$ may be far larger than $n$. Diameter at most six is `∀ u v, T.dist u v ≤ 6`, which in a tree is the longest simple path.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Theorem 1.1, p.2; §3.1, p.10 (diameter)

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking

open Classical

namespace TreeEdgeRankPC

/-- The binary code of an instance `(T, K)` of the decision problem of Theorem 1.1, p.2
(arXiv:2610.12438, held version of 2026-11-02, sha256 9e04ca7b…): `n` in unary, a separator, the `n²`
adjacency bits in row-major order, then `K` in binary (`Nat.bits`, least significant bit first, no
trailing zero).

**Formalization Note.** The code is injective in `(n, T, K)`. A tree on `n` vertices has adjacency
matrix of size polynomial in `n`, and edge lists convert to and from it in NC¹. `K` is written in binary
as an integer `K ≥ 0`, so `K` may be far larger than `n`. -/
noncomputable def encTree {n : ℕ} (T : SimpleGraph (Fin n)) (K : ℕ) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u => (List.finRange n).map fun v => decide (T.Adj u v)) ++
    Nat.bits K

/-- **Tree-Edge-Ranking**, Theorem 1.1, p.2: "Given a tree T and an integer K ≥ 0, deciding whether T has
edge ranking at most K". A string that encodes no instance is not in the language. -/
def TER : Set (List Bool) :=
  {s | ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ), T.IsTree ∧ s = encTree T K ∧ er T ≤ K}

/-- **Tree-Edge-Ranking for trees of diameter at most six**, Theorem 1.1, p.2.

**Formalization Note.** §3.1, p.10: a tree "has diameter D when its longest simple path has D edges". In
a tree this is the maximum of `T.dist`, so the condition is `∀ u v, T.dist u v ≤ 6`. A string that
encodes no instance, or a tree of larger diameter, is not in the language. -/
def TER6 : Set (List Bool) :=
  {s | ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ),
    T.IsTree ∧ (∀ u v, T.dist u v ≤ 6) ∧ s = encTree T K ∧ er T ≤ K}

end TreeEdgeRankPC


