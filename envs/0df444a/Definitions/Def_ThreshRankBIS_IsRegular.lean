-- Prove2me | Definitions.Def_ThreshRankBIS_IsRegular
-- name    : ThreshRankBIS_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:55.805229+00:00
-- url     : https://prove2.me/theorems/1862bbcf-e5f7-4b3c-b66a-e2aac4302040
-- title:
--   $d$-regular bipartite graph $G=(X\cup Y,E)$: sides, regularity, $X$-part
-- statement:
--   Let $n\ge 0$. The bipartite graph $G=(X\cup Y,E)$ with $|X|=|Y|=n$ is given by its **biadjacency matrix** $E\in\{0,1\}^{n\times n}$: its vertex set is $V=X\sqcup Y$ with both sides numbered by $\{1,\dots,n\}$, $x\in X$ and $y\in Y$ are adjacent iff $E_{xy}=1$, and there are no edges inside $X$ or inside $Y$ (the platform's bipartite graph of a biadjacency matrix).
--
--   The graph is **$d$-regular** if every row and every column of $E$ has exactly $d$ ones, i.e. every vertex has exactly $d$ neighbours. The module also records the two sides $X$, $Y$ as vertex sets and the $X$-part $J\cap X$ of a vertex set $J$.
--
--   These are the standing objects of the whole paper: every result is about a simple $d$-regular bipartite graph with $|X|=|Y|=n$ and $d\ge 1$.
--
--   **Formalization Note** Every simple bipartite graph with sides of size $n$ is the graph of exactly one matrix $E$ once each side is numbered, so quantifying over $E$ is quantifying over the paper's graphs, with the bipartition given as part of the input.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3; §2.1, p.7

import Mathlib
import Definitions.Def_HiddenPartition_bip
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- The vertex set `V(G) = X ∪ Y` of a bipartite graph with `|X| = |Y| = n`: `Sum.inl x` is the
left vertex `x ∈ X` and `Sum.inr y` the right vertex `y ∈ Y`, both indexed by `Fin n`.

Source: C. A. Carlson, A. Kolla, *Efficient Algorithms for Approximately Counting Bipartite
Independent Sets in Low Threshold Rank Graphs*, STOC 2027 submission (manuscript sha256
9b315e04…), §1.1, p.3 and §2.1, p.7. -/
abbrev V (n : ℕ) : Type := Fin n ⊕ Fin n

/-- **`d`-regularity** of the bipartite graph `G = (X ∪ Y, E)` with biadjacency matrix `E` (§1.1,
p.3; §2.1, p.7): every left vertex has exactly `d` right neighbours and every right vertex has
exactly `d` left neighbours.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3 and §2.1,
p.7.

The graph itself is the platform's `HiddenPartition.bip E` (sides `X = inl`, `Y = inr`, `x ~ y` iff
`E x y`). The module also records the sides `X`, `Y` as vertex sets and the `X`-part `J ∩ X`.

**Formalization Note.** Every simple bipartite graph with sides `X`, `Y` of size `n` is
`HiddenPartition.bip E` for exactly one `E : Fin n → Fin n → Bool` (after numbering each side by
`Fin n`), so quantifying over `E` is quantifying over the paper's graphs, with the bipartition as
part of the data, as in the paper's `G = (X ∪ Y, E)`. -/
def IsRegular {n : ℕ} (E : Fin n → Fin n → Bool) (d : ℕ) : Prop :=
  (∀ x : Fin n, #(univ.filter (fun y => E x y = true)) = d) ∧
    (∀ y : Fin n, #(univ.filter (fun x => E x y = true)) = d)

/-- The left side `X ⊆ V(G)` as a set of vertices. -/
def Xs (n : ℕ) : Finset (V n) := univ.map Function.Embedding.inl

/-- The right side `Y ⊆ V(G)` as a set of vertices. -/
def Ys (n : ℕ) : Finset (V n) := univ.map Function.Embedding.inr

/-- The `X`-part `J ∩ X` of a vertex set `J`, as a subset of `Fin n`. -/
def leftPart {n : ℕ} (J : Finset (V n)) : Finset (Fin n) := univ.filter (fun x => Sum.inl x ∈ J)

end ThreshRankBIS


