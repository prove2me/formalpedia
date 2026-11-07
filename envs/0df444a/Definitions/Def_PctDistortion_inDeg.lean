-- Prove2me | Definitions.Def_PctDistortion_inDeg
-- name    : PctDistortion_inDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:57.773626+00:00
-- url     : https://prove2.me/theorems/b3c5415f-7524-4afe-9be8-6c6506d5db9d
-- title:
--   In-degree, normalized minimum in-degree, simple and oriented digraphs
-- statement:
--   For a digraph $G=(V,E)$ on a finite node set, $N^-(i)=\{j\in V:(j,i)\in E\}$ is the in-neighbourhood of $i$ and $\deg^-(i)=|N^-(i)|$ its **in-degree**. The **minimum in-degree** is $\delta^-(G)=\min_{j\in V}\deg^-(j)$, and its normalized form is $\delta^-(G)/|V|$; for a class $\mathcal H$ of digraphs, (1) sets $\delta^-(\mathcal H)=\sup_{G\in\mathcal H}\delta^-(G)/|V|$.
--
--   A digraph is **simple** if it has no self-loops (a relation has no parallel arcs), and **oriented** if it has neither self-loops nor 2-cycles: for each pair $i,j$ at most one of $(i,j)$, $(j,i)$ is an arc.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9, eq. (1)

import Mathlib

set_option autoImplicit false

namespace PctDistortion

open Classical in
/-- The **in-degree** `deg⁻(w) = |N⁻(w)|` of node `w` in a digraph on a finite node type, where
`N⁻(w) = {u | (u, w) ∈ E}` is the in-neighbourhood of `w`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "We write N−(i) = {j ∈ V | (j, i) ∈ E} for the in-neighborhood of node i. The
in-degree of node j is then simply the size of the in-neighborhood, deg−(j) = |N−(j)|." -/
noncomputable def inDeg {W : Type} [Fintype W] (G : Digraph W) (w : W) : ℕ :=
  (Finset.univ.filter (fun u => G.Adj u w)).card

/-- The **normalized minimum in-degree** `δ⁻(G)/|V|` of a digraph on a finite node type, where
`δ⁻(G) = min_j deg⁻(j)`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "we write δ−(G) = minj∈V deg−(j) for the minimum in-degree"; the class quantity
(1) is the supremum of `δ⁻(G)/|V|` over the class. -/
noncomputable def normMinInDeg {W : Type} [Fintype W] (G : Digraph W) : ℝ :=
  (⨅ w, (inDeg G w : ℝ)) / (Fintype.card W : ℝ)

/-- A digraph is **simple**: it has no self-loops (a relation has no parallel arcs).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "All our digraphs will be simple, i.e., contain no self-loops or parallel arcs." -/
def IsSimple {W : Type} (G : Digraph W) : Prop :=
  ∀ w, ¬ G.Adj w w

/-- A digraph is **oriented**: it contains neither self-loops nor 2-cycles, i.e. for every pair of
nodes `i, j` at most one of `(i, j)`, `(j, i)` is an arc (taking `i = j` excludes loops).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "A digraph is called oriented if it contains neither self-loops nor 2-cycles,
i.e., for each pair of nodes i, j ∈ V, it contains at most one of the arcs (i, j) and (j, i)." -/
def IsOriented {W : Type} (G : Digraph W) : Prop :=
  ∀ i j, G.Adj i j → ¬ G.Adj j i

end PctDistortion


