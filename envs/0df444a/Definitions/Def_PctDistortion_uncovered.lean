-- Prove2me | Definitions.Def_PctDistortion_uncovered
-- name    : PctDistortion_uncovered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:14.7672+00:00
-- url     : https://prove2.me/theorems/ca90acf2-af0c-4d0e-a3d5-0bbe4b42c9c5
-- title:
--   Covering and the uncovered set of a digraph
-- statement:
--   In a simple digraph $G=(V,E)$, node $i$ **covers** node $j$ if $N^-(i)\subsetneq N^-(j)$. The **uncovered set** $U(G)$ is the set of nodes covered by no other node.
--
--   In the tournament of an election this is the social-choice uncovered set: $i$ covers $j$ when every candidate defeating $i$ also defeats $j$. ABC-maximal lotteries are supported on $U(G)$.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 2, p.9

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- Node `i` **covers** node `j` in the digraph `G`: `N⁻(i) ⊊ N⁻(j)`, the in-neighbourhood of
`i` is a strict subset of that of `j`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 2, p.9: "Given a simple digraph G = (V, E), we say that node i covers node j if
N−(i) ⊊ N−(j)." -/
def covers {W : Type} (G : Digraph W) (i j : W) : Prop :=
  {k | G.Adj k i} ⊂ {k | G.Adj k j}

/-- The **uncovered set** `U(G)`: the nodes covered by no node of `G`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 2, p.9: "The uncovered set of a simple digraph G, denoted by U(G), is the set of
nodes not covered by any other node."

**Formalization Note.** No node covers itself (strict inclusion), so "no other node" and "no
node" agree. -/
def uncovered {W : Type} (G : Digraph W) : Set W :=
  {j | ∀ i, ¬ covers G i j}

end PctDistortion


