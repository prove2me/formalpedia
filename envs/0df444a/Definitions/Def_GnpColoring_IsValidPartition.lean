-- Prove2me | Definitions.Def_GnpColoring_IsValidPartition
-- name    : GnpColoring_IsValidPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:55.738211+00:00
-- url     : https://prove2.me/theorems/736765d2-05ac-4d16-8c86-c0e1ba149419
-- title:
--   Valid block partition (Definition 3.2)
-- statement:
--   Fix a graph $G$ on $n$ vertices, parameters $d,\eta,A,C$ and a diameter constant $D>0$. A set $S$ of vertices gives a **valid block partition** if $S\subseteq\hat S$ (every singleton is a global breakpoint) and, with $\mathcal B$ the blocks of $S$:
--
--   1. every block $B\in\mathcal B$ induces a tree or a unicyclic graph;
--   2. every $v\in S$ has at most one neighbour in each block;
--   3. every block has diameter at most $D\log n/d^{2\eta}$.
--
--   This is the structure the block dynamics of Section 3 is defined on; Theorem 4.1 shows $G(n,d/n)$ admits one with high probability.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2, p.15

import Mathlib
import Definitions.Def_GnpColoring_globalBreakpoints
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_IsTreeOrUnicyclic
import Definitions.Def_GnpColoring_blockDiam

open scoped Classical
open Finset

namespace GnpColoring

/-- **Valid block partition** (Definition 3.2) with diameter constant `D > 0`: `S ⊆ Ŝ`, and
1. every block `B ∈ 𝓑` induces a tree or a unicyclic graph;
2. every `v ∈ S` has at most one neighbour in each block;
3. every block has diameter (inside it) at most `D log(n)/d^(2η)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2, p.15: "Given a graph G and parameters d, η, A, C, fix also a diameter
constant D = D(η, A, C) > 0, independent of d and n. Let Ŝ be the set of global breakpoints in G.
Choose a subset S ⊆ Ŝ … This block partition resulting from S is called valid if the following
conditions are met."

**Formalization Note** "at most one edge between v and B" is `|N(v) ∩ B| ≤ 1`; `log` is
natural; `d^(2η)` is `Real.rpow`. -/
def IsValidPartition {n : ℕ} (G : SimpleGraph (Fin n)) (d η A C D : ℝ) (S : Finset (Fin n)) :
    Prop :=
  0 < D ∧ S ⊆ globalBreakpoints G d η A C ∧
    (∀ B ∈ blocks G S, IsTreeOrUnicyclic G B) ∧
    (∀ v ∈ S, ∀ B ∈ blocks G S, (B.filter fun u => G.Adj v u).card ≤ 1) ∧
    (∀ B ∈ blocks G S, (blockDiam G B : ℝ) ≤ D * Real.log n / d ^ (2 * η))

end GnpColoring


