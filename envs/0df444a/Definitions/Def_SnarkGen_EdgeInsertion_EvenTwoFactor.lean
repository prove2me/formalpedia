-- Prove2me | Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor
-- name    : SnarkGen_EdgeInsertion_EvenTwoFactor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:21.418645+00:00
-- url     : https://prove2.me/theorems/8135d9d3-6e79-4ecf-8edc-e583c788a9d6
-- title:
--   2-factor and even 2-factor (§2, p. 4; Lemma 3.1, p. 5)
-- statement:
--   Let $G = (V,E)$ be a finite simple graph.
--
--   1. A **2-factor** of $G$ is a spanning 2-regular subgraph $F$ of $G$: $F$ has every vertex of $G$ as a vertex, every edge of $F$ is an edge of $G$, and every vertex has degree exactly $2$ in $F$. Each connected component of a 2-factor is a cycle.
--   2. A 2-factor $F$ is **even** if all of its cycles have even length, i.e. every connected component of $F$ has an even number of vertices.
--
--   The **oddness** of a bridgeless cubic graph (p. 4) is the minimum number of odd components in a 2-factor; a cubic graph has oddness $0$ exactly when it has an even 2-factor. Even 2-factors are the bridge between 3-edge-colourings and the edge insertion operation in §3.1.
--
--   **Formalization Note** A 2-factor is a graph `F : SimpleGraph V` on the same vertex type as `G` (hence spanning) with `F ≤ G` and `F.IsRegularOfDegree 2` (degrees computed classically). The length of a cycle of `F` is the number of vertices of the corresponding connected component, counted with `Nat.card`. Oddness is not defined as a number: the mission only needs "oddness 0", which is the existence of an even 2-factor.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, §2 (2-factor, oddness) and p. 5, Lemma 3.1 (even 2-factor)

import Mathlib

namespace SnarkGen.EdgeInsertion

variable {V : Type*}

open Classical in
/-- A **2-factor** of `G` (arXiv:1206.6690v3, p. 4, §2) is a spanning 2-regular subgraph of `G`.
It is represented as a graph `F` on the same vertex type (hence spanning) with `F ≤ G` and every
vertex of degree exactly 2 in `F`. -/
def IsTwoFactor [Fintype V] (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ F.IsRegularOfDegree 2

/-- An **even 2-factor** (arXiv:1206.6690v3, p. 5, Lemma 3.1) is a 2-factor all of whose cycles
have even length. The cycles of a 2-factor `F` are its connected components, and the length of
such a cycle is its number of vertices. -/
def IsEvenTwoFactor [Fintype V] (G F : SimpleGraph V) : Prop :=
  IsTwoFactor G F ∧ ∀ c : F.ConnectedComponent, Even (Nat.card c.supp)

end SnarkGen.EdgeInsertion


