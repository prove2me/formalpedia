-- Prove2me | Definitions.Def_MCPoise_MGraph
-- name    : MCPoise_MGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:51.620522+00:00
-- url     : https://prove2.me/theorems/e3ff708a-5c35-4a91-8665-bd40ecb8bead
-- title:
--   Multigraphs, minimum cuts and S-path-packings
-- statement:
--   A **multigraph** is a list of edges, with position as identity, so parallel copies are distinct. The **degree** counts incidences, a loop twice. $\lambda(t, T)$ is the minimum number of edges with exactly one endpoint in $W$, over vertex sets $W$ containing $t$ and disjoint from $T$.
--
--   For $S \subseteq V$, an **$S$-path-packing** is a collection of edge-disjoint paths, each with two distinct endpoints in $S$.
--
--   **Formalization Note** Internal vertices of a packed path may lie in $S$, as the page does not exclude them.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 4, Theorem 2.8, p.17

import Mathlib

namespace MCPoise

/-- **A multigraph, by its list of edges.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.2.1, p.17: "Replace each edge e with Cx̂_{e,j} parallel copies."

**Formalization Note.** An edge is its position in the list, so parallel copies are distinct. Loops are allowed. -/
structure MGraph (V : Type*) where
  edges : List (Sym2 V)

variable {V : Type*} [DecidableEq V]

/-- The degree of `v`: the number of incidences, a loop counting twice. -/
def MGraph.deg (M : MGraph V) (v : V) : ℕ :=
  (M.edges.map fun e => if v ∈ e then (if e.IsDiag then 2 else 1) else 0).sum

/-- The number of edges with exactly one endpoint in `W`. -/
noncomputable def MGraph.cutSize (M : MGraph V) (W : Finset V) : ℕ :=
  open scoped Classical in (M.edges.filter fun e => ∃ a b, e = s(a, b) ∧ a ∈ W ∧ b ∉ W).length

/-- **`λ(t, T)`,** "the size of the min-cut separating t from S \ t" (Theorem 2.8, p.17).

**Formalization Note.** The infimum is over a set of natural numbers that contains `cutSize {t}` when `t ∉ T`, so the `ℕ`-valued
`sInf` is the true minimum in the only case used, `T = S \ {t}`. -/
noncomputable def MGraph.lam (M : MGraph V) (t : V) (T : Finset V) : ℕ :=
  sInf {m | ∃ W : Finset V, t ∈ W ∧ Disjoint W T ∧ m = M.cutSize W}

/-- A path of a multigraph: its vertices and the positions of its edges. -/
structure MPath (V : Type*) where
  vs : List V
  es : List ℕ

/-- `p` is a simple path of `M`: distinct vertices, joined by the listed edges in order. -/
def IsMPath (M : MGraph V) (p : MPath V) : Prop :=
  p.vs.Nodup ∧
    List.Forall₂ (fun e uv => M.edges[e]? = some s(uv.1, uv.2)) p.es (p.vs.zip p.vs.tail)

/-- **An `S`-path-packing.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 4, p.17: "For S ⊆ V, an S-path-packing is a collection of edge-disjoint paths, each with two distinct
endpoints in S."

**Formalization Note.** Internal vertices may lie in `S`, as the page does not exclude them. Edge-disjoint is disjointness of
edge positions, so two paths may use different parallel copies of one edge. -/
def IsSPacking (M : MGraph V) (S : Finset V) (Q : List (MPath V)) : Prop :=
  (∀ p ∈ Q, IsMPath M p ∧ ∃ a b, a ≠ b ∧ a ∈ S ∧ b ∈ S ∧
    p.vs.head? = some a ∧ p.vs.getLast? = some b) ∧
  Q.Pairwise fun p p' => ∀ e ∈ p.es, e ∉ p'.es

end MCPoise


