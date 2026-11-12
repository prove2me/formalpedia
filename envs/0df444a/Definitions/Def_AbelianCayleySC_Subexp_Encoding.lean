-- Prove2me | Definitions.Def_AbelianCayleySC_Subexp_Encoding
-- name    : AbelianCayleySC_Subexp_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:45.559229+00:00
-- url     : https://prove2.me/theorems/7748df30-0c09-437b-b2fa-6e7784c6770a
-- title:
--   Graph and vertex-set encodings for the machine, and undirected abelian Cayley graphs as input graphs
-- statement:
--   The algorithms of the paper receive a graph and return a set of vertices. A graph on the vertex set $\{0,\dots,n-1\}$ is written as the word of its $n^2$ adjacency bits $[i\sim j]$, row by row ($i$ outer, $j$ inner), diagonal included so that self-loops are visible; a set $Q$ of vertices is written as its $n$ indicator bits $[i\in Q]$. The alphabet is the four-symbol alphabet of the reused machine model, with the symbols $0$ and $1$ as bits.
--
--   A graph on $\{0,\dots,n-1\}$ is an **undirected abelian Cayley graph** if there are a finite abelian group $\Gamma$, a symmetric set $S=-S\subseteq\Gamma$ and a bijection $e:\{0,\dots,n-1\}\to\Gamma$ such that
--
--   $$i\sim j\iff e(j)-e(i)\in S .$$
--
--   Self-loops ($0\in S$) and disconnected graphs ($S$ not generating $\Gamma$) are allowed. Only the graph is input: the group, the labelling $e$ and $S$ are not.
--
--   This fixes the input and output format of Theorem 1.2 and Theorem 2.1 once, so that the machine cannot be handed extra information.
--
--   **Formalization Note** $\Gamma$ ranges over groups in Lean's `Type`; every finite abelian group is isomorphic to one there, so nothing is lost.
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), Theorem 1.2 p.2; Theorem 2.1 p.3; §2 p.3 ("we are only given the graph, not a description of the underlying group and a labeling of the vertices"); §3 p.7 (Cayley graphs)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace AbelianCayleySC.Subexp

open OnlineCRS.Combine (Sym)

/-!
# Inputs and outputs of the sparsest-cut algorithms; abelian Cayley graphs as input graphs

Jake Ruotolo, *Sparsest Cut on Abelian Cayley Graphs*, STOC 2027 submission #1724 (October 2026),
Theorem 1.2 p.2, Theorem 2.1 p.3, §2 p.3 ("we are only given the graph, not a description of the
underlying group and a labeling of the vertices").

A graph on `n` vertices is given to the machine as its `n × n` adjacency bits, and a set of
vertices is returned as its `n` indicator bits, over the alphabet `Sym = Fin 4` (symbols `0`,
`1` are the bits).
-/

/-- The input word of a graph on `Fin n`: the `n²` adjacency bits `[adj i j]`, row-major
(`i` outer, `j` inner), diagonal included so that self-loops are visible. -/
def encodeGraph {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj] : List Sym :=
  (List.finRange n).flatMap (fun i =>
    (List.finRange n).map (fun j => if adj i j then (1 : Sym) else 0))

/-- The output word of a set `Q ⊆ Fin n`: its `n` indicator bits `[i ∈ Q]`, in increasing `i`. -/
def encodeSet {n : ℕ} (Q : Finset (Fin n)) : List Sym :=
  (List.finRange n).map (fun i => if i ∈ Q then (1 : Sym) else 0)

/-- A graph on `Fin n` is an **undirected abelian Cayley graph** when, for some finite abelian group
`Γ`, symmetric `S ⊆ Γ` (`S = −S`) and bijection `e : Fin n ≃ Γ`, vertices `i, j` are adjacent iff
`e j − e i ∈ S`. Loops (`0 ∈ S`) and disconnected graphs (`S` not generating `Γ`) are allowed. -/
def IsAbelianCayley {n : ℕ} (adj : Fin n → Fin n → Prop) : Prop :=
  ∃ (Γ : Type) (_ : AddCommGroup Γ) (S : Finset Γ) (e : Fin n ≃ Γ),
    (∀ s ∈ S, -s ∈ S) ∧ ∀ i j : Fin n, adj i j ↔ e j - e i ∈ S

end AbelianCayleySC.Subexp


