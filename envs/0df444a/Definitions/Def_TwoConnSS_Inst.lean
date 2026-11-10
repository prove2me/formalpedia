-- Prove2me | Definitions.Def_TwoConnSS_Inst
-- name    : TwoConnSS_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:02.299512+00:00
-- url     : https://prove2.me/theorems/50955cf1-6fef-491d-b601-0294bb04f934
-- title:
--   An instance of 2ECSS: a simple graph on $\{0,\dots,n-1\}$ given by an adjacency matrix
-- statement:
--   An **instance** of the minimum 2-edge-connected spanning subgraph problem (2ECSS) is a finite simple undirected graph $G$ on the vertex set $V = \{0, \dots, n-1\}$, given by an $n \times n$ Boolean matrix. The graph has an edge $\{u, v\}$ exactly when $u \ne v$ and the matrix has a $1$ in position $(u, v)$ or $(v, u)$.
--
--   The helper `toEdges` reads a list of pairs of numbers as a set of edges of $V$: a pair $(a, b)$ with $a, b < n$ gives the unordered pair $\{a, b\}$, and pairs with an entry $\ge n$ are ignored. This is how the outputs of all algorithms in this mission are read back.
--
--   **Formalization Note** Every matrix gives a simple graph and every simple graph on $n$ vertices arises, so no well-formedness hypothesis is needed. A pair $(a, a)$ gives a diagonal element, which is never an edge, so an output containing one is infeasible.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §6, p.23

import Mathlib

namespace TwoConnSS

/-- **An instance of 2ECSS: a finite simple undirected graph on `{0, …, n−1}`.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §6, p.23: "All input graphs are
finite and undirected. They are simple unless a contraction or an auxiliary construction explicitly
creates parallel edges."

`n` is the number of vertices (`V = Fin n`) and `adj` is an `n × n` Boolean matrix.

**Formalization Note.** The graph of an instance (`Inst.graph`) has an edge `{u, v}` exactly when
`u ≠ v` and `adj u v` or `adj v u` holds, so every matrix gives a simple graph and every simple graph
on `Fin n` is the graph of some instance; no well-formedness hypothesis is needed. -/
structure Inst where
  n : ℕ
  adj : Fin n → Fin n → Bool

/-- The simple graph `G` of an instance: `u ∼ v` iff `u ≠ v` and the matrix has a `1` at `(u, v)`
or at `(v, u)`. -/
def Inst.graph (I : Inst) : SimpleGraph (Fin I.n) where
  Adj u v := u ≠ v ∧ (I.adj u v = true ∨ I.adj v u = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The edge set of `Fin n` read off a list of pairs of numbers.** A pair `(a, b)` with
`a, b < n` gives the unordered pair `{a, b}`; pairs with an entry `≥ n` are ignored. A pair `(a, a)`
gives the diagonal element `{a, a}`, which is never an edge of a simple graph, so an output
containing it fails every "`F ⊆ E(G)`" clause. -/
def toEdges (n : ℕ) (l : List (ℕ × ℕ)) : Finset (Sym2 (Fin n)) :=
  (l.filterMap fun p => if h : p.1 < n ∧ p.2 < n then some s(⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else none).toFinset

end TwoConnSS


