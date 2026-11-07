-- Prove2me | Definitions.Def_MCPoise_Inst
-- name    : MCPoise_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:47.096583+00:00
-- url     : https://prove2.me/theorems/d8f33ffa-4897-4032-adbd-dcae2c43afbc
-- title:
--   An instance of multicommodity poise: a graph with indexed demand pairs
-- statement:
--   An **instance** of the multicommodity poise problem consists of an undirected graph $G = (V, E)$ with $V = \{0, \dots, n-1\}$, given by a list of edges, and a list of demand pairs $D = ((s_1, t_1), \dots, (s_k, t_k))$ of vertices.
--
--   The graph $G$ has an edge $\{u, v\}$ exactly when $u \ne v$ and $(u, v)$ or $(v, u)$ is listed.
--
--   Demands are counted by their position in the list, so a pair may repeat, a vertex may be a terminal of several demands, and $s_i = t_i$ is allowed. The instance with $n = 0$ or $k = 0$ is allowed too.
--
--   **Formalization Note** Vertices have the type `Fin n`, so every instance is well-formed by its type.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1.2, p.3; footnote 2, p.9; Appendix B, p.35

import Mathlib

namespace MCPoise

/-- The simple graph on `Fin n` with an edge `{u, v}` for every listed pair with `u ≠ v`. Loops and
repeated entries of the list are harmless and do not change the graph. -/
def listGraph {n : ℕ} (l : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ l ∨ (v, u) ∈ l)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **An instance of MC Poise.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1.2, p.3: "given an undirected graph G = (V, E) with demand pairs D = {(s₁, t₁), . . . , (s_k, t_k)}".

`n` is the number of vertices (`V = Fin n`), `edges` lists the edges and `dem` the demand pairs.

**Formalization Note.** Vertices are `Fin n`, so every instance is well-formed by its type. Demands are
indexed by their position in `dem` (footnote 2, p.9; p.35: "We work with demand indices, so distinct
demands are counted separately even if their chosen paths coincide"): repeated demands, repeated
terminals and `s_i = t_i` are all allowed, as are `n = 0` and `k = 0`. -/
structure Inst where
  n : ℕ
  edges : List (Fin n × Fin n)
  dem : List (Fin n × Fin n)

/-- The graph `G` of an instance. -/
abbrev Inst.graph (I : Inst) : SimpleGraph (Fin I.n) := listGraph I.edges

/-- The number `k` of demand pairs. -/
abbrev Inst.k (I : Inst) : ℕ := I.dem.length

/-- The source `s_i`. -/
def Inst.s (I : Inst) (i : Fin I.k) : Fin I.n := (I.dem.get i).1

/-- The sink `t_i`. -/
def Inst.t (I : Inst) (i : Fin I.k) : Fin I.n := (I.dem.get i).2

/-- The terminal of the demand `i` on side `b`: `s_i` for `false`, `t_i` for `true`. -/
def Inst.term (I : Inst) (i : Fin I.k) (b : Bool) : Fin I.n := if b then I.t i else I.s i

end MCPoise


