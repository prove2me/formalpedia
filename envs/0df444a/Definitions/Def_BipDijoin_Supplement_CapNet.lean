-- Prove2me | Definitions.Def_BipDijoin_Supplement_CapNet
-- name    : BipDijoin_Supplement_CapNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:49:54.773073+00:00
-- url     : https://prove2.me/theorems/ccff9089-5846-4789-8215-c7abe2aa913e
-- title:
--   Capacitated multidigraphs with source and sink capacities, and partial routings (Definition 5.1)
-- statement:
--   A **capacitated multidigraph** $N$ has vertices $V=\{0,\dots,n-1\}$ and arcs $j=0,\dots,m-1$, arc $j$ going from its tail to its head with a rational capacity $c(j)$; parallel arcs are distinct indices. It also carries a **source capacity** (supply) $\Delta:V\to\mathbb Q$ and a **sink capacity** $\nabla:V\to\mathbb Q$. Write $\deg^+(v)$ for the number of arcs leaving $v$ (with multiplicity, independently of capacity), and for $S\subseteq V$
--   $$c(\delta^+(S))=\sum_{j:\ \mathrm{tail}(j)\in S,\ \mathrm{head}(j)\notin S}c(j),\qquad \Delta(S)=\sum_{v\in S}\Delta(v),\qquad \nabla(S)=\sum_{v\in S}\nabla(v),$$
--   $\kappa=|\Delta|=\Delta(V)$ and $\operatorname{supp}(\Delta)=\{v:\Delta(v)\neq0\}$.
--
--   A flow $f$ **partially routes $\Delta$ and respects $\nabla$** (Definition 5.1) if there are functions $a$ (routed supply) and $b$ (absorbed flow) with
--   $$0\le f(j)\le c(j),\qquad 0\le a(v)\le\Delta(v),\qquad 0\le b(v)\le\nabla(v),\qquad a(v)+f(\delta^-(v))=b(v)+f(\delta^+(v))$$
--   for every arc $j$ and vertex $v$. The routing is **full** if this holds with $a=\Delta$.
--
--   This is the network of the local routing theorem (Theorem 5.2), which the local search for small strong ends (Theorem 3.4) calls on the alternating digraph.
--
--   **Formalization Note** Arc $j$ is the $j$-th entry $(\mathrm{tail},\mathrm{head},c)$ of a list. Flows and the witnesses $a,b$ are functions $\mathbb N\to\mathbb Q$; only their values on arcs $j<m$ and vertices $v<n$ are constrained. Nonnegativity of the data is imposed by the input conditions of the theorem that uses the network.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §5.1, p.15 (PDF p.17), input and routing conventions and Definition 5.1

import Mathlib

set_option autoImplicit false

namespace BipDijoin

namespace Supplement

/-!
# Capacitated multidigraphs with source and sink capacities, and partial routings

C. Nalam, T. Saranurak, *Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and
Local Graph Algorithms*, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §5.1, p.15
(PDF p.17): "Let G = (V, E) be a directed multigraph with nonnegative rational arc capacities c.
Write deg⁺_G(v) for the number of original arcs leaving v, counted with multiplicity and
independently of capacity. For S ⊆ V, write c(δ⁺_G(S)) = Σ_{uv∈E: u∈S, v∉S} c(uv),
x(S) = Σ_{v∈S} x(v), |x| = x(V)."
Definition 5.1 (Partial routing), p.15: "A flow f partially routes ∆ and respects ∇ if there exist
functions a, b satisfying 0 ≤ f(e) ≤ c(e), 0 ≤ a(v) ≤ ∆(v), 0 ≤ b(v) ≤ ∇(v),
a(v) + f(δ⁻_G(v)) = b(v) + f(δ⁺_G(v)) (v ∈ V). Here a is routed supply and b is absorbed flow.
The routing is full if these equations hold with a = ∆."

**Formalization Note.**
* The vertices are `0, …, n − 1`; arc `j` (`j < m`) is the `j`-th entry `(tail, head, capacity)`
  of `arcs`, so parallel arcs (and loops) are distinct indices. Capacities, the source capacity
  `∆` (`supply`) and the sink capacity `∇` (`sinkCap`) are rationals; their nonnegativity is part
  of the input conditions of the statements that use them. Values of `supply` and `sinkCap` at
  `v ≥ n` play no role.
* A flow, and the witnesses `a` (routed supply) and `b` (absorbed flow), are functions `ℕ → ℚ`;
  only the values on arcs `j < m` and vertices `v < n` are constrained.
-/

/-- A capacitated directed multigraph on the vertices `0, …, n − 1` with source capacities `∆` and
sink capacities `∇` (§5.1, p.15). -/
structure CapNet where
  /-- The number of vertices; the vertices are `0, …, n − 1`. -/
  n : ℕ
  /-- The arcs: arc `j` is `arcs[j] = (tail, head, capacity)`. -/
  arcs : List (ℕ × ℕ × ℚ)
  /-- The source capacity (supply) `∆(v)`. -/
  supply : ℕ → ℚ
  /-- The sink capacity `∇(v)`. -/
  sinkCap : ℕ → ℚ

namespace CapNet

variable (N : CapNet)

/-- The number `m` of arcs. -/
def m : ℕ := N.arcs.length

/-- The tail of arc `j`. -/
def tail (j : ℕ) : ℕ := (N.arcs.getD j (0, 0, 0)).1

/-- The head of arc `j`. -/
def head (j : ℕ) : ℕ := (N.arcs.getD j (0, 0, 0)).2.1

/-- The capacity `c(j)` of arc `j`. -/
def cap (j : ℕ) : ℚ := (N.arcs.getD j (0, 0, 0)).2.2

/-- `deg⁺(v)`: the number of arcs leaving `v`, with multiplicity, independently of capacity. -/
def outdeg (v : ℕ) : ℕ := ((Finset.range N.m).filter (fun j => N.tail j = v)).card

/-- `f(δ⁻(v))`: the flow on the arcs entering `v`. -/
def inflow (f : ℕ → ℚ) (v : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range N.m).filter (fun j => N.head j = v), f j

/-- `f(δ⁺(v))`: the flow on the arcs leaving `v`. -/
def outflow (f : ℕ → ℚ) (v : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range N.m).filter (fun j => N.tail j = v), f j

/-- `c(δ⁺(S))`: the total capacity of the arcs from `S` to its complement. -/
def cutCap (S : Finset ℕ) : ℚ :=
  ∑ j ∈ (Finset.range N.m).filter (fun j => N.tail j ∈ S ∧ N.head j ∉ S), N.cap j

/-- `∆(S) = Σ_{v ∈ S} ∆(v)`. -/
def setSupply (S : Finset ℕ) : ℚ := ∑ v ∈ S, N.supply v

/-- `∇(S) = Σ_{v ∈ S} ∇(v)`. -/
def setSink (S : Finset ℕ) : ℚ := ∑ v ∈ S, N.sinkCap v

/-- `κ = |∆| = ∆(V)`. -/
def kappa : ℚ := ∑ v ∈ Finset.range N.n, N.supply v

/-- `supp(∆)`: the vertices with nonzero supply. -/
def supp : Finset ℕ := (Finset.range N.n).filter (fun v => N.supply v ≠ 0)

/-- The conditions of Definition 5.1 for the flow `f` with routed supply `a` and absorbed flow
`b`: capacity constraints, `0 ≤ a ≤ ∆`, `0 ≤ b ≤ ∇`, and conservation
`a(v) + f(δ⁻(v)) = b(v) + f(δ⁺(v))` at every vertex. -/
def IsRouting (f a b : ℕ → ℚ) : Prop :=
  (∀ j < N.m, 0 ≤ f j ∧ f j ≤ N.cap j) ∧
    ∀ v < N.n, (0 ≤ a v ∧ a v ≤ N.supply v) ∧ (0 ≤ b v ∧ b v ≤ N.sinkCap v) ∧
      a v + N.inflow f v = b v + N.outflow f v

/-- `f` **partially routes** `∆` and **respects** `∇` (Definition 5.1). -/
def PartiallyRoutes (f : ℕ → ℚ) : Prop := ∃ a b, N.IsRouting f a b

/-- `f` **fully routes** `∆` and respects `∇`: Definition 5.1 with `a = ∆`. -/
def FullyRoutes (f : ℕ → ℚ) : Prop := ∃ b, N.IsRouting f N.supply b

end CapNet

end Supplement

end BipDijoin


