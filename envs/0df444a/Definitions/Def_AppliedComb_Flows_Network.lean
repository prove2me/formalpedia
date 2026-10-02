-- Prove2me | Definitions.Def_AppliedComb_Flows_Network
-- name    : AppliedComb_Flows_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:37:42.677189+00:00
-- url     : https://prove2.me/theorems/db706693-945d-49ad-b014-05231acb208e
-- title:
--   Networks, flows, their values, cuts and cut capacities (Sections 13.1–13.2)
-- statement:
--   A **network** consists of a finite set $V$ of vertices, a set of directed edges $(x, y)$ between them, two distinct vertices $S$ (the **source**) and $T$ (the **sink**), and a **capacity** $c(x, y) \ge 0$ on each edge $(x, y)$. The directed graph is an **oriented graph**: for each pair of vertices $x, y$ at most one of $(x, y)$ and $(y, x)$ is an edge. All edges incident with the source are oriented away from it and all edges incident with the sink are oriented towards it, so no edge enters $S$ and no edge leaves $T$.
--
--   A **flow** $\phi$ assigns to each edge $(x, y)$ a value $0 \le \phi(x, y) \le c(x, y)$; following the book's convention, $\phi(x, y) = 0$ when $(x, y)$ is not an edge. It must satisfy the two conservation laws
--   $$\sum_{x} \phi(S, x) = \sum_{x} \phi(x, T), \qquad \sum_{x} \phi(x, y) = \sum_{x} \phi(y, x) \quad (y \ne S, T).$$
--   The common value of the two sides of the first law, $\sum_x \phi(S, x)$, is the **value** of $\phi$.
--
--   A **cut** is a partition $V = L \cup U$ with $S \in L$ and $T \in U$. Its **capacity** is
--   $$c(L, U) = \sum_{x \in L,\ y \in U} c(x, y),$$
--   the total capacity of the edges directed from $L$ to $U$; edges from $U$ to $L$ are not counted.
--
--   These are the objects of the Max Flow–Min Cut Theorem (Theorem 13.10) and of the weak duality bound (Theorem 13.4).
--
--   **Formalization Note.** The vertex set is a type `V` with `[Fintype V] [DecidableEq V]`; the edge set is a relation `adj`, and the capacity is a function `cap : V → V → ℝ` whose values off the edges are never used. A flow is any `ϕ : V → V → ℝ` satisfying `IsFlow`, which includes the book's convention `ϕ(x, y) = 0` for non-edges; the first conservation law is kept as part of the definition, as on the page. A cut is represented by its part `L : Finset V`, with `U = Lᶜ`. The phrase "oriented with the sink" (p. 259) is read as "oriented towards the sink", as p. 269 confirms ("all edges incident with the sink are oriented towards the sink"). Capacities are arbitrary non-negative reals: zero capacities are allowed and irrational ones are not excluded.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 259–262, Sections 13.1–13.2 (network, flow, value, cut, capacity of a cut)

import Mathlib

namespace AppliedComb.Flows

/-- A network (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 259, Section 13.1)
on a finite vertex set `V`.

* `adj x y` says that the directed edge `(x, y)` is present. The underlying directed graph is
  an **oriented graph**: for each pair of vertices `x, y` at most one of `(x, y)` and `(y, x)`
  is an edge (`oriented`; taking `x = y` this also excludes loops).
* `S` is the **source** and `T` the **sink**, two distinct vertices. All edges incident with the
  source are oriented away from the source (`no_edge_into_source`), and all edges incident with
  the sink are oriented towards the sink (`no_edge_out_of_sink`).
* `cap x y` is the **capacity** `c(x, y)` of the edge `(x, y)`, a non-negative real number
  (`cap_nonneg`). Values of `cap` on pairs that are not edges are never used. -/
structure Network (V : Type*) [Fintype V] [DecidableEq V] where
  /-- `adj x y` : the directed edge `(x, y)` belongs to the network. -/
  adj : V → V → Prop
  /-- The source `S`. -/
  S : V
  /-- The sink `T`. -/
  T : V
  /-- The capacity `c(x, y)` of the edge `(x, y)`. -/
  cap : V → V → ℝ
  source_ne_sink : S ≠ T
  oriented : ∀ x y, adj x y → ¬ adj y x
  no_edge_into_source : ∀ x, ¬ adj x S
  no_edge_out_of_sink : ∀ y, ¬ adj T y
  cap_nonneg : ∀ x y, adj x y → 0 ≤ cap x y

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **flow** `ϕ` in the network `N` (Keller & Trotter, pp. 259–260): a function assigning to
each directed edge `e = (x, y)` a value with `0 ≤ ϕ(x, y) ≤ c(x, y)`, extended by the book's
convention `ϕ(x, y) = 0` when `(x, y)` is not an edge (p. 262), such that the conservation
laws hold:
1. `∑ₓ ϕ(S, x) = ∑ₓ ϕ(x, T)` (the amount leaving the source equals the amount arriving at the
   sink);
2. for every vertex `y` other than the source and the sink, `∑ₓ ϕ(x, y) = ∑ₓ ϕ(y, x)`. -/
def IsFlow (N : Network V) (ϕ : V → V → ℝ) : Prop :=
  (∀ x y, N.adj x y → 0 ≤ ϕ x y ∧ ϕ x y ≤ N.cap x y) ∧
  (∀ x y, ¬ N.adj x y → ϕ x y = 0) ∧
  (∑ x, ϕ N.S x = ∑ x, ϕ x N.T) ∧
  (∀ y, y ≠ N.S → y ≠ N.T → ∑ x, ϕ x y = ∑ x, ϕ y x)

/-- The **value** of a flow `ϕ` (p. 260): the amount `∑ₓ ϕ(S, x)` leaving the source. -/
def value (N : Network V) (ϕ : V → V → ℝ) : ℝ :=
  ∑ x, ϕ N.S x

/-- A **cut** (p. 261): a partition `V = L ∪ U` of the vertex set with `S ∈ L` and `T ∈ U`.
It is represented by the part `L`; the other part is `U = Lᶜ`. -/
def IsCut (N : Network V) (L : Finset V) : Prop :=
  N.S ∈ L ∧ N.T ∉ L

open Classical in
/-- The **capacity** `c(L, U)` of the cut `V = L ∪ U` (p. 261): the total capacity of all edges
from `L` to `U = Lᶜ`,
`c(L, U) = ∑_{x ∈ L, y ∈ U} c(x, y)`, where only directed edges `(x, y)` with `x ∈ L`, `y ∈ U`
are counted (edges from `U` to `L` are not included). -/
noncomputable def cutCapacity (N : Network V) (L : Finset V) : ℝ :=
  ∑ x ∈ L, ∑ y ∈ Lᶜ, if N.adj x y then N.cap x y else 0

end Network

end AppliedComb.Flows


