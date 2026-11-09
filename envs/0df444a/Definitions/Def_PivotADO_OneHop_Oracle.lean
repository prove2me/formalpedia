-- Prove2me | Definitions.Def_PivotADO_OneHop_Oracle
-- name    : PivotADO_OneHop_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:12.182432+00:00
-- url     : https://prove2.me/theorems/dfa8267a-d802-4785-8d77-87f4472765db
-- title:
--   Definition 2 — r-pivot 1-hop k-stretch oracle
-- statement:
--   For a graph $G$, integer $r\ge1$ and real $k\ge1$, an oracle consists of a weighted storage graph $H$ on the same vertices and finite pivot sets $\mathcal P(v)$ containing $v$, each of cardinality at most $r$. Stored weights dominate $\delta_G$ on every edge. Its estimate is
--
--   $$D_{H,\mathcal P}(u,v)=\min_{p_u\in\mathcal P(u),\ p_v\in\mathcal P(v)}W_H(u,v;p_u,p_v),\qquad
--   \delta_G(u,v)\le D_{H,\mathcal P}(u,v)\le k\delta_G(u,v).$$
--
--   Both inequalities hold for all queries, including equal endpoints and distinct components. The minimum is over nonempty finite sets and is attained, even if its value is infinite. A realizing pivot pair includes membership in both pivot sets and equality of its weight to this minimum. Space is the number of unordered edges of $H$; no query algorithm is required. The parameter ranges $r\ge1$, $k\ge1$ are supplied by each theorem. Nonnegative extended weights include finite-weight oracles as a special case.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Definition 2, (5.1) and §5.1 realizing walk, p.17,19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_WeightedGraph

set_option autoImplicit false
open scoped Classical ENNReal
noncomputable section

namespace PivotADO.OneHop

/-- The finite minimum in Definition 2, equation (5.1), p.17.
In an Oracle each indexing finset contains its own endpoint. -/
def estimate {V : Type*} (H : WeightedGraph V) (pivots : V → Finset V)
    (u v : V) : ℝ≥0∞ :=
  ⨅ pu ∈ pivots u, ⨅ pv ∈ pivots v, walkWeight H u v pu pv

/-- An r-pivot 1-hop k-stretch ADO, Definition 2, p.17.
Infinite weights are allowed, counted, and never helpful on a reachable query. -/
structure Oracle {V : Type*} (G : SimpleGraph V) (r : ℕ) (k : ℝ) where
  storage : WeightedGraph V
  pivots : V → Finset V
  self_mem : ∀ v, v ∈ pivots v
  card_le : ∀ v, (pivots v).card ≤ r
  dominates : ∀ u v, storage.graph.Adj u v → distance G u v ≤ storage.weight u v
  bounds : ∀ u v, distance G u v ≤ estimate storage pivots u v ∧
    estimate storage pivots u v ≤ ENNReal.ofReal k * distance G u v

/-- A particular pair of pivots attains the finite minimum, including its pivot membership. -/
def Realizes {V : Type*} {G : SimpleGraph V} {r : ℕ} {k : ℝ}
    (O : Oracle G r k) (u v pu pv : V) : Prop :=
  pu ∈ O.pivots u ∧ pv ∈ O.pivots v ∧
    walkWeight O.storage u v pu pv = estimate O.storage O.pivots u v

end PivotADO.OneHop


