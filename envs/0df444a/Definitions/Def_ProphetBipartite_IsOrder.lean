-- Prove2me | Definitions.Def_ProphetBipartite_IsOrder
-- name    : ProphetBipartite_IsOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:17.160663+00:00
-- url     : https://prove2.me/theorems/34a695f5-2bb3-40a9-89d1-25a3ef26588c
-- title:
--   Arrival orders of the edges
-- statement:
--   The edges arrive online in an order $\sigma=(e(t))_{t=1}^{T}$, enumerated by arrival time from $1$ to $T=|E|$. An **arrival order** is a list of edges in which every edge of $E$ occurs exactly once.
--
--   The prophet inequality of the mission holds for every arrival order.
--
--   **Formalization Note** `IsOrder σ` is `σ.Nodup ∧ ∀ e, e ∈ σ`; an order that omits an edge is excluded. The paper's adversary may also choose a distribution over orders, which reduces to fixed orders by averaging.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §2, p.4

import Mathlib

namespace ProphetBipartite

/-- **Arrival orders.** Gravin & Wang, arXiv:1902.06243v1, §2, p.4: "The edges arrive online in an
unknown order `σ = (e(t))_{t=1}^{T}`, where edges are enumerated by their arrival time from 1 to
`T = |E|`."

An arrival order is a list of edges in which every edge of `E` occurs exactly once.

**Formalization Note.** `σ.Nodup ∧ ∀ e, e ∈ σ` says that `σ` enumerates `E`, so its length is
`|E|`. An order that omits an edge is excluded. -/
def IsOrder {E : Type*} (σ : List E) : Prop :=
  σ.Nodup ∧ ∀ e, e ∈ σ

end ProphetBipartite


