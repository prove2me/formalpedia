-- Prove2me | Definitions.Def_FulfillFlex_DC
-- name    : FulfillFlex_DC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:29.996197+00:00
-- url     : https://prove2.me/theorems/cddec91d-7f7a-4ced-881f-f8ad00c7af9a
-- title:
--   Distribution centers $0,\dots,N$
-- statement:
--   The fulfillment network has $N+1$ **distribution centers** (DCs), indexed by $0\le j\le N$. Each DC is primarily responsible for the orders of its own district. A **link** $(j,j')$ means that DC $j$ may satisfy demand at DC $j'$, and the set of links is a subset $A$ of ordered pairs of DCs.
--
--   This index set carries every object of the mission: costs, demand, inventory, flows and limits.
--
--   **Formalization Note** `DC N` is `Fin (N + 1)`. Its linear order breaks cost ties in the spillover limit policy. Costs are written source first: `c j j'` is $c_{jj'}$, the unit cost of satisfying demand at DC $j'$ from DC $j$.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), §1.3, pp.4–5

import Mathlib

namespace FulfillFlex

/-- **Distribution centers.**
DeValve, Wei, Wu, Yuan, *Understanding the Value of Fulfillment Flexibility in an Online Retailing
Environment*, SSRN 3265838 (2021-01-18 version), §1.3, p.4: "There are N + 1 distribution centers
(DCs) and N + 1 districts, indexed by 0 ≤ j ≤ N".

`DC N` is the index set `{0, …, N}` of the `N + 1` DCs. Its linear order is what breaks cost ties
in the spillover limit policy.

**Formalization Note** A link set is a `Set (DC N × DC N)`, with `(j, j') ∈ A` meaning that DC `j`
may serve demand at DC `j'` (p.5). Costs are written source first: `c j j'` is the paper's
`c_{jj'}`, the unit cost of satisfying demand at DC `j'` from DC `j` (p.6). -/
abbrev DC (N : ℕ) : Type := Fin (N + 1)

end FulfillFlex


