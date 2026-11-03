-- Prove2me | Definitions.Def_FulfillFlex_Assumption2
-- name    : FulfillFlex_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:08.921222+00:00
-- url     : https://prove2.me/theorems/40156fba-177a-450c-8bf6-781221a35568
-- title:
--   Assumption 2 — transitive links and the cost inequality (6)
-- statement:
--   **Assumption 2** requires that for any links $(j,j'),(j',j'')\in A$ we have $(j,j'')\in A$ and
--
--   $$
--   c_{jj''}+c_{j'j'}\le c_{jj'}+c_{j'j''}.
--   $$
--
--   It says that the network favors local fulfillment. It is what lets an optimal solution of the deterministic program spill out of a DC only after that DC's own demand is covered, and the paper shows that local no-holdback policies can fail to be asymptotically optimal without it.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Assumption 2, display (6), p.16

import Mathlib
import Definitions.Def_FulfillFlex_DC

namespace FulfillFlex

/-- **Assumption 2 (network structure and costs).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Assumption 2, display (6), p.16:
"For any (j,j′),(j′,j′′) ∈ A, we have (j,j′′) ∈ A and c_{jj′′} + c_{j′j′} ≤ c_{jj′} + c_{j′j′′}."

**Formalization Note** `c j j'` is `c_{jj'}`, source first. -/
structure Assumption2 {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) : Prop where
  /-- The link set is transitive. -/
  trans : ∀ j j' j'', (j, j') ∈ A → (j', j'') ∈ A → (j, j'') ∈ A
  /-- Display (6). -/
  cost : ∀ j j' j'', (j, j') ∈ A → (j', j'') ∈ A → c j j'' + c j' j' ≤ c j j' + c j' j''

end FulfillFlex


