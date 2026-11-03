-- Prove2me | Definitions.Def_FulfillFlex_Assumption1
-- name    : FulfillFlex_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:04.269479+00:00
-- url     : https://prove2.me/theorems/5c1a837d-9f51-4a08-ab93-d906af528849
-- title:
--   Assumption 1 — cost structure of the network
-- statement:
--   Let $A$ be the set of links, $c_{jj'}$ the unit fulfillment cost of satisfying demand at DC $j'$ from DC $j$, and $p_j$ the unit lost sales cost at DC $j$. **Assumption 1** requires
--
--   $$
--   p_j\ge c_{jj}>0\quad\forall j,\qquad
--   c_{j'j'}\le c_{jj'}\le p_{j'}\quad\forall (j,j')\in A,\qquad
--   p_{j'}+c_{jj}\le p_j+c_{jj'}\quad\forall (j,j')\in A.
--   $$
--
--   So costs are positive, a lost sale costs at least a fulfillment, local fulfillment is the cheapest way to serve a DC, and the firm always prefers to trade a lost sale at $j$ and a spillover to $j'$ for a local fulfillment at $j$ and a lost sale at $j'$. The assumption is standing throughout the paper.
--
--   **Formalization Note** Displays (1)–(3) of the paper are the five fields of a structure. Costs off the links are unconstrained, and no statement reads them.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Assumption 1, displays (1)–(3), p.6

import Mathlib
import Definitions.Def_FulfillFlex_DC

namespace FulfillFlex

/-- **Assumption 1 (cost structure).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Assumption 1, displays (1)–(3), p.6:
`p_j ≥ c_jj > 0` for all `j`; `c_{j'j'} ≤ c_{jj'} ≤ p_{j'}` for all `(j, j') ∈ A`; and
`p_{j'} + c_jj ≤ p_j + c_{jj'}` for all `(j, j') ∈ A`.

**Formalization Note** `c j j'` is `c_{jj'}`, source first. Costs off the links are not
constrained; no statement of this mission reads them. -/
structure Assumption1 {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ) :
    Prop where
  /-- Display (1), left inequality: a lost sale costs at least a local fulfillment. -/
  local_le_lost : ∀ j, c j j ≤ p j
  /-- Display (1), right inequality: local fulfillment has positive cost. -/
  local_pos : ∀ j, 0 < c j j
  /-- Display (2), left inequality: local fulfillment is at most as costly as spillover. -/
  local_le_link : ∀ j j', (j, j') ∈ A → c j' j' ≤ c j j'
  /-- Display (2), right inequality: spillover is at most as costly as a lost sale. -/
  link_le_lost : ∀ j j', (j, j') ∈ A → c j j' ≤ p j'
  /-- Display (3). -/
  exchange : ∀ j j', (j, j') ∈ A → p j' + c j j ≤ p j + c j j'

end FulfillFlex


