-- Prove2me | Definitions.Def_BayesClock_IsZeroPriceAuction
-- name    : BayesClock_IsZeroPriceAuction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:18.965637+00:00
-- url     : https://prove2.me/theorems/443204a7-b514-4b3d-805e-e3259f640d4c
-- title:
--   The zero-price auction $\mathrm{auc}_o$
-- statement:
--   The auction $\mathrm{auc}_o$ posts the price $0$ to every bidder and serves a maximal feasible set of largest total expected value $\sum_{i\in S}\mathbb E[v_i]$, rejecting all other bidders.
--
--   **Formalization Note** A predicate on single-price auctions. At price $0$ every bidder stays, so only the rule's value on the set of all bidders matters.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §4, p.12; §3.2, p.9; §A.3, p.21

import Mathlib
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_SinglePriceAuction
import Definitions.Def_BayesClock_expectedValue

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The auction `auc_o`: Feldman et al., arXiv:2202.09291v1, §4, p.12 ("accepting all the bidders of
that set, for a price of 0, and rejecting all other bidders") and §3.2, p.9 ("sets zero prices to all
bidders and selects the set with maximum expected value"). All prices are `0` and the preferred set
is a maximal feasible set of largest total expected value.

**Formalization Note** At price `0` every bidder stays, because values are nonnegative, so the set of
acceptors is always `Finset.univ` and only `select Finset.univ` matters. -/
structure IsZeroPriceAuction {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (ν : N → Measure ℝ≥0) (a : SinglePriceAuction 𝓕) : Prop where
  /-- All prices are zero. -/
  price_eq_zero : ∀ i, a.price i = 0
  /-- The preferred set is a maximal feasible set. -/
  select_univ_mem : a.select Finset.univ ∈ maximalSets 𝓕
  /-- The preferred set has the largest total expected value. -/
  select_univ_max : ∀ S ∈ maximalSets 𝓕,
    ∑ i ∈ S, expectedValue (ν i) ≤ ∑ i ∈ a.select Finset.univ, expectedValue (ν i)

end BayesClock


