-- Prove2me | Definitions.Def_BayesClock_SinglePriceAuction
-- name    : BayesClock_SinglePriceAuction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:10.958308+00:00
-- url     : https://prove2.me/theorems/eb81f858-1139-47e9-92a1-9331412a778d
-- title:
--   Deterministic single-price clock auction (Mechanism 1)
-- statement:
--   A **deterministic single-price clock auction** on $\mathcal F$ consists of a vector of prices $p=(p_i)_{i\in N}$ and a rule that assigns to each set $A$ of buyers a feasible subset of $A$. It runs as follows:
--
--   1. the price $p_i$ is posted to each buyer $i$;
--   2. buyer $i$ stays exactly when $p_i\le v_i$;
--   3. among the set $A$ of buyers who stayed, the rule selects the preferred feasible subset $F\subseteq A$, $F\in\mathcal F$;
--   4. the buyers of $F$ are served and each pays $p_i$; all other buyers pay $0$.
--
--   The welfare on $v$ is $\sum_{i\in F}v_i$, and the expected welfare is its expectation under the product law $D=\times_{i\in N}D_i$ of the values.
--
--   Prices are fixed before any value is seen, and the rule reads only the set of buyers who stayed. These two restrictions are what separate a clock auction from a sealed-bid auction, which could read the values and serve the best set.
--
--   **Formalization Note** The auction is a structure with fields `price`, `select`, `select_subset` and `select_mem`, and may depend on the prior, because the Bayesian seller knows it. The expected welfare is an $\mathbb R_{\ge0}\cup\{\infty\}$-valued lower integral, so it needs no integrability assumption. This module also holds `accepted`, `winners`, `payment`, `welfare` and `expectedWelfare`.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Mechanism 1, §3, p.6; §2, pp.5–6

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- A deterministic single-price clock auction on the feasibility constraint `𝓕`: Mechanism 1,
Feldman et al., arXiv:2202.09291v1, §3, p.6. It posts the vector of prices `price`, and among the
set `A` of bidders who stay it selects the preferred feasible subset `select A`.

**Formalization Note** `price` does not depend on the values, and `select` reads the set of
acceptors only, never the values: this is what separates a clock auction from a sealed-bid auction.
Determinism is the absence of any random seed. The structure is chosen after the prior, since
prices may use public information, which in the Bayesian setting includes the distribution (§2,
pp.5–6). -/
structure SinglePriceAuction {N : Type*} (𝓕 : Finset (Finset N)) where
  /-- Line 1 of Mechanism 1: the vector of prices `p`. -/
  price : N → ℝ≥0
  /-- Line 3 of Mechanism 1: the preferred subset of the bidders who stayed. -/
  select : Finset N → Finset N
  /-- The preferred subset consists of bidders who stayed. -/
  select_subset : ∀ A, select A ⊆ A
  /-- The preferred subset is feasible. -/
  select_mem : ∀ A, select A ∈ 𝓕

namespace SinglePriceAuction

variable {N : Type*} [Fintype N] {𝓕 : Finset (Finset N)}

/-- Line 2 of Mechanism 1, p.6: bidder `i` stays exactly when `p i ≤ v i`, the event `I[vi ≥ p]` of
Lemma 3, p.10; a bidder at equality stays. -/
noncomputable def accepted (a : SinglePriceAuction 𝓕) (v : N → ℝ≥0) : Finset N :=
  Finset.univ.filter (fun i => a.price i ≤ v i)

/-- Line 4 of Mechanism 1, p.6: the accepted bidders, on the value vector `v`. They depend on `v`
only through `accepted`. -/
noncomputable def winners (a : SinglePriceAuction 𝓕) (v : N → ℝ≥0) : Finset N :=
  a.select (a.accepted v)

/-- Line 4 of Mechanism 1, p.6: a winner is charged `p i`, every other bidder pays `0`. -/
noncomputable def payment [DecidableEq N] (a : SinglePriceAuction 𝓕) (v : N → ℝ≥0) (i : N) : ℝ≥0 :=
  if i ∈ a.winners v then a.price i else 0

/-- The social welfare `SW(F) = ∑ i ∈ F, v i` of the served set `F`, §2, p.5, in `ℝ≥0∞`. -/
noncomputable def welfare (a : SinglePriceAuction 𝓕) (v : N → ℝ≥0) : ℝ≥0∞ :=
  ∑ i ∈ a.winners v, (v i : ℝ≥0∞)

/-- The expected social welfare `E v∼D [auc]` of the auction, §2, p.5, where `D = ×ᵢ Dᵢ` is the
product of the laws `ν i`.

**Formalization Note** A lower Lebesgue integral with values in `ℝ≥0∞`: no integrability is
required, and an infinite expectation is the value `∞`, not a junk `0`. -/
noncomputable def expectedWelfare (a : SinglePriceAuction 𝓕)
    (ν : N → Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, a.welfare v ∂Measure.pi ν

end SinglePriceAuction

end BayesClock


