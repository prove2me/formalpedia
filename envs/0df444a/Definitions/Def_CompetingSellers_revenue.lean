-- Prove2me | Definitions.Def_CompetingSellers_revenue
-- name    : CompetingSellers_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:42.794097+00:00
-- url     : https://prove2.me/theorems/083d00dd-1b47-4702-bc09-567972bcf21f
-- title:
--   Equilibrium revenues $\mathrm{rev}_A(M_A,M_B)$, $\mathrm{rev}_B(M_A,M_B)$ and the buyer's utility
-- statement:
--   For mechanisms $M_A,M_B$, $\mathrm{rev}_A(M_A,M_B)$ and $\mathrm{rev}_B(M_A,M_B)$ are the expected payments to Alice and to Bob when the buyer plays a selected (tie-broken utility-maximizing) plan; the buyer's equilibrium utility is the maximum of $\mathrm{util}(\pi)$ over all plans. Further, $\mathrm{util}_{AB}(M_A,M_B)$ and $\mathrm{util}_{BA}(M_A,M_B)$ are the maximum utilities over plans visiting Alice first, respectively Bob first (Lemma 3.1), and "the buyer interacts with seller $i$ first" means that a selected plan approaches $i$ first.
--
--   These values define the induced two-player game between the sellers.
--
--   **Formalization Note** All values are real numbers: selected plans never pay an infinite expected amount on a reached branch, and every utility and revenue lies in $[0,\max\{a,b\}]$. If no plan were selected the revenue would read $0$; Observation A.2 rules this out. `revenueFrom a b i` is the revenue under the fixed-order selection `selectedPlansFrom a b i`.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2, p.15 (PDF 18); Lemma 3.1, p.19

import Mathlib
import Definitions.Def_CompetingSellers_selectedPlans

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **Equilibrium revenues `rev_A(M_A, M_B)`, `rev_B(M_A, M_B)`** (§2, p.15).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.15 (PDF 18): "We therefore define `rev_A(M_A, M_B)` to
denote the expected payment the buyer makes to Alice, given equilibrium play by the buyer, when
his value for Alice's good is `a`, for Bob's good is `b`, and Alice's and Bob's mechanisms are
`M_A` and `M_B` respectively. Similarly, `rev_B(M_A, M_B)` will be the expected payment the buyer
makes to Bob under equilibrium play by the buyer."

`revenue a b A B i` is seller `i`'s expected revenue under the buyer's tie-broken
utility-maximizing plans (`selectedPlans`).

**Formalization Note.** All selected plans give the same revenues (they lexicographically
maximize a vector whose second and third coordinates are the revenues), so the value is the
supremum over selected plans, converted to `ℝ`. A selected plan never has an infinite expected
payment on a reached branch (its utility would be `−∞ <` the utility `0` of not participating),
so the conversion loses nothing; if no plan were selected the value would be `0`, which
Observation A.2 (i) excludes. -/
noncomputable def revenue (a b : ℝ) (A B : Mech S null) (i : Seller) : ℝ :=
  (⨆ π ∈ selectedPlans a b A B, π.rev A B i).toReal

/-- The buyer's equilibrium expected utility: the maximum of `util(A, B, π)` over all plans
(converted to `ℝ`; it lies in `[0, max a b]`). -/
noncomputable def buyerUtil (a b : ℝ) (A B : Mech S null) : ℝ :=
  (⨆ π : Plan S, π.util a b A B).toReal

/-- `util_{AB}(A, B)` (for `i = alice`) and `util_{BA}(A, B)` (for `i = bob`), Lemma 3.1, p.19:
the maximum utility the buyer can obtain when interacting with seller `i` first. -/
noncomputable def orderUtil (a b : ℝ) (A B : Mech S null) (i : Seller) : ℝ :=
  (⨆ (π : Plan S) (_ : π.first = i), π.util a b A B).toReal

/-- "The buyer, when faced with this pair of mechanisms, interacts with seller `i` first": a
selected plan approaches `i` first (by Observation A.5 all selected plans share their order). -/
def BuyerFirst (a b : ℝ) (A B : Mech S null) (i : Seller) : Prop :=
  ∃ π ∈ selectedPlans a b A B, π.first = i

/-- Seller `j`'s expected revenue in the fixed-order model where the buyer must approach seller `i`
first (`revenue` with `selectedPlansFrom`; Observation A.2, p.50). -/
noncomputable def revenueFrom (a b : ℝ) (i : Seller) (A B : Mech S null) (j : Seller) : ℝ :=
  (⨆ π ∈ selectedPlansFrom a b i A B, π.rev A B j).toReal

end CompetingSellers


