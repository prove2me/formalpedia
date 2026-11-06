-- Prove2me | Definitions.Def_CompetingSellers_selectedPlans
-- name    : CompetingSellers_selectedPlans
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:32.649394+00:00
-- url     : https://prove2.me/theorems/f77a7901-de3e-4655-81cd-6f1202b9cf80
-- title:
--   The buyer's tie-broken utility-maximizing plans
-- statement:
--   For mechanisms $M_A,M_B$ the buyer's **selected plans** are the plans that lexicographically maximize
--   $$\big(\mathrm{util},\ \mathrm{rev}_B,\ \mathrm{rev}_A,\ X_B,\ X_A,\ \mathbf 1\{\text{order }AB\}\big):$$
--   first the buyer's expected utility, then (among the utility maximizers) Bob's expected revenue, then Alice's expected revenue, then the probability of obtaining Bob's good, then that of obtaining Alice's good, and finally the order $AB$ over $BA$.
--
--   This is the buyer behaviour of the paper's main model (p.15: "the buyer breaks ties first in favor of maximizing the expected revenue of Bob, then in favor of maximizing the expected revenue of Alice …"); Observation A.2 shows the set is nonempty and Observation A.5 that all selected plans give the same payoffs.
--
--   **Formalization Note** The set is defined by nested maximizer sets over all plans, without assuming that any maximum is attained. Messages on branches of probability zero do not affect any coordinate and are not constrained. `selectedPlansFrom a b i` is the same successive maximization over the plans approaching seller $i$ first, the buyer's selection in the fixed-order models of Observation A.2 ($i$ = Alice: aligned; $i$ = Bob: misaligned).
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2, p.15 (PDF 18); Observation A.5, p.53

import Mathlib
import Definitions.Def_CompetingSellers_Plan

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- The maximizers of `f` on `s` (empty if the supremum is not attained). -/
def argmaxOn {α β : Type} [Preorder β] (f : α → β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

/-- **The buyer's tie-broken utility-maximizing plans** (§2, p.15).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.15 (PDF 18): the buyer selects an action plan maximizing
his expected utility; "Consider a tie-breaking rule under which the buyer breaks ties first in
favor of maximizing the expected revenue of Bob, then in favor of maximizing the expected revenue
of Alice. If ties still remain, they are broken in favor of maximizing the probability of
obtaining the good from Bob, then in favor of maximizing the probability of obtaining the good
from Alice. Any remaining tie is broken in favor of the order AB."

`selectedPlans a b A B` is the set of plans that successively maximize
`(util, rev_B, rev_A, X_B, X_A, 1{order AB})` (Observation A.5, p.53).

**Formalization Note.** The successive maximizations are nested `argmaxOn`s over all plans; the
set may a priori be empty (Observation A.2 (i) states it is not). Choices on branches reached
with probability zero do not change any coordinate (they enter with weight `0`), so they are
unrestricted here; every statement about them is made only on reached branches (footnote 18,
Definition 2.1). -/
def selectedPlans {S : Type} [MeasurableSpace S] {null : S} (a b : ℝ) (A B : Mech S null) :
    Set (Plan S) :=
  argmaxOn (fun π : Plan S => if π.first = Seller.alice then (1 : ℕ) else 0)
    (argmaxOn (fun π : Plan S => π.totalAlloc A B Seller.alice)
      (argmaxOn (fun π : Plan S => π.totalAlloc A B Seller.bob)
        (argmaxOn (fun π : Plan S => π.rev A B Seller.alice)
          (argmaxOn (fun π : Plan S => π.rev A B Seller.bob)
            (argmaxOn (fun π : Plan S => π.util a b A B) Set.univ)))))

/-- **The buyer's selected plans in a fixed-order model** (Observation A.2, p.50: "with buyer plans
restricted to the prescribed order"): the plans approaching seller `i` first that successively
maximize `(util, rev_B, rev_A, X_B, X_A)` among such plans. `i = alice` is the aligned model and
`i = bob` the misaligned model (p.50, footnote 23: the final order preference is irrelevant when the
order is fixed). -/
def selectedPlansFrom {S : Type} [MeasurableSpace S] {null : S} (a b : ℝ) (i : Seller)
    (A B : Mech S null) : Set (Plan S) :=
  argmaxOn (fun π : Plan S => π.totalAlloc A B Seller.alice)
    (argmaxOn (fun π : Plan S => π.totalAlloc A B Seller.bob)
      (argmaxOn (fun π : Plan S => π.rev A B Seller.alice)
        (argmaxOn (fun π : Plan S => π.rev A B Seller.bob)
          (argmaxOn (fun π : Plan S => π.util a b A B) {π | π.first = i}))))

end CompetingSellers


