-- Prove2me | Definitions.Def_CompetingSellers_IsStackelbergEq
-- name    : CompetingSellers_IsStackelbergEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:01.563216+00:00
-- url     : https://prove2.me/theorems/d1e02363-a9cb-4258-88ad-c4a2e7544794
-- title:
--   Stackelberg equilibrium of the induced seller game, with Bob's Alice-favourable tie-breaking
-- statement:
--   Alice's strategy is a mechanism $A$, Bob's a map $\mathcal M$ from Alice's mechanisms to his. Bob **best-responds** to $A'$ with $B$ if $\mathrm{rev}_B(A',B)\ge\mathrm{rev}_B(A',B')$ for all $B'$; his **selected best response** is one maximizing Alice's revenue among his best responses. The pair $(A,\mathcal M)$ is a **Stackelberg equilibrium** if
--
--   1. for every Alice mechanism $A'$, $\mathcal M(A')$ is a best response to $A'$ that maximizes $\mathrm{rev}_A(A',\cdot)$ among Bob's best responses, and
--   2. $\mathrm{rev}_A(A,\mathcal M(A))\ge\mathrm{rev}_A(A',\mathcal M(A'))$ for every $A'$.
--
--   The general notion (a leader, a follower answering every leader move with a best response that is most favourable to the leader, and a leader best response) is stated separately and instantiated with the sellers' revenues.
--
--   **Formalization Note** Bob's tie-breaking ("Henceforth, Bob is assumed to follow this tie-breaking rule", p.16) is part of the equilibrium condition; revenues are the buyer-tie-broken ones.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 Induced Stackelberg Equilibrium and Bob's Tie-Breaking, p.16 (PDF 19)

import Mathlib
import Definitions.Def_CompetingSellers_revenue

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- A **Stackelberg equilibrium with follower tie-breaking in the leader's favour** of a
two-player game in which the leader picks `x : X`, the follower observes it and answers by a
strategy `f : X → Y`, and the payoffs are `uL x y` (leader) and `uF x y` (follower):
(a) for every leader move `x'`, `f x'` maximizes the follower's payoff, and among the follower's
maximizers it maximizes the leader's payoff; (b) `x` maximizes `x' ↦ uL x' (f x')`. -/
def IsLeaderFavourableStackelberg {X Y : Type} (uL uF : X → Y → ℝ) (x : X) (f : X → Y) :
    Prop :=
  (∀ x', (∀ y, uF x' y ≤ uF x' (f x')) ∧
      ∀ y, (∀ y', uF x' y' ≤ uF x' y) → uL x' y ≤ uL x' (f x')) ∧
    ∀ x', uL x' (f x') ≤ uL x (f x)

variable {S : Type} [MeasurableSpace S] {null : S}

/-- `B` is a best response of Bob to Alice's `A`: `B ∈ argsup_M rev_B(A, M)` (p.16). -/
def IsBestResponse (a b : ℝ) (A B : Mech S null) : Prop :=
  ∀ B' : Mech S null, revenue a b A B' Seller.bob ≤ revenue a b A B Seller.bob

/-- `B` is the best response picked by Bob (p.16, "Bob's Tie-Breaking"): a best response that
maximizes Alice's expected revenue among Bob's best responses. -/
def IsBobChoice (a b : ℝ) (A B : Mech S null) : Prop :=
  IsBestResponse a b A B ∧
    ∀ B' : Mech S null, IsBestResponse a b A B' →
      revenue a b A B' Seller.alice ≤ revenue a b A B Seller.alice

/-- **Stackelberg equilibrium of the induced game** (§2, p.16).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19): "We say these strategies of the sellers
`(M_A, 𝓜)` form a Stackelberg equilibrium (in the induced two-agent game) if (a)
`𝓜(M′) ∈ arg sup_M rev_B(M′, M)` for all mechanisms `M′` … and (b)
`M_A ∈ arg sup_M rev_A(M, 𝓜(M))`", and ("Bob's Tie-Breaking", p.16) "we may assume that Bob
selects, after every Alice mechanism, a best response maximizing her expected revenue among his
best responses. Henceforth, Bob is assumed to follow this tie-breaking rule."

**Formalization Note.** Bob's strategy `𝓜` is an arbitrary map from Alice's mechanisms to his.
Revenues are the buyer-tie-broken revenues `revenue`. Bob's tie-breaking is part of the
definition (condition (a) holds for every `A′` with Alice-favourable tie-breaking). -/
def IsStackelbergEq (a b : ℝ) (A : Mech S null) (𝓜 : Mech S null → Mech S null) : Prop :=
  IsLeaderFavourableStackelberg (fun A' B => revenue a b A' B Seller.alice)
    (fun A' B => revenue a b A' B Seller.bob) A 𝓜

end CompetingSellers


