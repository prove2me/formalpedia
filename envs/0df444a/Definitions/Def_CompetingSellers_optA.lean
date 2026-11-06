-- Prove2me | Definitions.Def_CompetingSellers_optA
-- name    : CompetingSellers_optA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:44.801628+00:00
-- url     : https://prove2.me/theorems/3d127455-0583-47d6-9de1-a227b6a7e863
-- title:
--   Alice's optimal revenue $\mathrm{opt}_A(a;b)$ and Alice-optimal mechanisms
-- statement:
--   Let $\mathcal S$ be the set of Stackelberg equilibria. **Alice's optimal revenue** is
--   $$\mathrm{opt}_A(a;b)=\sup_{(A,\mathcal M)\in\mathcal S}\mathrm{rev}_A(A,\mathcal M(A)).$$
--   A mechanism $A$ is **optimal for Alice** if some $\mathcal M$ makes $(A,\mathcal M)$ a Stackelberg equilibrium and $\mathrm{rev}_A(A,\mathcal M(A))\ge\mathrm{rev}_A(A',\mathcal M'(A'))$ for every Stackelberg equilibrium $(A',\mathcal M')$. The equilibrium payoffs at a pair $(A,B)$ are the triple (Alice's revenue, Bob's revenue, the buyer's utility).
--
--   These are the objects of Theorem 1.1.
--
--   **Formalization Note** A real supremum over equilibria of the game with message space `S` (bounded by $\max\{a,b\}$); it would be $0$ if there were no equilibrium, which Theorem 1.1 excludes.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 Alice's Optimal Revenue, p.16 (PDF 19)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Alice's optimal revenue** `optA(a; b)` (§2 "Alice's Optimal Revenue", p.16).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19): "let `S` be the set of all Stackelberg
equilibria. We define Alice's optimal revenue as `optA(a; b) = sup_{(A,𝓜)∈S} rev_A(A, 𝓜(A))`."

**Formalization Note.** A real supremum over the Stackelberg equilibria of the game with message
space `S` and null message `null` (passed explicitly). Every revenue lies in `[0, max a b]`, so
the set is bounded; it is `0` if there were no equilibrium, which Theorem 1.1 excludes. -/
noncomputable def optA (S : Type) [MeasurableSpace S] (null : S) (a b : ℝ) : ℝ :=
  ⨆ p : {p : Mech S null × (Mech S null → Mech S null) // IsStackelbergEq a b p.1 p.2},
    revenue a b p.1.1 (p.1.2 p.1.1) Seller.alice

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **Alice-optimal mechanism** (p.16): "a mechanism `A` is optimal for Alice (with respect to
`(a, b)`) if there exists a strategy `𝓜` for Bob such that `(A, 𝓜)` is a Stackelberg equilibrium
in the induced game, and for any Stackelberg equilibrium `(A′, 𝓜′) ∈ S` it holds that
`rev_A(A, 𝓜(A)) ≥ rev_A(A′, 𝓜′(A′))`." -/
def IsAliceOptimal (a b : ℝ) (A : Mech S null) : Prop :=
  ∃ 𝓜 : Mech S null → Mech S null, IsStackelbergEq a b A 𝓜 ∧
    ∀ (A' : Mech S null) (𝓜' : Mech S null → Mech S null), IsStackelbergEq a b A' 𝓜' →
      revenue a b A' (𝓜' A') Seller.alice ≤ revenue a b A (𝓜 A) Seller.alice

/-- The payoffs of the three agents at a mechanism pair: (Alice's revenue, Bob's revenue, the
buyer's utility). -/
noncomputable def eqPayoffs (a b : ℝ) (A B : Mech S null) : ℝ × ℝ × ℝ :=
  (revenue a b A B Seller.alice, revenue a b A B Seller.bob, buyerUtil a b A B)

end CompetingSellers


