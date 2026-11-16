-- Prove2me | Definitions.Def_CompetingSellers_Supplement_IsStackelbergEqFrom
-- name    : CompetingSellers_Supplement_IsStackelbergEqFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:32:05.91659+00:00
-- url     : https://prove2.me/theorems/9e1f366d-6e4d-4ce4-9f54-82c32ad1a9b3
-- title:
--   Stackelberg equilibria, best responses, $\mathrm{opt}^{AB}_A$ / $\mathrm{opt}^{BA}_A$ and payoff triples in the fixed-order (aligned / misaligned) models
-- statement:
--   In the **aligned model** (§4) Alice commits to a mechanism, Bob responds, and the buyer must visit Alice first; in the **misaligned model** (§5) the timing is the same but the buyer must visit Bob first. Write $i\in\{A,B\}$ for the seller the buyer must visit first and $\mathrm{rev}^{(i)}_j(A,B)$ for seller $j$'s expected revenue when the buyer, restricted to plans approaching $i$ first, maximizes his expected utility and breaks ties by Bob's revenue, then Alice's, then Bob's and Alice's allocation probabilities ($\mathrm{rev}^{AB}_j$ and $\mathrm{rev}^{BA}_j$ in the paper).
--
--   1. $B$ is a **best response** of Bob to $A$ if $\mathrm{rev}^{(i)}_B(A,B')\le\mathrm{rev}^{(i)}_B(A,B)$ for every mechanism $B'$.
--   2. A pair $(A,\mathcal M)$, with $\mathcal M$ a map from Alice's mechanisms to Bob's, is a **Stackelberg equilibrium** if for every $A'$ the mechanism $\mathcal M(A')$ is a best response to $A'$ that maximizes Alice's revenue among Bob's best responses, and $A$ maximizes $A'\mapsto\mathrm{rev}^{(i)}_A(A',\mathcal M(A'))$.
--   3. Alice's **optimal revenue** is $\mathrm{opt}^{(i)}_A(a;b)=\sup_{(A,\mathcal M)}\mathrm{rev}^{(i)}_A(A,\mathcal M(A))$ over Stackelberg equilibria, and $A$ is **Alice-optimal** if some $(A,\mathcal M)$ is a Stackelberg equilibrium whose Alice revenue is at least that of every Stackelberg equilibrium.
--   4. The **payoff triple** of $(A,B)$ is (Alice's revenue, Bob's revenue, the buyer's maximum expected utility over plans visiting $i$ first).
--
--   These are the paper's §2 notions with the buyer's order prescribed; they are the objects of Theorems 1.3 and 1.4.
--
--   **Formalization Note** The fixed-order revenues and buyer plans are the published `revenueFrom`, `selectedPlansFrom` and `orderUtil` of the base mission, and the equilibrium is the published `IsLeaderFavourableStackelberg`. The optimal revenue is a real supremum over the equilibria; revenues are bounded, and the value would be $0$ if there were no equilibrium (Theorem 1.3 asserts existence).
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 p.16 (PDF 19); §4 p.31 (PDF 34) (rev^AB, opt^AB_A); §5 p.38 (PDF 41) (rev^BA, opt^BA_A); Observation A.2 p.50 (PDF 53)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers.Supplement

variable {S : Type} [MeasurableSpace S] {null : S}

/-- `B` is a best response of Bob to Alice's `A` in the fixed-order model where the buyer must
approach seller `i` first (`i = alice`: the aligned model, §4, p.31; `i = bob`: the misaligned
model, §5, p.38): `B ∈ argsup_M rev^{order}_B(A, M)`.
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19), with the revenues `rev^{AB}_i`, `rev^{BA}_i`
of pp.31, 38 (PDF 34, 41).

**Formalization Note.** The main-model `IsBestResponse` with `revenue` replaced by `revenueFrom`
(the buyer's plans restricted to the prescribed order, Observation A.2, p.50). -/
def IsBestResponseFrom (a b : ℝ) (i : Seller) (A B : Mech S null) : Prop :=
  ∀ B' : Mech S null, revenueFrom a b i A B' Seller.bob ≤ revenueFrom a b i A B Seller.bob

/-- **Stackelberg equilibrium of a fixed-order model** (§2, p.16, applied to the aligned model of
§4, p.31 and the misaligned model of §5, p.38).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19): "(a) `𝓜(M′) ∈ arg sup_M rev_B(M′, M)` for all
mechanisms `M′` … and (b) `M_A ∈ arg sup_M rev_A(M, 𝓜(M))`", with Bob selecting "a best response
maximizing her expected revenue among his best responses"; p.31 (PDF 34): "let `rev^{AB}_i(A, B)`
denote seller `i`'s revenue under the buyer's prescribed tie-breaking rules and when the buyer is
forced to visit Alice first"; p.38 (PDF 41): "`rev^{BA}_i(A, B)` for seller `i`'s expected revenue
under the prescribed order BA".

**Formalization Note.** `i` is the seller the buyer must visit first (`alice`: aligned,
`bob`: misaligned). The definition is the published `IsStackelbergEq` with the fixed-order revenues
`revenueFrom a b i`; Bob's Alice-favourable tie-breaking is part of it (Observation A.2 covers the
fixed orders). -/
def IsStackelbergEqFrom (a b : ℝ) (i : Seller) (A : Mech S null)
    (𝓜 : Mech S null → Mech S null) : Prop :=
  IsLeaderFavourableStackelberg (fun A' B => revenueFrom a b i A' B Seller.alice)
    (fun A' B => revenueFrom a b i A' B Seller.bob) A 𝓜

/-- **Alice's optimal revenue in a fixed-order model**: `opt^{AB}_A(a; b)` for `i = alice`
(p.31, PDF 34: "the supremum of Alice's expected revenue over Stackelberg equilibria when a buyer
with values `a, b > 0` is forced to visit Alice first") and `opt^{BA}_A(a; b)` for `i = bob`
(p.38, PDF 41).

**Formalization Note.** A real supremum over the fixed-order Stackelberg equilibria; revenues lie
in `[0, max a b]`, so the set is bounded; the value would be `0` if there were no equilibrium. -/
noncomputable def optAFrom (S : Type) [MeasurableSpace S] (null : S) (a b : ℝ) (i : Seller) : ℝ :=
  ⨆ p : {p : Mech S null × (Mech S null → Mech S null) // IsStackelbergEqFrom a b i p.1 p.2},
    revenueFrom a b i p.1.1 (p.1.2 p.1.1) Seller.alice

/-- **Alice-optimal mechanism in a fixed-order model** (p.16's definition with the order fixed):
there is a strategy `𝓜` of Bob with `(A, 𝓜)` a Stackelberg equilibrium, and for every Stackelberg
equilibrium `(A′, 𝓜′)` of the same model, `rev_A(A, 𝓜(A)) ≥ rev_A(A′, 𝓜′(A′))`. -/
def IsAliceOptimalFrom (a b : ℝ) (i : Seller) (A : Mech S null) : Prop :=
  ∃ 𝓜 : Mech S null → Mech S null, IsStackelbergEqFrom a b i A 𝓜 ∧
    ∀ (A' : Mech S null) (𝓜' : Mech S null → Mech S null), IsStackelbergEqFrom a b i A' 𝓜' →
      revenueFrom a b i A' (𝓜' A') Seller.alice ≤ revenueFrom a b i A (𝓜 A) Seller.alice

/-- The payoff triple at a mechanism pair in the fixed-order model with first seller `i`:
(Alice's expected revenue, Bob's expected revenue, the buyer's expected utility), the utility being
the buyer's maximum utility over plans approaching `i` first (`util_{AB}` / `util_{BA}`). -/
noncomputable def eqPayoffsFrom (a b : ℝ) (i : Seller) (A B : Mech S null) : ℝ × ℝ × ℝ :=
  (revenueFrom a b i A B Seller.alice, revenueFrom a b i A B Seller.bob, orderUtil a b A B i)

end CompetingSellers.Supplement


