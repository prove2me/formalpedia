-- Prove2me | Definitions.Def_BudgetCoreExchange_Exchange
-- name    : BudgetCoreExchange_Exchange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:23.27976+00:00
-- url     : https://prove2.me/theorems/fae9a5ec-8c2b-4f1d-8490-97e1bcc2d555
-- title:
--   Combinatorial exchange with budget-constrained buyers and the "XOR of additive groups" bid language
-- statement:
--   A **combinatorial exchange with budget-constrained buyers** consists of a finite set $I$ of buyers, a finite set $J$ of sellers and a finite set $K$ of indivisible items, together with
--
--   1. for every seller $j$, the set $K(j)\subseteq K$ of items endowed to $j$;
--   2. for every buyer $i$, a valuation $v_i$ on packages $S\subseteq K$, and for every seller $j$ a valuation (reservation price) $v_j$ on packages $Z\subseteq K$;
--   3. for every buyer $i$, a budget $B_i$.
--
--   Valuations are written in the **"XOR of additive groups"** bid language. A bid is a list of groups $(R,[(T_1,w_1),\dots,(T_r,w_r)])$, where $R$ and the $T_k$ are packages and the $w_k$ weights, and it encodes
--   $$
--   v(S)=\max\Big(0,\ \max_{(R,[(T_k,w_k)]_k):\ R\subseteq S}\ \sum_{k:\ T_k\subseteq S} w_k\Big).
--   $$
--   A plain XOR bid "$T$ for $w$" is the group $(T,[(T,w)])$. A bid is **valid** if every $T_k$ is nonempty and every $w_k\ge0$; then $v\ge0$, $v(\emptyset)=0$ and $v$ is monotone (free disposal). An exchange is valid if all budgets are nonnegative and all bids and asks are valid.
--
--   This is the model of §2 and of the program (CEx); the bid language makes valuations finite objects so that the exchange can be the input of a decision problem.
--
--   **Formalization Note** Numbers live in a scalar type `R` (reals for the economics, rationals for coded instances; `Exchange.map` converts). Endowments may overlap; the supply constraint counts units item by item. The bid language is a reading: §2 allows arbitrary valuations, and Appendix A.3 says "XOR bidding language" although its buyers $B^{\mathcal G}_j$ need two groups of this language.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, §2, pp.6–7 (bidders, items, valuations, free disposal); §3, p.8 (budgets Bᵢ); program (CEx), pp.11–12; Appendix A.3, pp.29–31 (bidding language)

import Mathlib

namespace BudgetCoreExchange

/-- A **group** of the bid language "XOR of additive groups": a required bundle `req` and a list
of weighted bundles `parts`. Coefficients live in a scalar type `R` (`ℝ` for the economics, `ℚ`
for the coded instances of the decision problem).

**Formalization Note.** This bid language is a reading, not the paper's text. Bichler–Waldherr,
arXiv:1807.08253v1, §2, pp.6–7, allow arbitrary valuations `vᵢ(S) ∈ ℝ≥0` with `vᵢ(∅) = 0` and
free disposal, and Appendix A.3, p.29, speaks of "an XOR bidding language", but the valuation of
the buyers `Bᴳⱼ` (p.31, a count of clause bundles) has no polynomial-size XOR representation. The
language below contains plain XOR bids (a bid `(T, w)` is the group `(T, [(T, w)])`) and
expresses `Bᴳⱼ` with two groups. -/
structure BidGroup (Item R : Type) where
  /-- The bundle that must be contained in the allocated package for the group to count. -/
  req : Finset Item
  /-- The weighted bundles whose weights add up when they are contained in the package. -/
  parts : List (Finset Item × R)

/-- A bid (a valuation in the "XOR of additive groups" language): a list of groups. -/
abbrev Bid (Item R : Type) : Type := List (BidGroup Item R)

/-- The value of a group for the package `S`: if `req ⊆ S`, the sum of the weights `w` of the
parts `(T, w)` with `T ⊆ S`; otherwise `0`. -/
def BidGroup.value {Item : Type} [DecidableEq Item] (g : BidGroup Item ℝ) (S : Finset Item) : ℝ :=
  if g.req ⊆ S then ((g.parts.filter fun p => decide (p.1 ⊆ S)).map fun p => p.2).sum else 0

/-- The valuation `v(S)` encoded by a bid (Bichler–Waldherr, arXiv:1807.08253v1, §2, pp.6–7):
`v(S) = max(0, max over the groups of the group's value at S)`. For a valid bid
(`Bid.Valid`: nonnegative weights, nonempty parts) it is nonnegative, monotone (free disposal)
and `v(∅) = 0`. -/
def Bid.value {Item : Type} [DecidableEq Item] (b : Bid Item ℝ) (S : Finset Item) : ℝ :=
  (b.map fun g => g.value S).foldr max 0

/-- A bid is valid if every part has a nonempty bundle and a nonnegative weight; this makes the
encoded valuation nonnegative, monotone (free disposal) and zero on `∅`, as required on pp.6–7
of arXiv:1807.08253v1. -/
def Bid.Valid {Item : Type} (b : Bid Item ℝ) : Prop :=
  ∀ g ∈ b, ∀ p ∈ g.parts, p.1.Nonempty ∧ 0 ≤ p.2

/-- A **combinatorial exchange with budget-constrained buyers** (Bichler–Waldherr,
arXiv:1807.08253v1, §2, pp.6–7, §3, p.8, and the program (CEx), pp.11–12): finite sets of buyers
`Buyer`, sellers `Seller` and indivisible items `Item` (finiteness is imposed where the
exchange is used), with
* `endow j` — the items `K(j)` endowed to seller `j` (the package a seller sells consists of the
  items endowed to him, p.12);
* `bid i` — the valuation `vᵢ` of buyer `i`;
* `ask j` — the valuation (reservation prices) `vⱼ` of seller `j`;
* `budget i` — the budget `Bᵢ` of buyer `i`.

**Formalization Note.** Valuations are given in the bid language `Bid` (see `BidGroup`).
Endowments may overlap: (Supply) counts units item by item. -/
structure Exchange (Buyer Seller Item R : Type) where
  endow : Seller → Finset Item
  bid : Buyer → Bid Item R
  ask : Seller → Bid Item R
  budget : Buyer → R

namespace Exchange

variable {Buyer Seller Item : Type}

/-- Change the scalar type of an exchange (used to read a rational instance as a real one). -/
def map {R R' : Type} (f : R → R') (E : Exchange Buyer Seller Item R) :
    Exchange Buyer Seller Item R' where
  endow := E.endow
  bid i := (E.bid i).map fun g => ⟨g.req, g.parts.map fun p => (p.1, f p.2)⟩
  ask j := (E.ask j).map fun g => ⟨g.req, g.parts.map fun p => (p.1, f p.2)⟩
  budget i := f (E.budget i)

/-- An exchange is valid if budgets are nonnegative and all bids and asks are valid (so that every
valuation is nonnegative, monotone and zero on `∅`, pp.6–7). -/
def Valid (E : Exchange Buyer Seller Item ℝ) : Prop :=
  (∀ i, 0 ≤ E.budget i) ∧ (∀ i, (E.bid i).Valid) ∧ ∀ j, (E.ask j).Valid

/-- The valuation `vᵢ(S)` of buyer `i`. -/
def bval [DecidableEq Item] (E : Exchange Buyer Seller Item ℝ) (i : Buyer) (S : Finset Item) : ℝ :=
  (E.bid i).value S

/-- The valuation `vⱼ(Z)` of seller `j`. -/
def sval [DecidableEq Item] (E : Exchange Buyer Seller Item ℝ) (j : Seller) (Z : Finset Item) : ℝ :=
  (E.ask j).value Z

end Exchange

end BudgetCoreExchange


