-- Prove2me | Definitions.Def_SupplyRevenue_Demand
-- name    : SupplyRevenue_Demand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:41.189742+00:00
-- url     : https://prove2.me/theorems/071c449f-dfc7-44a4-9d36-a02b887944b1
-- title:
--   Values, offers and tie-ruled demand
-- statement:
--   Items are $M=[m]$ and bundles are subsets of $M$. A **value** is a function $v$ on bundles with $v(\emptyset)=0$ that is monotone. An **offer** consists of an assortment $A\subseteq M$ and prices $p\ge 0$.
--
--   The **residual order** is a fixed injective rank on bundles. Given a stock $S\subseteq M$, a buyer's **demand** is the bundle $Q\subseteq A\cap S$ that maximizes, lexicographically,
--
--   $$\bigl(v(Q)-p(Q),\ p(Q),\ \mathrm{rank}(Q)\bigr).$$
--
--   Empty demand is allowed, and the maximizer is unique because the rank is injective. Full-stock demand is the case $S=M$. Every benchmark of the mission uses this demand.
--
--   **Formalization Note** The rank is a parameter `tie`, and all benchmarks of a statement share one. A larger rank wins; the direction is immaterial because the rank is arbitrary.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2

import Mathlib

namespace SupplyRevenue

/-!
# Valuations, offers and tie-ruled demand

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "Values are normalized and monotone"; "Demand maximizes utility v(Q) − p(Q), then payment, then a fixed
residual bundle order, allowing empty demand. Type-independent offers comprise p ≥ 0 and assortments".

**Formalization Note** Items are `Fin m`, bundles `Finset (Fin m)`. The residual bundle order is any injective rank
`tie : Finset (Fin m) ↪ ℕ`, and one rank is shared by all benchmarks of a statement (reading R3). Larger rank wins; the
direction is immaterial because the rank is arbitrary. The price of an item outside the assortment is never read.
Demand is the unique maximizer of the lexicographic triple over `Q ⊆ A ∩ S`, with `A` the assortment and `S` the stock.
Full-stock demand takes `S = Finset.univ`.
-/

/-- A value function is normalized and monotone (§1.1, p.2). -/
structure IsValuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop where
  empty : v ∅ = 0
  mono : Monotone v

/-- A type-independent offer: an assortment and nonnegative item prices (§1.1, p.2). -/
structure Offer (m : ℕ) where
  assort : Finset (Fin m)
  price : Fin m → ℝ
  price_nonneg : ∀ j, 0 ≤ price j

/-- The payment `p(Q)` of a bundle at the prices of an offer. -/
noncomputable def Offer.pay {m : ℕ} (o : Offer m) (Q : Finset (Fin m)) : ℝ := ∑ j ∈ Q, o.price j

/-- The empty offer: nothing is on sale. -/
def Offer.empty (m : ℕ) : Offer m where
  assort := ∅
  price := fun _ => 0
  price_nonneg := fun _ => le_rfl

/-- A fixed residual bundle order, encoded as an injective rank on bundles (reading R3). -/
abbrev Tie (m : ℕ) := Finset (Fin m) ↪ ℕ

/-- The lexicographic score `(v(Q) − p(Q), p(Q), tie Q)` of a bundle: utility, then payment, then the residual order. -/
noncomputable def demandScore {m : ℕ} (tie : Tie m) (v : Finset (Fin m) → ℝ) (o : Offer m)
    (Q : Finset (Fin m)) : ℝ ×ₗ ℝ ×ₗ ℕ :=
  toLex (v Q - o.pay Q, toLex (o.pay Q, tie Q))

theorem exists_demand {m : ℕ} (tie : Tie m) (v : Finset (Fin m) → ℝ) (o : Offer m)
    (S : Finset (Fin m)) :
    ∃ Q ∈ (o.assort ∩ S).powerset, ∀ Q' ∈ (o.assort ∩ S).powerset,
      demandScore tie v o Q' ≤ demandScore tie v o Q :=
  Finset.exists_max_image _ _ ⟨∅, Finset.empty_mem_powerset _⟩

/-- Tie-ruled demand of value `v` at offer `o` with stock `S`: the maximizer over `Q ⊆ A ∩ S` of the lexicographic
triple. Empty demand is allowed. -/
noncomputable def demand {m : ℕ} (tie : Tie m) (v : Finset (Fin m) → ℝ) (o : Offer m)
    (S : Finset (Fin m)) : Finset (Fin m) :=
  Classical.choose (exists_demand tie v o S)

theorem demand_subset {m : ℕ} (tie : Tie m) (v : Finset (Fin m) → ℝ) (o : Offer m)
    (S : Finset (Fin m)) : demand tie v o S ⊆ o.assort ∩ S :=
  Finset.mem_powerset.mp (Classical.choose_spec (exists_demand tie v o S)).1

theorem demand_max {m : ℕ} (tie : Tie m) (v : Finset (Fin m) → ℝ) (o : Offer m)
    (S Q : Finset (Fin m)) (hQ : Q ⊆ o.assort ∩ S) :
    demandScore tie v o Q ≤ demandScore tie v o (demand tie v o S) :=
  (Classical.choose_spec (exists_demand tie v o S)).2 Q (Finset.mem_powerset.mpr hQ)

end SupplyRevenue


