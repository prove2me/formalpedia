-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_Alloc
-- name    : SampleMechDesign_Supplement_Alloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:43:49.19963+00:00
-- url     : https://prove2.me/theorems/458029a7-a2a1-50e2-800f-154b3f08f688
-- title:
--   Section 2 — buyers, items, bundles, valuations and allocations of single-unit items
-- statement:
--   There are $m$ items and $n$ buyers. A **bundle** is a set $q$ of items. A **valuation vector** $v=(v_1,\dots,v_n)$ gives each buyer $j$ a value $v_j(q)\in\mathbb R$ for every bundle. An **additive** buyer has $v_j(q)=\sum_{i\in q}v_j(e_i)$, so an additive valuation vector is an array of item values $v_j(e_i)$. A profile of bundles $(q_1,\dots,q_n)$ has a production cost $c(q_1,\dots,q_n)$.
--
--   With one unit of each item, an **allocation** $Q$ assigns every item to one buyer or to nobody, so there are $(n+1)^m$ allocations, and $q_j$ is the bundle buyer $j$ receives under $Q$.
--
--   The paper never says how ties between equally good outcomes are broken. A **tie-breaking rule** is a map $\mathrm{tb}$ that, given a context (a valuation vector, a buyer, an item) and a nonempty finite set of maximizers, returns one of them.
--
--   These objects are the common setting of every mechanism class in this supplement.
--
--   **Formalization Note** `BVal n m` is `Fin n → Finset (Fin m) → ℝ`, `AVal n m` is `Fin n → Fin m → ℝ`, `Alloc n m` is `Fin m → Option (Fin n)`, and `IsChoice tb` says that `tb` returns a member of every nonempty set. Valuations are arbitrary real functions; the paper imposes nothing else.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 2, p.7 (PDF p.7)

import Mathlib

namespace SampleMechDesign.Supplement

open Finset

/-- **Allocations of `m` single-unit items to `n` buyers, and the setting of Section 2.**
Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, Section 2, p.7.

There are `m` items (`Fin m`) and `n` buyers (`Fin n`). A bundle is a set of items
(`Finset (Fin m)`); a profile of bundles `Bundles n m` gives each buyer one bundle, and a cost
function is a map `c : Bundles n m → ℝ`. A valuation vector `BVal n m` gives each buyer a value
for every bundle; an additive valuation vector `AVal n m` gives each buyer a value for every item,
and `additiveVal` turns it into the bundle valuation `v_j(q) = ∑_{i ∈ q} v_j(e_i)`. An allocation
`Alloc n m` assigns each item to one buyer or to nobody, so there are `(n + 1)^m` of them;
`Q.bundle j` is the bundle buyer `j` receives.

`IsChoice tb` says that a tie-breaking rule `tb` picks an element of every nonempty set of
maximizers it is given; the rule may depend on a context (the valuation, the buyer).

**Formalization Note.**
* The paper never fixes how ties among utility- or welfare-maximizing outcomes are broken. The
  statements of this mission take the tie-breaking rule as a parameter `tb` with `IsChoice tb` and
  quantify over it: the chosen outcome depends only on the context and on the set of maximizers.
* Single units: an allocation is a map `Fin m → Option (Fin n)`. With one unit of each item
  (item pricing, auctions) the bundles of an allocation are disjoint.
* Valuations are arbitrary real functions on bundles (the paper imposes nothing else). -/
abbrev Bundles (n m : ℕ) := Fin n → Finset (Fin m)

/-- Valuation vectors over bundles: `v j q` is buyer `j`'s value for bundle `q`
(Section 2, p.7). -/
abbrev BVal (n m : ℕ) := Fin n → Finset (Fin m) → ℝ

/-- Additive valuation vectors: `v j i` is buyer `j`'s value `v_j(e_i)` for item `i`. -/
abbrev AVal (n m : ℕ) := Fin n → Fin m → ℝ

/-- The bundle valuation of an additive buyer profile, `v_j(q) = ∑_{i ∈ q} v_j(e_i)`. -/
def additiveVal {n m : ℕ} (v : AVal n m) : BVal n m := fun j q => ∑ i ∈ q, v j i

/-- A tie-breaking rule picks a member of every nonempty set it is given. -/
def IsChoice {β α : Type*} (tb : β → Finset α → α) : Prop :=
  ∀ (b : β) (s : Finset α), s.Nonempty → tb b s ∈ s

/-- Allocations of single-unit items: each item goes to one buyer or to nobody. -/
abbrev Alloc (n m : ℕ) := Fin m → Option (Fin n)

/-- The bundle buyer `j` receives under the allocation `Q`. -/
def Alloc.bundle {n m : ℕ} (Q : Alloc n m) (j : Fin n) : Finset (Fin m) :=
  univ.filter fun i => Q i = some j

/-- The profile of bundles of an allocation. -/
def Alloc.bundles {n m : ℕ} (Q : Alloc n m) : Bundles n m := fun j => Q.bundle j

end SampleMechDesign.Supplement


