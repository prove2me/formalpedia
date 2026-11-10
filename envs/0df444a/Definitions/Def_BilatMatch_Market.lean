-- Prove2me | Definitions.Def_BilatMatch_Market
-- name    : BilatMatch_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:14.051243+00:00
-- url     : https://prove2.me/theorems/0e682c1b-0acc-4d51-960f-2206cf4256c2
-- title:
--   Matching market $\mathcal I=(G,\mathcal F,(F_{B_i}),(F_{S_j}))$ with countable agent sets
-- statement:
--   A **matching market** $\mathcal I$ consists of a bipartite compatibility graph $G=(B,S,E)$ with buyer set $B$, seller set $S$ and edge set $E\subseteq B\times S$, a family $\mathcal F$ of feasible matchings of $G$, and for each buyer $i\in B$ a value prior $F_{B_i}$ and for each seller $j\in S$ a cost prior $F_{S_j}$ on $\mathbb R$.
--
--   The market is **valid** when
--
--   1. every $M\in\mathcal F$ is a matching contained in $E$ (no agent lies on two edges of $M$);
--   2. $\mathcal F$ is nonempty and downward closed (deleting trades preserves feasibility);
--   3. every prior is a Borel probability measure on $\mathbb R$.
--
--   Nothing else is assumed: types may be negative, unbounded, without mean, atomic or continuous. Types are mutually independent: the type profile $\theta=(v,c)\in\mathbb R^B\times\mathbb R^S$ has the product law $\bigotimes_i F_{B_i}\otimes\bigotimes_j F_{S_j}$. The module also defines the profile with one agent's report replaced, and the gains $\sum_{(i,j)\in M}(v_i-c_j)$ of a finite set of edges.
--
--   **Formalization Note** $B$ and $S$ are arbitrary types; theorems add `[Countable B] [Countable S]` (finite included) or `[Fintype B] [Fintype S]`. The product law is Mathlib's `Measure.infinitePi`, which needs no finiteness of the index set.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §2 Market Model and Benchmarks, p.5 (pdf p.7)

import Mathlib

open MeasureTheory

namespace BilatMatch

/-!
# Matching markets with countably many agents

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §2 "Market Model and Benchmarks", p.5 (pdf p.7).

**Formalization Note**
* The buyer set `B` and seller set `S` are arbitrary types; the theorems put `[Countable B]
  [Countable S]` (finite included) where the paper says "countable", and `[Fintype B] [Fintype S]`
  where it says "finitely many agents".
* Edges and matchings are `Set (B × S)` (possibly infinite), the family `F` is a `Set` of them.
* The priors are arbitrary Borel probability measures on `ℝ`: no sign, no moment, no density.
* Mutual independence of all types is the product law `typeMeasure` (Mathlib's
  `Measure.infinitePi`, which needs no finiteness of the index type).
-/

variable {B S : Type*}

/-- `M` is a matching of the bipartite graph with edge set `E`: `M ⊆ E` and no buyer and no seller
lies on two different edges of `M`. -/
def IsMatching (E M : Set (B × S)) : Prop :=
  M ⊆ E ∧ ∀ e ∈ M, ∀ e' ∈ M, (e.1 = e'.1 ∨ e.2 = e'.2) → e = e'

/-- A matching market `I = (G = (B, S, E), F, (F_{B_i}), (F_{S_j}))` (p.5): the compatibility
edges `E ⊆ B × S`, the family `F` of feasible matchings, buyer `i`'s value prior `F_{B_i}` and
seller `j`'s cost prior `F_{S_j}`. Its standing assumptions are `Market.IsValid`. -/
structure Market (B S : Type*) where
  /-- the compatibility edges `E` -/
  edges : Set (B × S)
  /-- the family `F` of feasible matchings -/
  family : Set (Set (B × S))
  /-- buyer `i`'s value prior `F_{B_i}` -/
  buyerLaw : B → Measure ℝ
  /-- seller `j`'s cost prior `F_{S_j}` -/
  sellerLaw : S → Measure ℝ

/-- The standing assumptions of §2 (p.5): `F` is a nonempty downward-closed family of matchings of
`G`, and every prior is a (Borel) probability measure on `ℝ`. Nothing else is assumed. -/
structure Market.IsValid (I : Market B S) : Prop where
  family_matching : ∀ M ∈ I.family, IsMatching I.edges M
  family_nonempty : I.family.Nonempty
  family_downward : ∀ M ∈ I.family, ∀ M' : Set (B × S), M' ⊆ M → M' ∈ I.family
  buyerLaw_prob : ∀ i, IsProbabilityMeasure (I.buyerLaw i)
  sellerLaw_prob : ∀ j, IsProbabilityMeasure (I.sellerLaw j)

/-- A type (or report) profile `θ = (v, c)`: buyer values `v : B → ℝ`, seller costs `c : S → ℝ`. -/
abbrev Profile (B S : Type*) := (B → ℝ) × (S → ℝ)

/-- The law of the whole type profile: all values and costs mutually independent (p.5). -/
noncomputable def typeMeasure (I : Market B S) : Measure (Profile B S) :=
  (Measure.infinitePi I.buyerLaw).prod (Measure.infinitePi I.sellerLaw)

open Classical in
/-- The profile `θ` with buyer `i`'s report replaced by `r`. -/
noncomputable def updateBuyer (θ : Profile B S) (i : B) (r : ℝ) : Profile B S :=
  (Function.update θ.1 i r, θ.2)

open Classical in
/-- The profile `θ` with seller `j`'s report replaced by `r`. -/
noncomputable def updateSeller (θ : Profile B S) (j : S) (r : ℝ) : Profile B S :=
  (θ.1, Function.update θ.2 j r)

/-- The gains from trade of a set of edges `M` at a profile, `∑_{(i,j) ∈ M} (v_i − c_j)`, as a
`finsum` (meaningful for finite `M`). -/
noncomputable def matchingGFT (M : Set (B × S)) (θ : Profile B S) : ℝ :=
  ∑ᶠ e ∈ M, (θ.1 e.1 - θ.2 e.2)

end BilatMatch


