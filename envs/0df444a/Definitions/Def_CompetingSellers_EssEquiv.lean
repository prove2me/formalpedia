-- Prove2me | Definitions.Def_CompetingSellers_EssEquiv
-- name    : CompetingSellers_EssEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:58.162792+00:00
-- url     : https://prove2.me/theorems/e1b382bb-9da4-4731-af5c-87b6615b0ade
-- title:
--   Essential equivalence of two mechanisms of the same seller
-- statement:
--   Two mechanisms $M_i,M_i'$ of seller $i$ are **essentially equivalent** if, against every mechanism $M_{-i}$ of the other seller, they induce the same expected utility for the buyer, the same expected revenue for each seller, the same interaction order, the same allocation probability from the first seller, and the same conditional allocation probability from the second seller on each branch reached with positive probability (after winning, respectively losing, the first good).
--
--   Uniqueness statements of the paper are up to this equivalence (footnote 3); Proposition 3.20 item 3 uses it.
--
--   **Formalization Note** The comparison is made between all selected plans of the two mechanism pairs; the winning branch is reached iff the first allocation probability is positive, the losing branch iff it is below $1$.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 2.1, p.17 (PDF 20)

import Mathlib
import Definitions.Def_CompetingSellers_revenue

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

variable {S : Type} [MeasurableSpace S] {null : S}

/-- The pairs `(A, B)` and `(A', B')` induce the same buyer utility, the same revenue for each
seller, and, for any selected plans of the two pairs, the same interaction order, the same
first-seller allocation probability and the same conditional second-seller allocation probability
on each branch reached with positive probability. -/
def SameOutcome (a b : ℝ) (A B A' B' : Mech S null) : Prop :=
  buyerUtil a b A B = buyerUtil a b A' B' ∧
    revenue a b A B Seller.alice = revenue a b A' B' Seller.alice ∧
    revenue a b A B Seller.bob = revenue a b A' B' Seller.bob ∧
    ∀ π ∈ selectedPlans a b A B, ∀ π' ∈ selectedPlans a b A' B',
      π.first = π'.first ∧ π.firstAlloc A B = π'.firstAlloc A' B' ∧
        (0 < π.firstAlloc A B → π.allocW A B = π'.allocW A' B') ∧
        (π.firstAlloc A B < 1 → π.allocL A B = π'.allocL A' B')

/-- **Essential equivalence** (Definition 2.1, p.17).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 2.1, p.17 (PDF 20): "Fix a seller `i ∈ {A, B}`. Two
mechanisms `M_i` and `M′_i` offered by seller `i` are essentially equivalent if, for every
mechanism `M_{−i}` offered by the other seller, they induce the same expected utility for the
buyer, the same expected revenue for each seller, and the same interaction order under the stated
buyer tie-breaking rules. They must also induce the same allocation probability from the first
seller and the same conditional allocation probability from the second seller on each branch
reached with positive probability, according to whether the buyer receives the first seller's
good."

**Formalization Note.** Order and allocations are compared across all selected plans of the two
pairs (Observation A.5 shows the selected plans of one pair agree on them); the win branch is
reached iff the first allocation is positive, the lose branch iff it is below `1`. -/
def EssEquiv (a b : ℝ) (i : Seller) (M M' : Mech S null) : Prop :=
  match i with
  | .alice => ∀ B : Mech S null, SameOutcome a b M B M' B
  | .bob => ∀ A : Mech S null, SameOutcome a b A M A M'

end CompetingSellers


