-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_Transportation
-- name    : BipartiteMatchingHT_Delay_Transportation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:10:59.148464+00:00
-- url     : https://prove2.me/theorems/1f01b08e-e4c6-4744-a425-096b71c38cdf
-- title:
--   Supported bipartite transportation flows
-- statement:
--   A bipartite transportation network consists of an edge relation, supplies on the left, and capacities on the right. A feasible real flow is nonnegative, zero outside the edge relation, and has row and column sums bounded by supply and capacity. Its value is total transported mass. A maximum flow attains at least every feasible flow's value. A saturated flow makes both row and column constraints equalities. These are general network definitions; no queueing, optimal-value, existence, or positivity theorem is bundled into them.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 12–14, feasible flows and (6)

import Mathlib

open scoped BigOperators

namespace BipartiteMatchingHT.Delay

/-- A capacitated bipartite transportation network, independent of any queue. -/
structure Transportation (I J : Type) where
  edge : I → J → Prop
  supply : I → ℝ
  capacity : J → ℝ

namespace Transportation
variable {I J : Type} [Fintype I] [Fintype J]

def Feasible (N : Transportation I J) (f : I → J → ℝ) : Prop :=
  (∀ i j, 0 ≤ f i j) ∧ (∀ i j, ¬ N.edge i j → f i j = 0) ∧
  (∀ i, ∑ j, f i j ≤ N.supply i) ∧ (∀ j, ∑ i, f i j ≤ N.capacity j)

noncomputable def value (f : I → J → ℝ) : ℝ := ∑ i, ∑ j, f i j

def IsMaxFlow (N : Transportation I J) (f : I → J → ℝ) : Prop :=
  N.Feasible f ∧ ∀ g, N.Feasible g → value g ≤ value f

def Saturated (N : Transportation I J) (f : I → J → ℝ) : Prop :=
  N.Feasible f ∧ (∀ i, ∑ j, f i j = N.supply i) ∧
    (∀ j, ∑ i, f i j = N.capacity j)

end Transportation
end BipartiteMatchingHT.Delay


