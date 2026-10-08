-- Prove2me | Definitions.Def_TalagrandExpectationThreshold
-- name    : TalagrandExpectationThreshold
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.933957+00:00
-- url     : https://prove2.me/theorems/f4892531-162c-456c-b93d-b022f10c67cc
-- statement:
--   For a finite type α, a family is a finite set of subsets of α. For p∈ℝ, the cost of a family G is the sum over S∈G of p^|S|. G covers F when every H∈F contains some S∈G as a subset. F is Small at p if some family G covers F and has cost at most 1/2. For a real-valued weight g on subsets of α, fracCost(p,g) is the sum over all subsets S of g(S)·p^|S|. A FractionalCover of F is a weight g with 0≤g(S)≤1 for every S such that every H∈F has total weight at least 1 over the subsets of H, that is, the sum of g(S) over S⊆H is at least 1. F is FractionalSmall at p if some fractional cover g of F has fracCost(p,g)≤1/2. A family F is Increasing if every superset of a member of F is also in F. The integral feasible set of F is the set of p with 0≤p≤1 for which F is Small at p, and the fractional feasible set is the set of p with 0≤p≤1 for which F is FractionalSmall at p. Finally q(F) is the supremum (sSup in the reals) of the integral feasible set and qf(F) is the supremum of the fractional feasible set. These are definitions only, with no theorem relating q and qf asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TalagrandExpectationThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TalagrandExpectationThreshold.lean; bytes 269..1516
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

abbrev Family (α : Type*) := Finset (Finset α)

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

def cost (p : ℝ) (G : Family α) : ℝ := ∑ S ∈ G, p ^ S.card

def Covers (G F : Family α) : Prop := ∀ H ∈ F, ∃ S ∈ G, S ⊆ H

def Small (p : ℝ) (F : Family α) : Prop :=
  ∃ G : Family α, Covers G F ∧ cost p G ≤ 1 / 2

def fracCost (p : ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ S : Finset α, g S * p ^ S.card

def FractionalCover (F : Family α) (g : Finset α → ℝ) : Prop :=
  (∀ S, 0 ≤ g S ∧ g S ≤ 1) ∧
    ∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, g S

def FractionalSmall (p : ℝ) (F : Family α) : Prop :=
  ∃ g : Finset α → ℝ, FractionalCover F g ∧ fracCost p g ≤ 1 / 2

def Increasing (F : Family α) : Prop :=
  ∀ H ∈ F, ∀ K : Finset α, H ⊆ K → K ∈ F

def integralFeasible (F : Family α) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ Small p F}

def fractionalFeasible (F : Family α) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ FractionalSmall p F}

def q (F : Family α) : ℝ := sSup (integralFeasible F)

def qf (F : Family α) : ℝ := sSup (fractionalFeasible F)

end



end TalagrandThreshold
end OAI


