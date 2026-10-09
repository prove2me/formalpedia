-- Prove2me | Definitions.Def_CustAssort_AugGreedy_Greedy
-- name    : CustAssort_AugGreedy_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:09.463437+00:00
-- url     : https://prove2.me/theorems/966ba4ab-8de8-4506-bc8e-7d1a41406760
-- title:
--   §4.1, p. 10 — Greedy runs and exact stopping condition
-- statement:
--   Given a real-valued set function $g$, a finite product set $P$, and a cardinality limit $k$, Greedy starts with $\Delta=\varnothing$. While $|\Delta|<k$ and $P\setminus\Delta\ne\varnothing$, it adds a product $i\in P\setminus\Delta$ maximizing $g(\Delta\cup\{i\})$ among the remaining products. It returns $\Delta$ when the loop stops.
--
--   The reachability predicate includes every sequence allowed by this rule, including every tie-breaking choice. The output predicate requires both reachability and the printed stopping condition. These general definitions support the Greedy approximation theorem and every iteration of Augmented Greedy.
--
--   **Formalization Note** At $k=0$, the empty set is the output. A reached state with fewer than $k$ products is an output only if no product remains in $P\setminus\Delta$.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), §4.1, Greedy, p. 10

import Mathlib

namespace CustAssort.AugGreedy

/-- States reachable under the Greedy loop, including every possible tie-breaking (§4.1, p. 10). -/
inductive GreedyReach {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P : Finset α) (k : ℕ) : Finset α → Prop
  | nil : GreedyReach g P k ∅
  | step {Δ : Finset α} {i : α} :
      GreedyReach g P k Δ → Δ.card < k → i ∈ P \ Δ →
      (∀ i' ∈ P \ Δ, g (insert i' Δ) ≤ g (insert i Δ)) →
      GreedyReach g P k (insert i Δ)

/-- An output of Greedy is a reachable state at which the loop has stopped (§4.1, p. 10). -/
def IsGreedyOutput {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P : Finset α) (k : ℕ) (Δ : Finset α) : Prop :=
  GreedyReach g P k Δ ∧ ¬ (Δ.card < k ∧ (P \ Δ).Nonempty)

end CustAssort.AugGreedy


