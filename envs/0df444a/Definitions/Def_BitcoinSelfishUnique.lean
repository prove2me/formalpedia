-- Prove2me | Definitions.Def_BitcoinSelfishUnique
-- name    : BitcoinSelfishUnique
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T17:07:38.220482+00:00
-- url     : https://prove2.me/theorems/bac117d1-1233-4fd1-a881-a04520a4ede4
-- title:
--   Stationary distributions of the selfish-mining chain
-- statement:
--   One predicate over the selfish-mining mission's chain.
--
--   **`IsStationary α γ π`** — a function $\pi$ from states to reals is a stationary distribution of the chain with parameters $\alpha, \gamma$: it is nonnegative on every state; its values on the lead states $\pi(\text{lead } n)$ form a summable sequence; its total mass `stateSum π` $= \pi(\text{zero}) + \pi(\text{tie}) + \sum'_n \pi(\text{lead } n)$ is 1; and it is invariant under one step: for every state $s$, $\pi(s) = $ `stateSum (fun t => π t * P α γ t s)`, the inflow into $s$ from all states weighted by the one-step transition probabilities.
--
--   **Formalization Note.** Imports Mathlib and the selfish-mining mission's definitions. The selfish-mining mission proved that its `stationary α` satisfies the balance equations and has mass 1; this mission is about every $\pi$ satisfying them.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)

import Definitions.Def_BitcoinSelfishMining

/-!
# Selfish mining: stationary distributions of the Eyal–Sirer chain

This file defines what it means for a function `π : State → ℝ` to be a stationary distribution of
the selfish-mining chain of `Definitions/Def_BitcoinSelfishMining.lean`: it is nonnegative, its
values on the leads form a summable family (so that `stateSum π` is a genuine sum), it has total
mass one and it is invariant under one step of the chain, `π s = Σ_t π t · P(t → s)` for every
state `s` (the sum running over all states via `stateSum`).

The paper's distribution `stationary α` is one such distribution (`stationary_balance`,
`total_mass` in the solutions of `BitcoinSelfishMining`); the theorems in
`Solutions/Sol_BitcoinSelfishUnique_all.lean` show that for `0 < α < 1/2` it is the only one.
-/

namespace BitcoinSelfishUnique

/-- A stationary distribution of the selfish-mining chain: nonnegative, summable over the leads,
total mass one, invariant under one step. -/
structure IsStationary (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ π s
  summable : Summable (fun n : ℕ => π (.lead n))
  mass : BitcoinSelfishMining.stateSum π = 1
  invariant : ∀ s, π s = BitcoinSelfishMining.stateSum (fun t => π t * BitcoinSelfishMining.P α γ t s)

end BitcoinSelfishUnique


