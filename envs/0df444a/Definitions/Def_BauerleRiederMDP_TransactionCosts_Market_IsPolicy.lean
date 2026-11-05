-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_IsPolicy
-- name    : BauerleRiederMDP_TransactionCosts_Market_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:34.986344+00:00
-- url     : https://prove2.me/theorems/555693d9-3659-42a2-94c2-54d9c292f7c5
-- title:
--   Markov policies from time $n$
-- statement:
--   A Markov policy from time $n$ is a sequence $\pi=(f_n,\dots,f_{N-1})$ of decision rules. It is encoded as a sequence indexed by $\mathbb N$ of which only the entries $n\le k<N$ are constrained or used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5 b), p.16 (PDF 31)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IsDecisionRule

namespace BauerleRiederMDP.TransactionCosts

/-- A Markov policy from time `n` (Bäuerle & Rieder 2011, Definition 2.1.5 b), p.16, PDF 31):
`π = (f_n, …, f_{N−1})` with every `f_k` a decision rule of the transaction cost model. The
policy is a sequence `π : ℕ → (ℝ × ℝ → ℝ × ℝ)`, of which only the entries `n ≤ k < N` are
constrained or used. -/
def Market.IsPolicy {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (π : ℕ → ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → IsDecisionRule M.c (π k)

end BauerleRiederMDP.TransactionCosts


