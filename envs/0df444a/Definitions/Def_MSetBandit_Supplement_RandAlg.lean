-- Prove2me | Definitions.Def_MSetBandit_Supplement_RandAlg
-- name    : MSetBandit_Supplement_RandAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:45:33.612782+00:00
-- url     : https://prove2.me/theorems/4da27a71-61c1-4ce9-91b8-7dc1f464881e
-- title:
--   Randomized algorithm on $\mathcal X_{d,m}$: $X_t=h_t(H_{t-1},\Upsilon)$
-- statement:
--   A **randomized algorithm** on the action set $\mathcal X_{d,m}$ is described by a measurable space $\Omega$ carrying its private randomness $\Upsilon$, sampled once before the interaction, and deterministic decision rules $h_t$: at round $t$ the algorithm plays
--   $$
--   X_t=h_t(H_{t-1},\Upsilon),
--   $$
--   where $H_{t-1}$ is the history of past actions and scalar feedback. For each round and each history the map $\omega\mapsto h_t(H_{t-1},\omega)$ is measurable. The law of $\Upsilon$ (a probability measure on $\Omega$) is supplied separately.
--
--   Sampling the randomness in advance is equivalent to generating fresh randomness at every round, so this form covers every randomized bandit algorithm; it is the model over which the paper's lower bounds quantify.
--
--   **Formalization Note** Rounds are indexed from $0$. Measurability of the decision rules is the standing convention that makes the events of the interaction measurable.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix E, p.41 (private randomness $\Upsilon$, $X_t=h_t(H_{t-1},\Upsilon)$)

import Mathlib
import Definitions.Def_MSetBandit_Supplement_History
open MeasureTheory

namespace MSetBandit.Supplement

/-- **Randomized algorithm on `X_{d,m}` (private-randomness form).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix E, p.41:
"let `Υ` collect the algorithm's private randomness … sampled … before the interaction begins.
This is equivalent to generating fresh randomness at each round … We can then write the
algorithm's chosen action at time `t ∈ [T]` as `X_t = h_t(H_{t−1}, Υ)` … where `h_t` … are
deterministic functions."

A `RandAlg d m Ω` is, for each round `t` and each history `H` of length `t`, a decision rule
`h t H : Ω → Action d m` mapping the realization of the private randomness to the action played.
The law of `Υ` is a probability measure on `Ω` supplied separately in each theorem.

**Formalization Note.** Rounds are 0-based: the action of round `t` depends on the history of
the first `t` rounds. Each decision rule is required to be measurable in the randomness (the
standing convention that makes the events of the interaction measurable). -/
structure RandAlg (d m : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- the decision rule `h_t(H_{t−1}, ·)` -/
  h : (t : ℕ) → History d m t → Ω → Action d m
  /-- each decision rule is measurable in the private randomness -/
  measurable_h : ∀ t (H : History d m t), Measurable (h t H)

end MSetBandit.Supplement


