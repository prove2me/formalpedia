-- Prove2me | Definitions.Def_SuttonTD_Convergence_ExpectedVisits
-- name    : SuttonTD_Convergence_ExpectedVisits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:31.43399+00:00
-- url     : https://prove2.me/theorems/44a2a644-ee7c-45d1-811d-2dbafc64d026
-- title:
--   $d_i$: expected number of visits to state $i$ in one sequence
-- statement:
--   For an absorbing Markov chain started from the distribution $\mu$, let $d_i$ be **the expected number of times the chain is in the nonterminal state $i$ in one sequence**:
--
--   $$d_i=\sum_{s,\,j}\Pr(s,j)\cdot\#\{t: s_t=i\},$$
--
--   the sum running over all finite lists $s$ of nonterminal states and all terminal states $j$, with $\Pr(s,j)$ the probability of the sequence (see `EpisodeModel`). The diagonal matrix $D=\operatorname{diag}(d)$ enters the mean dynamics of linear TD(0).
--
--   **Formalization Note** The sum is an unconditional sum (`tsum`) over the countable type of (list, terminal state) pairs. Its convergence and its value $[\mu^\top(I-Q)^{-1}]_i$ are the content of the milestone for equation (7), not of this definition.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, p. 25 (PDF p. 17)

import Definitions.Def_SuttonTD_Convergence_EpisodeModel

namespace SuttonTD.Convergence

namespace AbsorbingChain

variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

/-- `d_i`, "the expected number of times the Markov chain is in state `i` in one sequence"
(Sutton 1988, §4.1, p. 25, PDF p. 17): the sum, over all finite sequences
`(s_1, …, s_m)` of nonterminal states and terminal states `j`, of the probability
`pathWeight C μ s j` of that sequence times the number of occurrences of `i` in `s`.

Formalization Note: the sum is a `tsum` over the countable type `List N × T`; it is the
expectation of the visit count under the episode law of `IsEpisodeStream`. The statement that the
family is summable with sum `[μᵀ(I − Q)⁻¹]_i` is the milestone `expected_visits_eq` ((7) of
the paper), not part of this definition. -/
noncomputable def expectedVisits (C : AbsorbingChain N T) (μ : N → ℝ) (i : N) : ℝ :=
  ∑' p : List N × T, C.pathWeight μ p.1 p.2 * (p.1.count i : ℝ)

end AbsorbingChain

end SuttonTD.Convergence


