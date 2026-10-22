-- Prove2me | Definitions.Def_TBSGStrategyIteration_value
-- name    : TBSGStrategyIteration_value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:05:23.613481+00:00
-- url     : https://prove2.me/theorems/eed22ac7-6947-44ae-99c1-41445428980b
-- title:
--   Value vector $v_\pi$ of a strategy profile (Definition 2.5)
-- statement:
--   For a strategy profile $\pi$ the play is a Markov chain on $S$ with transition matrix $P_\pi$, and $(P_\pi^k)_{i,j}$ is the probability of being at $j$ after exactly $k$ steps from $i$. The **value vector** $v_\pi \in \mathbb{R}^n$ records, for every initial state $i$, the expected total discounted cost:
--   $$v_\pi = \sum_{k \ge 0} \gamma^k P_\pi^k \, c_\pi .$$
--   More generally, for any cost vector $d \in \mathbb{R}^m$ on the actions, $\mathrm{valueWith}(d, \pi) = \sum_{k\ge 0} \gamma^k P_\pi^k d_\pi$ with $(d_\pi)_i = d(\pi(i))$; the value vector is the case $d = c$.
--
--   **Formalization Note.** The series is a `tsum` in $\mathbb{R}^S$. It is always summable here ($P_\pi^k$ is row stochastic, so the $k$-th term has sup norm at most $\gamma^k \max_a |d(a)|$ with $0 < \gamma < 1$), so the junk value of a non-summable `tsum` never arises. The general cost vector is used for the modified values (Definition 3.5) and the flux vectors (Definition 3.8).
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 3, Definition 2.5 (the Markov-chain form is the one used in the proof of Lemma 3.2, p. 4)

import Mathlib
import Definitions.Def_TBSGStrategyIteration_Profile

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- The value vector of the profile `π` for an arbitrary cost vector `d : A → ℝ`:
the expected total discounted cost `∑_{k ≥ 0} γ^k P_π^k d_π`, where `(P_π^k)_{i,j}` is the
probability that the Markov chain of `π` started at `i` is at `j` after exactly `k` steps
and `(d_π)_i = d(π(i))`. (The series converges absolutely since `P_π` is row stochastic and
`0 < γ < 1`.) Used with `d = c` (Def. 2.5), with the modified costs (Def. 3.5) and with the
unit costs of Def. 3.8. -/
noncomputable def valueWith (G : Game S A) (d : A → ℝ) (π : Profile G) : S → ℝ :=
  ∑' k : ℕ, G.γ ^ k • (π.transMat ^ k).mulVec (fun i => d (π.act i))

/-- Def. 2.5: the value vector `v_π ∈ ℝ^n`; `(v_π)_i` is the expected total discounted cost
when the game starts at state `i` and the players use the strategy profile `π`. -/
noncomputable def value (G : Game S A) (π : Profile G) : S → ℝ :=
  valueWith G G.c π

end TBSGStrategyIteration


