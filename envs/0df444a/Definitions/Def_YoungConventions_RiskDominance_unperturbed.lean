-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_unperturbed
-- name    : YoungConventions_RiskDominance_unperturbed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:46.231066+00:00
-- url     : https://prove2.me/theorems/0290b243-966d-45e2-b7d1-872d876b417b
-- title:
--   Adaptive play $P^0$ without mistakes, display (1)
-- statement:
--   Let $p$ be a best-reply distribution. **Adaptive play with memory $m$ and sample size $k$** is the Markov chain on $H$ with transition probabilities
--   $$P^0_{hh'}=\prod_{i=1}^n p_i(s_i\mid h)\quad\text{if $h'$ is a successor of $h$ and $s$ is the right-most element of $h'$},$$
--   and $P^0_{hh'}=0$ if $h'$ is not a successor of $h$.
--
--   $P^0$ is the unperturbed process; its recurrent communication classes are the candidates for stochastic stability.
--
--   **Formalization Note** $P^0$ is a real matrix indexed by $H\times H$, rows indexed by the current state. The sample size enters only through the hypothesis that $p$ is a best-reply distribution for $k$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 62, display (1)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_newest
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor

open Classical

namespace YoungConventions.RiskDominance

/-- **Adaptive play `P⁰` without mistakes**, display (1). Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 62 (PDF p. 7): "If `s` is
the right-most element of `h′`, the probability of moving from `h` to `h′` is
`P⁰_{hh′} = ∏_{i=1,n} pᵢ(sᵢ|h)`. `P⁰_{hh′} = 0` if `h′` is not a successor of `h`. We call the
process `P⁰` adaptive play with memory `m` and sample size `k`."

**Formalization Note.** The transition matrix is a `Matrix (YoungConventions.AdaptivePlay.History S m) (YoungConventions.AdaptivePlay.History S m) ℝ`, rows
indexed by the current state. Memory `m` is the length of the state; the sample size `k` enters
only through the hypothesis that `p` is a best-reply distribution for `k`
(`IsBestReplyDistribution`). Players experiment independently, so the product is over all players. -/
noncomputable def unperturbed {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (p : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) : Matrix (YoungConventions.AdaptivePlay.History S m) (YoungConventions.AdaptivePlay.History S m) ℝ :=
  fun h h' => if YoungConventions.AdaptivePlay.IsSuccessor h h' then ∏ i, p i h (newest h' i) else 0

end YoungConventions.RiskDominance


