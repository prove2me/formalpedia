-- Prove2me | Definitions.Def_FoundationsRL_DECLower_Algorithm_policyAt
-- name    : FoundationsRL_DECLower_Algorithm_policyAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:09:41.399212+00:00
-- url     : https://prove2.me/theorems/d641f966-57df-44f2-a533-efb529cb6cfd
-- title:
--   Round-$t$ decision distribution $p_t(\cdot\mid H_{t-1})$ read off a full history
-- statement:
--   For an algorithm $p$, a horizon $T$ and a round $t\in\{1,\dots,T\}$, this is the kernel that maps a history $H_T$ of $T$ rounds to
--
--   $$
--   p_t(\cdot\mid H_{t-1}),
--   $$
--
--   the round-$t$ decision distribution evaluated at the first $t-1$ rounds of $H_T$.
--
--   It is the "random variable $p_t$, viewed as a function of the history" of the proof of Proposition 28, and it enters both the expected regret and the average action distribution.
--
--   **Formalization Note** Rounds are $0$-based in Lean: index $t$ is round $t+1$ and reads coordinates $0,\dots,t-1$ of the history.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (6.3), p. 94; proof of Proposition 28, p. 108

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_Algorithm

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Round-`t` decision distribution as a function of the full history** `H_T ↦ p_t(· | H_{t−1})`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (6.3), p. 94 ("p_t ∈ Δ(Π) is the learner's distribution over decisions at round t") and
proof of Proposition 28, p. 108 ("Viewed as a function of the history H_{t−1}, each p_t is a random
variable").

For `t : Fin T` (round `t + 1`), `alg.policyAt T t` sends a history `h` of length `T` to
`alg.p t` evaluated at the first `t` rounds of `h`.

**Formalization Note.** 0-based: `t : Fin T` is round `t + 1`, and its decision distribution
reads only coordinates `0, …, t − 1` (rounds `1, …, t`) of the history. The restriction map is
measurable, so this is a kernel. -/
noncomputable def Algorithm.policyAt {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (T : ℕ) (t : Fin T) : Kernel (Fin T → D × ℝ × O) D :=
  (alg.p t).comap (fun h (i : Fin t) => h (Fin.castLE t.isLt.le i))
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

end FoundationsRL.DECLower


