-- Prove2me | Definitions.Def_FoundationsRL_DECLower_histLaw
-- name    : FoundationsRL_DECLower_histLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:14.556001+00:00
-- url     : https://prove2.me/theorems/a9d1df25-0562-401a-b94b-480c7a8f51a5
-- title:
--   Law $\mathbb P^M$ of the history $H_t$ under algorithm $p$ and model $M$
-- statement:
--   For an algorithm $p$ and a kernel $M:\Pi\to\Delta(\mathbb R\times\mathcal O)$, the **history law** $\mathbb P^M$ on $H_t=(\pi_1,r_1,o_1,\dots,\pi_t,r_t,o_t)$ is the law of the process
--
--   $$
--   \pi_s\sim p_s(\cdot\mid H_{s-1}),\qquad (r_s,o_s)\sim M(\pi_s),\qquad s=1,\dots,t,
--   $$
--
--   where, given $\pi_s$, the pair $(r_s,o_s)$ is drawn from $M(\pi_s)$ regardless of the past (Assumption 7). It is built round by round: $H_0$ is the empty history, and $H_{s}$ appends $(\pi_s,r_s,o_s)$ to $H_{s-1}$.
--
--   This is the distribution $\mathbb P^M$ over $H_T$ "for this algorithm when $M$ is the true model" in the proof of Proposition 28; the expected regret and the average action distribution are expectations under it.
--
--   **Formalization Note** Coordinates are $0$-based (coordinate $i$ is round $i+1$). The append map is measurable (checked in a verification file), so the law is a genuine pushforward. For a Markov $M$ it is a probability measure.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Assumption 7 and (6.1), p. 94; footnote 14, p. 104; proof of Proposition 28, p. 108

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_Algorithm

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Law of the history** `P^M` of an algorithm interacting with a model.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Assumption 7 and (6.1), p. 94; footnote 14, p. 104; proof of Proposition 28, p. 108
("Let P^M denote the distribution over H_T for this algorithm when M is the true model").

`histLaw alg M t` is the law of `H_t = (π_1, r_1, o_1, …, π_t, r_t, o_t)` when, for each round,
`π_{s+1} ∼ p_{s+1}(· | H_s)` and then `(r_{s+1}, o_{s+1}) ∼ M(π_{s+1})`, appended to the history.
It is defined by recursion: `H_0` is the empty history (a point mass), and `H_{t+1}` is drawn by
composing the law of `H_t` with the kernel "draw the decision from `alg.p t`, then the
reward–observation pair from `M` at that decision", followed by appending (`Fin.snoc`).

**Formalization Note.** 0-based coordinates: coordinate `i` of a history is round `i + 1`.
Assumption 7's "generated independently" is the fact that given `π_t`, `(r_t, o_t) ∼ M(π_t)`
regardless of the past (`Kernel.prodMkLeft` ignores the history). The append map is measurable
(checked in `Solutions/verification/FoundationsRL_DECLower_sanity.lean`), so `Measure.map` is the
pushforward. For a Markov `M` each `histLaw alg M t` is a probability measure. -/
noncomputable def histLaw {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (M : Kernel D (ℝ × O)) : (t : ℕ) → Measure (Fin t → D × ℝ × O)
  | 0 => Measure.dirac (isEmptyElim : Fin 0 → D × ℝ × O)
  | t + 1 =>
      ((histLaw alg M t) ⊗ₘ ((alg.p t) ⊗ₖ (Kernel.prodMkLeft (Fin t → D × ℝ × O) M))).map
        (fun x => Fin.snoc (α := fun _ => D × ℝ × O) x.1 x.2)

end FoundationsRL.DECLower


