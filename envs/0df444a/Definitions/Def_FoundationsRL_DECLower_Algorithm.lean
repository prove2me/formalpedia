-- Prove2me | Definitions.Def_FoundationsRL_DECLower_Algorithm
-- name    : FoundationsRL_DECLower_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:09:11.17007+00:00
-- url     : https://prove2.me/theorems/7bcc98e0-c14d-41ca-9819-cde98940f7ce
-- title:
--   Algorithm $p_t(\cdot\mid H_{t-1})$ for the DMSO protocol
-- statement:
--   An **algorithm** for the DMSO protocol over decision space $\Pi$ and observation space $\mathcal O$ is a sequence of probability kernels
--
--   $$
--   p_t(\cdot\mid H_{t-1})\in\Delta(\Pi),\qquad t=1,2,\dots,
--   $$
--
--   where $H_{t-1}=(\pi_1,r_1,o_1,\dots,\pi_{t-1},r_{t-1},o_{t-1})$ is the history of the first $t-1$ rounds. At round $t$ the learner draws $\pi_t\sim p_t(\cdot\mid H_{t-1})$.
--
--   The definition covers adaptive and randomized algorithms ("any randomization used by the algorithm", footnote 14), which is the class over which Proposition 28 quantifies.
--
--   **Formalization Note** The kernel with Lean index $t$ is the notes' $p_{t+1}(\cdot\mid H_t)$. A history of length $t$ is a function from $\{0,\dots,t-1\}$ to $\Pi\times\mathbb R\times\mathcal O$; coordinate $i$ is round $i+1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (6.27) and footnote 14, p. 104; proof of Proposition 28, p. 108

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Algorithm** `p = p_1, …, p_T`, `p_t = p_t(· | H_{t−1})`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (6.27) and footnote 14, p. 104; proof of Proposition 28, p. 108 ("any fixed algorithm,
which we recall is defined by a sequence of mappings p_1, …, p_T, where p_t = p_t(· | H_{t−1})").

An algorithm is a sequence of Markov kernels: `p t` maps a history
`H_t = (π_1, r_1, o_1, …, π_t, r_t, o_t)` of length `t` to a distribution over decisions.

**Formalization Note.** `p t` is the paper's `p_{t+1}(· | H_t)` (0-based index). A history of
length `t` is `Fin t → D × ℝ × O`; coordinate `i` is round `i + 1`. The kernel may depend on the
whole realized history and is randomized, which covers every algorithm of footnote 14
("any randomization used by the algorithm"). Kernels are measurable in the history by definition. -/
structure Algorithm (D O : Type*) [MeasurableSpace D] [MeasurableSpace O] where
  /-- `p t` is the decision distribution at round `t + 1` given the history of the first `t` rounds. -/
  p : (t : ℕ) → Kernel (Fin t → D × ℝ × O) D
  /-- each `p t` is a probability kernel -/
  markov : ∀ t, IsMarkovKernel (p t)

end FoundationsRL.DECLower


