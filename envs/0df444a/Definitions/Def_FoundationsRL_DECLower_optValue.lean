-- Prove2me | Definitions.Def_FoundationsRL_DECLower_optValue
-- name    : FoundationsRL_DECLower_optValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:59.514675+00:00
-- url     : https://prove2.me/theorems/81199b84-1665-471b-b825-581f85cb61e8
-- title:
--   Optimal mean reward $f^M(\pi_M)=\sup_{\pi}f^M(\pi)$
-- statement:
--   For a kernel $M$, the **optimal mean reward** is
--
--   $$
--   f^M(\pi_M)=\sup_{\pi\in\Pi} f^M(\pi),
--   $$
--
--   where $\pi_M:=\arg\max_{\pi\in\Pi}f^M(\pi)$ is the optimal decision of $M$.
--
--   It is the benchmark of the regret (6.3).
--
--   **Formalization Note** The supremum equals $f^M(\pi_M)$ whenever the maximum is attained, which the notation $\arg\max$ presupposes, and it is defined also when no maximizer exists. For a model every $f^M(\pi)$ lies in $[0,1]$, so the supremum is finite; for an empty decision space Lean's real supremum is $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.1, p. 94 (optimal decision π_M)

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_meanReward

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Optimal mean reward** `f^M(π_M)`, `π_M := arg max_{π∈Π} f^M(π)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.1, p. 94.

`optValue M = sup_d f^M(d)`.

**Formalization Note.** The paper's `π_M` is an argmax, so `f^M(π_M) = max_π f^M(π)` whenever the
maximum is attained, which the notation presupposes; the supremum agrees with it then and is
defined also when no maximizer exists (a generalization). For a model (`IsModel`) every
`f^M(d)` lies in `[0, 1]`, so the range is bounded and the real `⨆` is the true supremum
(for an empty decision space it is `0`). -/
noncomputable def optValue {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (M : Kernel D (ℝ × O)) : ℝ :=
  ⨆ d, meanReward M d

end FoundationsRL.DECLower


