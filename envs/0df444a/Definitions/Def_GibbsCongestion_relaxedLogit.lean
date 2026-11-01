-- Prove2me | Definitions.Def_GibbsCongestion_relaxedLogit
-- name    : GibbsCongestion_relaxedLogit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:03:27.283912+00:00
-- url     : https://prove2.me/theorems/1145d6b7-adb6-4579-8413-85b37823436a
-- title:
--   Relaxed logit dynamics
-- statement:
--   The **relaxed logit dynamics** Markov chain on $\mathcal P^n$: from the current profile,
--
--   1. with probability $\tfrac12$, perform a swap step (two random players exchange strategies);
--   2. with probability $\tfrac12$, perform a logit-dynamics step.
--
--   Its transition matrix is $P=\tfrac12\,\mathrm{Swap}+\tfrac12\,\mathrm{Logit}$. For every symmetric congestion game it is an ergodic, reversible chain whose stationary distribution is the Gibbs distribution. It is the chain whose mixing time Theorem 4.4 bounds.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.16

import Mathlib
import Definitions.Def_GibbsCongestion_logitStep
import Definitions.Def_GibbsCongestion_swapStep

namespace GibbsCongestion

/-- The **relaxed logit dynamics** Markov chain (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.16): with probability `1/2`
perform a swap step (two random players exchange strategies), and with probability `1/2`
perform a logit step. Its transition matrix is `(1/2)·swap + (1/2)·logit`. -/
noncomputable def relaxedLogit {E : Type*} [Fintype E] [DecidableEq E] (P : Finset (Finset E))
    (n : ℕ) (c : E → ℕ → ℝ) (T : ℝ) : Matrix (Fin n → P) (Fin n → P) ℝ :=
  (1 / 2 : ℝ) • swapStep P n + (1 / 2 : ℝ) • logitStep P n c T

end GibbsCongestion


