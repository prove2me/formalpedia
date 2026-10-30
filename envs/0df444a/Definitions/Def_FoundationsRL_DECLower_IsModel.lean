-- Prove2me | Definitions.Def_FoundationsRL_DECLower_IsModel
-- name    : FoundationsRL_DECLower_IsModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:03.819087+00:00
-- url     : https://prove2.me/theorems/dfe43f87-44dd-43f5-a1a0-fd33f8ea693f
-- title:
--   Model $M:\Pi\to\Delta([0,1]\times\mathcal O)$
-- statement:
--   Let $\Pi$ be a measurable decision space and $\mathcal O$ a measurable observation space. A **model** is a probability kernel
--
--   $$
--   M:\Pi\to\Delta(\mathbb R\times\mathcal O),\qquad \pi\mapsto M(\pi),
--   $$
--
--   such that for every decision $\pi$ the reward $r$ of $(r,o)\sim M(\pi)$ lies in $[0,1]$ almost surely.
--
--   In the Decision Making with Structured Observations (DMSO) framework, the learner selects a decision $\pi_t$ and nature draws a reward and an observation $(r_t,o_t)\sim M^\star(\pi_t)$ from the true model (Assumption 7, (6.1)).
--
--   **Formalization Note** The reward space $\mathcal R\subseteq\mathbb R$ of §6.1 is taken to be $[0,1]$, the range used in the proof of Proposition 28 ("since rewards are in $[0,1]$", p. 109) and in its source, Foster, Golowich & Han (arXiv:2301.08215), which assumes $\mathcal R=[0,1]$ throughout. The kernel is valued in $\mathbb R\times\mathcal O$ and puts full mass on $[0,1]\times\mathcal O$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.1, Assumption 7 and (6.1), p. 94; rewards in [0, 1]: proof of Proposition 28, p. 109

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Model** `M : Π → Δ(R × O)` with rewards in `[0, 1]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.1, Assumption 7 and (6.1), p. 94 ("M⋆ : Π → Δ(R × O) is the underlying model");
rewards in `[0, 1]`: proof of Proposition 28, p. 109 ("since rewards are in [0, 1]").

`IsModel M` says that `M` is a Markov kernel from the decision space `D` (the paper's `Π`) to
reward–observation pairs `ℝ × O`, and that for every decision the reward lies in `[0, 1]` almost
surely.

**Formalization Note.** The reward space `R ⊆ ℝ` of §6.1 is taken to be `[0, 1]`, the range the
proof of Proposition 28 (p. 109) and its source (Foster, Golowich & Han, arXiv:2301.08215,
"We assume throughout the paper that R = [0, 1]") use; the kernel is valued in `ℝ × O` and puts
full mass on `[0, 1] × O`. Measurability of `M` in the decision is part of being a kernel. -/
def IsModel {D O : Type*} [MeasurableSpace D] [MeasurableSpace O] (M : Kernel D (ℝ × O)) : Prop :=
  IsMarkovKernel M ∧ ∀ d, M d (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) = 1

end FoundationsRL.DECLower


