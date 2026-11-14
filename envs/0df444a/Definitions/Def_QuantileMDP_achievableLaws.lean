-- Prove2me | Definitions.Def_QuantileMDP_achievableLaws
-- name    : QuantileMDP_achievableLaws
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T02:47:23.138235+00:00
-- url     : https://prove2.me/theorems/fcaed0cc-059a-4829-a4a2-417a8dccac99
-- title:
--   Attainable finite-horizon reward laws in a quantile MDP
-- statement:
--   Backward recursion on the sets of reward laws for each state and time. Each iteration enumerates all actions and independent choices of feasible successor-state continuation laws and mixes their reward-shifted distributions.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.1, Theorem 4, p. 21. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_Model

open MeasureTheory

namespace QuantileMDP

/-- Backward recursion on all attainable return laws. Given an action,
choose a continuation law at each successor, translate it by the immediate
reward, and mix with the transition probabilities. -/
noncomputable def achievableLaws {S A : Type*} [Fintype S] (M : Model S A) :
    ℕ → ℕ → S → Set (Measure ℝ)
  | 0, _, _ => {Measure.dirac 0}
  | n + 1, t, s =>
    {μ | ∃ a ∈ M.adm t s, ∃ ν : S → Measure ℝ,
      (∀ i, ν i ∈ achievableLaws M n (t + 1) i) ∧
        μ = ∑ i, M.P t s a i • (ν i).map (fun x => x + M.r t s a i)}

end QuantileMDP


