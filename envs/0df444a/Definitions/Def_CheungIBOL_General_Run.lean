-- Prove2me | Definitions.Def_CheungIBOL_General_Run
-- name    : CheungIBOL_General_Run
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:13:44.985038+00:00
-- url     : https://prove2.me/theorems/6c021e45-b5ea-46cc-82b6-2a93d08f0fc5
-- title:
--   IBOL history law and expected physical revenue
-- statement:
--   Fix a deterministic context sequence $x_0,x_1,\ldots$, a model, an oracle and $\epsilon$. The law at time zero is the point mass at the empty history. From a history of length $t$, sample the next action from the oracle using $x_t$ and the current discounted rewards, then sample a fresh vector outcome from $\rho_{x_t,a}$, and append the observed triple. This sequential conditional-law construction makes policy randomization independent of the new outcome conditional on the chosen action and history. It retains feedback after depletion and never draws counterfactual outcomes for unchosen actions.
--
--   The expected revenue over $T$ rounds is the integral of the physical revenue over this constructed history law. Only the first $T$ contexts are used, so any finite oblivious sequence has this representation. The history measure is a probability measure supported on length $T$, and the bounded measurable physical revenue is integrable. These are properties of the construction, not hypotheses assuming a conclusion of the performance theorem.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 9–10 (including footnote 2) and 13–15, Algorithm 1, https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Oracle

open MeasureTheory
noncomputable section

namespace CheungIBOL.General

/-- The actual finite-history distribution. First sample the chosen action, then a fresh
outcome from its fixed law; append the feedback even when all resources are depleted. -/
def runLaw {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (x : ℕ → Fin c) :
    ℕ → Measure (History n c A)
  | 0 => Measure.dirac []
  | t + 1 => (runLaw M O ε x t).bind fun h =>
      (actionLaw M O ε t h (x t)).bind fun a =>
        (M.law (x t, a)).map fun y => h ++ [(x t, a, y)]

def expectedRevenue {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (x : ℕ → Fin c) (T : ℕ) : ℝ :=
  ∫ h, revenue M h ∂runLaw M O ε x T

end CheungIBOL.General


