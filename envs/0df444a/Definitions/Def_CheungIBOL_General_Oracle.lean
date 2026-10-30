-- Prove2me | Definitions.Def_CheungIBOL_General_Oracle
-- name    : CheungIBOL_General_Oracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:12:44.520978+00:00
-- url     : https://prove2.me/theorems/8efd19bb-4795-452f-a12e-5bc7955b052d
-- title:
--   History-dependent randomized bandit oracle
-- statement:
--   A randomized oracle is a sequence of probability kernels $O_t$ from the past observed history, current context, and current vector of discounted rewards to actions in $A$. The action law for IBOL is
--   $$O_t\bigl(h,x,r(1-\Psi_\epsilon(N(h)/b))\bigr).$$
--   The decision receives neither the true outcome law, future contexts, nor the horizon. It may depend on the entire ordered history and may randomize arbitrarily; it is not required to select a maximizer. The sequence is indexed by zero-based time, so $O_t$ here corresponds to the source oracle for period $t+1$. Probability kernels are the behavioral representation of the source's independent internal randomization.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 13–15, Algorithm 1, equation (6) and auxiliary problem, https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Inventory

open MeasureTheory ProbabilityTheory
noncomputable section

namespace CheungIBOL.General

/-- Randomized, history-dependent decisions. The input has neither the true law nor future
contexts nor the horizon. Time t denotes source period t+1. -/
structure Oracle (n c : ℕ) (A : Type*) [MeasurableSpace A] where
  decision : ℕ → Kernel (History n c A × Fin c × (Fin n → ℝ)) A
  decision_probability : ∀ t, IsMarkovKernel (decision t)

attribute [instance] Oracle.decision_probability

def actionLaw {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (t : ℕ)
    (h : History n c A) (x : Fin c) : Measure A :=
  O.decision t (h, x, discounted M ε h)

end CheungIBOL.General


