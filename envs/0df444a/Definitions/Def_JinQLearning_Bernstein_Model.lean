-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Model
-- name    : JinQLearning_Bernstein_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:32:45.588984+00:00
-- url     : https://prove2.me/theorems/b62e4e4c-5070-4065-b058-54f339c3c454
-- title:
--   Finite stage-dependent bounded-reward model
-- statement:
--   A finite tabular episodic MDP with S states, A common actions and H stages. This specializes the published nonstationary MDP: actions at each state are identified with Fin A by an equivalence, and the paper's reward is the negative of its cost. The reward is in [0,1] at each of the H stages. Each transition row is nonnegative and sums to one, by the underlying published model, with no equality between different stages. Expectation is a finite weighted sum and variance is the weighted second moment minus the squared mean. Policy is the finite type of stage-indexed deterministic Markov maps. Positive cardinalities are required where the theorems use the model. Index h represents source stage h+1. The underlying MDP's unused later times impose no restrictions on the finite instance.
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 4–5, §2.

import Definitions.Def_MDPComplexity_CircuitValue_Model

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

/-- A bounded reward, common-action specialization of the published nonstationary MDP.
The published cost is the negative of the reward; times 0,...,H-1 correspond to 1,...,H. -/
structure Model (S A H : ℕ) where
  base : MDPComplexity.CircuitValue.MDP (Fin S)
  actions : ∀ x, base.D x ≃ Fin A
  reward_bounds : ∀ (h : Fin H) x a,
    -(base.c x ((actions x).symm a) h.val) ∈ Set.Icc (0 : ℝ) 1

variable {S A H : ℕ}

def reward (M : Model S A H) (h : Fin H) (x : Fin S) (a : Fin A) : ℝ :=
  -M.base.c x ((M.actions x).symm a) h.val

def transition (M : Model S A H) (h : Fin H) (x : Fin S) (a : Fin A) (y : Fin S) : ℝ :=
  M.base.p x ((M.actions x).symm a) h.val y

def expectation (M : Model S A H) (h : Fin H) (x : Fin S) (a : Fin A)
    (f : Fin S → ℝ) : ℝ := ∑ y, transition M h x a y * f y

def variance (M : Model S A H) (h : Fin H) (x : Fin S) (a : Fin A)
    (f : Fin S → ℝ) : ℝ := expectation M h x a (fun y => f y ^ 2) - (expectation M h x a f) ^ 2

abbrev Policy (S A H : ℕ) := Fin H → Fin S → Fin A

end JinQLearning.Bernstein


