-- Prove2me | Definitions.Def_ShapleyScarf_Balanced_BalancedGame
-- name    : ShapleyScarf_Balanced_BalancedGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:17.376405+00:00
-- url     : https://prove2.me/theorems/bf657ca8-272b-422f-8a0e-af890c5917e8
-- title:
--   Section 3 — balanced families and balanced games
-- statement:
--   A family $T$ of nonempty coalitions of a finite trader set $N$ is **balanced** when it admits nonnegative real weights $\delta_S$, zero for coalitions outside $T$, satisfying
--
--   $$
--   \sum_{\substack{S\in T\\j\in S}}\delta_S=1
--   \qquad\text{for every }j\in N.
--   $$
--
--   A game $V$ without side payments is a **balanced game** if every such family satisfies
--   $\bigcap_{S\in T}V(S)\subseteq V(N)$. Zero weights within $T$ are allowed. These definitions supply the general balance condition used to classify the housing market game.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; pp. 108–109 of the source printing, Section 3, balanced-family equations and condition (e)

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_NTUGame

namespace ShapleyScarf.Balanced

def IsBalancingWeights {N : Type*} [Fintype N] [DecidableEq N]
    (T : Finset (Finset N)) (δ : Finset N → ℝ) : Prop :=
  (∀ S, 0 ≤ δ S) ∧
  (∀ S, S ∉ T → δ S = 0) ∧
  (∀ j : N, ∑ S ∈ T, (if j ∈ S then δ S else 0) = 1)

def IsBalancedFamily {N : Type*} [Fintype N] [DecidableEq N]
    (T : Finset (Finset N)) : Prop :=
  (∀ S ∈ T, S.Nonempty) ∧ ∃ δ : Finset N → ℝ, IsBalancingWeights T δ

def IsBalancedGame {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) : Prop :=
  IsNTUGame V ∧
  ∀ T : Finset (Finset N), IsBalancedFamily T →
    ∀ x : N → ℝ, (∀ S ∈ T, x ∈ V S) → x ∈ V Finset.univ

end ShapleyScarf.Balanced


