-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_HiddenModel
-- name    : BasisWeightLearning_Exact_HiddenModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:19:52.17391+00:00
-- url     : https://prove2.me/theorems/a3adb4c9-cb66-4f10-a1a2-71a496b7621f
-- title:
--   The fixed hidden-parameter learning-and-doing model
-- statement:
--   For parameter space $\Theta$, actions $A$ and signals $S$, the model consists of probabilities $p(a,s)(\theta)$, signal-dependent rewards $r(a,s)(\theta)$ and discount $\delta$. Validity requires $0<\delta\le1$, nonnegative probabilities and $\sum_s p(a,s)(\theta)=1$ for every action and parameter. The parameter is fixed through time. Rewards are arbitrary real numbers. Finiteness and nonemptiness of actions and signals are imposed by the theorem, and validity is a separate hypothesis. This general object contains no polynomial, frontier or conclusion assumption.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 7 (printed p. 7), §3, continuing on p. 8.

import Mathlib

namespace BasisWeightLearning.Exact
structure HiddenModel (Θ A S : Type) where
  probability : A → S → Θ → ℝ
  reward : A → S → Θ → ℝ
  discount : ℝ

def HiddenModel.Valid {Θ A S : Type} [Fintype S] (M : HiddenModel Θ A S) : Prop :=
  0 < M.discount ∧ M.discount ≤ 1 ∧
  (∀ a s θ, 0 ≤ M.probability a s θ) ∧
  (∀ a θ, ∑ s, M.probability a s θ = 1)
end BasisWeightLearning.Exact


