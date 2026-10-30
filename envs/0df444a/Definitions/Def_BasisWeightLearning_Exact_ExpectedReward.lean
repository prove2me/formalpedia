-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_ExpectedReward
-- name    : BasisWeightLearning_Exact_ExpectedReward
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:20:33.685834+00:00
-- url     : https://prove2.me/theorems/5f20d0ce-e78e-4b0e-81c8-141260f71e6a
-- title:
--   The expected one-period reward
-- statement:
--   For each action $a$, the expected reward conditional on the hidden parameter is the function $\bar r(a)(\theta)=\sum_{s\in S}p(a,s)(\theta)r(a,s)(\theta)$. The sum is finite. This is a derived function of the operational model and is distinct from the reward conditional on an individual signal.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 10 (printed p. 10), Eq. (5).

import Definitions.Def_BasisWeightLearning_Exact_HiddenModel
open scoped BigOperators

namespace BasisWeightLearning.Exact
noncomputable def expectedReward {Θ A S : Type} [Fintype S]
    (M : HiddenModel Θ A S) (a : A) : Θ → ℝ :=
  fun θ => ∑ s, M.probability a s θ * M.reward a s θ
end BasisWeightLearning.Exact


