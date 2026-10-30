-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_FunctionRecursion
-- name    : BasisWeightLearning_Exact_FunctionRecursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:22:29.83822+00:00
-- url     : https://prove2.me/theorems/10ae9d0a-1af2-4478-84e9-a80ba001aeba
-- title:
--   The independent continuation-function backward recursion
-- statement:
--   Given a next-period family $U$ and an action $a$, form every function $\bar r(a)+\delta\sum_s p(a,s)u_s$ with $u_s\in U$ separately for each signal; apply the function-space frontier to this set. Apply that frontier again to the union of the action families. Iterate from the supplied terminal family. The natural-number index counts decisions remaining: index $0$ is the terminal family and index $n+1$ is formed from index $n$. This recursion uses the model functions, not evaluation of a weight recursion.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 11 (printed p. 11), Eqs. (7)–(9).

import Definitions.Def_BasisWeightLearning_Exact_ExpectedReward
import Definitions.Def_BasisWeightLearning_Exact_FunctionFrontier
import Definitions.Def_BasisWeightLearning_Exact_TerminalData
open scoped BigOperators

namespace BasisWeightLearning.Exact
noncomputable def functionAction {A S : Type} [Fintype S]
    (M : HiddenModel Theta A S) (U : Set ValueFunction) (a : A) : Set ValueFunction :=
  functionFrontier {u | ∃ next : S → ValueFunction,
    (∀ s, next s ∈ U) ∧
    u = fun θ => expectedReward M a θ +
      M.discount * ∑ s, M.probability a s θ * next s θ}

noncomputable def functionStages {A S : Type} [Fintype S]
    (M : HiddenModel Theta A S) (B : TerminalData) : ℕ → Set ValueFunction
  | 0 => (B.functions : Set ValueFunction)
  | n + 1 => functionFrontier (⋃ a, functionAction M (functionStages M B n) a)
end BasisWeightLearning.Exact


