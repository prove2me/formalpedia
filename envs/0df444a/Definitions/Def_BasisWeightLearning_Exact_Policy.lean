-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_Policy
-- name    : BasisWeightLearning_Exact_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:20:27.545999+00:00
-- url     : https://prove2.me/theorems/a4b96752-4e83-4334-a0c9-164f6271eb8b
-- title:
--   Signal-dependent finite continuation policy trees
-- statement:
--   A deterministic policy with $n$ remaining decisions is a tree. At zero decisions it chooses a terminal label. At a decision node it selects one action and has one subtree for each observed signal. Neither the action nor the choice of subtree can depend on the hidden parameter or an unobserved reward. Given terminal functions, the value of a node is $\sum_s p(a,s)(\theta)[r(a,s)(\theta)+\delta u_s(\theta)]$. The same $\theta$ is used in every descendant. Finite action, signal and terminal-label sets yield the finite deterministic family described by Eq. (4); randomization convexifies that family.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF pp. 9–11 (printed pp. 9–11), §3.2, Eq. (4) on p. 10 and footnote 3 on p. 11.

import Definitions.Def_BasisWeightLearning_Exact_HiddenModel

namespace BasisWeightLearning.Exact
inductive PolicyTree (A S L : Type) : ℕ → Type
  | terminal (l : L) : PolicyTree A S L 0
  | decision {n : ℕ} (action : A) (children : S → PolicyTree A S L n) :
      PolicyTree A S L (n + 1)

noncomputable def policyValue {Θ A S L : Type} [Fintype S]
    (M : HiddenModel Θ A S) (terminal : L → Θ → ℝ) :
    {n : ℕ} → PolicyTree A S L n → Θ → ℝ
  | 0, .terminal l => terminal l
  | _ + 1, .decision a children => fun θ =>
      ∑ s, M.probability a s θ *
        (M.reward a s θ + M.discount * policyValue M terminal (children s) θ)
end BasisWeightLearning.Exact


