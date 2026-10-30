-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_PolynomialData
-- name    : BasisWeightLearning_Exact_PolynomialData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:21:27.20699+00:00
-- url     : https://prove2.me/theorems/462c9e80-684f-4244-b9aa-65a37404d8e7
-- title:
--   Assumption (A1) and expected-reward weights
-- statement:
--   Polynomial data supply signed finite weight vectors $w_p(a,s)$ and $w_r(a,s)$ for every action and signal. The separate representation predicate is (A1): their evaluations equal the model probability and reward functions on all of $[0,1]$. The expected-reward weight is defined by $w_{\bar r}(a)=\sum_s w_p(a,s)\otimes w_r(a,s)$. Probabilities are constrained as functions by model validity; their coefficients need not be nonnegative. All finite polynomial degrees are permitted.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 14 (printed p. 14), (A1), with Eq. (14) on p. 16.

import Definitions.Def_BasisWeightLearning_Exact_PolynomialWeights
import Definitions.Def_BasisWeightLearning_Exact_HiddenModel
open scoped BigOperators

namespace BasisWeightLearning.Exact
structure PolynomialData (A S : Type) where
  probability : A → S → Weight
  reward : A → S → Weight

def PolynomialData.Represents {A S : Type} (D : PolynomialData A S)
    (M : HiddenModel Theta A S) : Prop :=
  (∀ a s, evaluate (D.probability a s) = M.probability a s) ∧
  (∀ a s, evaluate (D.reward a s) = M.reward a s)

noncomputable def expectedWeight {A S : Type} [Fintype S]
    (D : PolynomialData A S) (a : A) : Weight :=
  ∑ s, D.probability a s * D.reward a s
end BasisWeightLearning.Exact


