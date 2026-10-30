-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_WeightRecursion
-- name    : BasisWeightLearning_Exact_WeightRecursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:22:32.841504+00:00
-- url     : https://prove2.me/theorems/2ad48d74-bfea-4eaa-a5d0-48e172bc38da
-- title:
--   The basis-weight backward recursion
-- statement:
--   Given a next-period weight set $W$ and action $a$, form every polynomial weight $w_{\bar r}(a)+\delta\sum_s w_p(a,s)\otimes w_s$ with $w_s\in W$ for every signal, and apply the coefficient-space frontier. Apply the coefficient frontier again to the union of all action families. Iterate from the assigned terminal weight set. Scalar multiplication by $\delta$ is multiplication by its constant polynomial. All degrees and signed coefficients are retained. The index is the number of decisions remaining, with the terminal family at zero.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 17 (printed p. 17), Eqs. (15)–(16).

import Definitions.Def_BasisWeightLearning_Exact_PolynomialData
import Definitions.Def_BasisWeightLearning_Exact_TerminalData
open scoped BigOperators

namespace BasisWeightLearning.Exact
noncomputable def weightAction {A S : Type} [Fintype S]
    (D : PolynomialData A S) (δ : ℝ) (W : Set Weight) (a : A) : Set Weight :=
  weightFrontier {w | ∃ next : S → Weight,
    (∀ s, next s ∈ W) ∧
    w = expectedWeight D a + Polynomial.C δ * ∑ s, D.probability a s * next s}

noncomputable def weightStages {A S : Type} [Fintype S]
    (D : PolynomialData A S) (δ : ℝ) (B : TerminalData) : ℕ → Set Weight
  | 0 => B.weights
  | n + 1 => weightFrontier (⋃ a, weightAction D δ (weightStages D δ B n) a)
end BasisWeightLearning.Exact


