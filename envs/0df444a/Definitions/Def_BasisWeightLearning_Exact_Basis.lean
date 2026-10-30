-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_Basis
-- name    : BasisWeightLearning_Exact_Basis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:21:16.851698+00:00
-- url     : https://prove2.me/theorems/9a046d35-38f5-4830-9a1a-992b5aa2939c
-- title:
--   Nonnegative finite basis families in the function space
-- statement:
--   A degree-$d$ basis family consists of $d+1$ nonnegative square-integrable functions on $[0,1]$, linearly independent as elements of $L^2$ with Lebesgue measure. Its evaluation on a weight vector is the finite linear combination $\Phi w=\sum_{i=0}^d w_i\phi_i$. Square-integrable functions are stored by measurable representatives, and independence is imposed on their $L^2$ equivalence classes. No strict positivity, constant basis element or frontier-preservation axiom is assumed. The monomials $1,\theta,\ldots,\theta^d$ are included.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 17 (printed p. 17), Lemma 3 and inherited preamble from p. 16.

import Definitions.Def_BasisWeightLearning_Exact_FunctionFrontier
open MeasureTheory
open scoped BigOperators

namespace BasisWeightLearning.Exact
structure BasisFamily (d : ℕ) where
  function : Fin (d + 1) → ValueFunction
  squareIntegrable : ∀ i, MemLp (function i) 2 intervalMeasure
  nonnegative : ∀ i θ, 0 ≤ function i θ
  independent : LinearIndependent ℝ (fun i => (squareIntegrable i).toLp (function i))

noncomputable def BasisFamily.evaluate {d : ℕ} (Φ : BasisFamily d)
    (w : Fin (d + 1) → ℝ) : ValueFunction :=
  fun θ => ∑ i, w i * Φ.function i θ
end BasisWeightLearning.Exact


