-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_PolynomialWeights
-- name    : BasisWeightLearning_Exact_PolynomialWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:20:31.545959+00:00
-- url     : https://prove2.me/theorems/d231f8d8-b534-45d9-a6c5-13d2e2fceaca
-- title:
--   Polynomial basis weights, evaluation and coefficient frontier
-- statement:
--   A weight is a real polynomial, equivalently a finitely supported sequence of signed coefficients. Evaluation gives $\Phi w(\theta)=\sum_i w_i\theta^i$. Polynomial addition implements zero padding and coefficient addition; multiplication is coefficient convolution, $(ab)_k=\sum_{i+j=k}a_i b_j$, not a Kronecker product. The coordinate vector at degree $d$ is $(w_0,\ldots,w_d)$. A member of a finite weight set is retained exactly when its vector is in the vector frontier at some common degree bound $d$ for the entire set. There is no fixed degree cap. For multiple distinct members, a strictly exposing normal must assign positive total mass to nonzero comparison coordinates, so deleting padded zero coordinates and renormalizing preserves exposure; a singleton is retained at every bound. Definition 4 is read as padding to $\max(d_a,d_b)+1$ components, as its surrounding example requires (insight I1).
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 14 (printed p. 14), §4.1, Definitions 4–5 (p. 15) and Definition 2.

import Definitions.Def_BasisWeightLearning_Exact_Domain
import Definitions.Def_BasisWeightLearning_Exact_VectorFrontier

namespace BasisWeightLearning.Exact
abbrev Weight := Polynomial ℝ
noncomputable def evaluate (w : Weight) : ValueFunction := fun θ => w.eval (θ : ℝ)
noncomputable def coordinates (d : ℕ) (w : Weight) : Fin (d + 1) → ℝ :=
  fun i => w.coeff i

noncomputable def weightFrontier (W : Set Weight) : Set Weight :=
  {w | w ∈ W ∧ ∃ d : ℕ, (∀ v ∈ W, v.natDegree ≤ d) ∧
    coordinates d w ∈ vectorFrontier (coordinates d '' W)}
end BasisWeightLearning.Exact


