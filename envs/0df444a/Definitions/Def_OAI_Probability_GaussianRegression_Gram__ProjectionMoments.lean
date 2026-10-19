-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Gram__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:33:45.952953+00:00
-- url     : https://prove2.me/theorems/2d2dab3a-f55f-48f1-a7b4-222d41130181
-- title:
--   The upper-triangular Gram–Schmidt factor
-- statement:
--   For vectors $v_1,\dots,v_n$ in an inner product space with Gram–Schmidt vectors $g_i$, the upper-triangular factor is the $n\times n$ matrix
--   $$
--   U_{ij}=[i=j]+[i<j]\,\frac{\langle g_i,v_j\rangle}{\|g_i\|^2},
--   $$
--   which expresses each $v_j$ in terms of the orthogonal vectors $g_i$: $v_j=\sum_iU_{ij}g_i$ (when the $g_i$ are nonzero). It is used to compare Gram determinants with products of orthogonal distances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Gram.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Gram.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments

namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end NoiselessRegression

end

end OAI


