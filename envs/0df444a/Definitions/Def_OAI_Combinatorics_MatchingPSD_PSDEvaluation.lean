-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
-- name    : OAI_Combinatorics_MatchingPSD_PSDEvaluation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:58:51.756679+00:00
-- url     : https://prove2.me/theorems/93b22ee9-b005-4f80-8782-052d6c626981
-- title:
--   The trace evaluation map of a matrix family and its positive semidefinite cone
-- statement:
--   Let $I$ and $R$ be finite index sets and $(B_i)_{i\in I}$ a family of real $R\times R$ matrices.
--
--   1. **Evaluation map.** The linear map $\mathrm{ev}_B:\mathbb{R}^{R\times R}\to\mathbb{R}^I$ given by
--   $$
--   \mathrm{ev}_B(A)_i=\operatorname{tr}(AB_i).
--   $$
--   2. **Evaluation cone.** The image of the positive semidefinite matrices,
--   $$
--   \mathcal{C}_B=\{\mathrm{ev}_B(A):A\succeq0\}\subseteq\mathbb{R}^I .
--   $$
--
--   The cone $\mathcal{C}_B$ collects the trace pairings that a single positive semidefinite matrix can realise against the family. A positive semidefinite factorization of a slack matrix asks, row by row, for vectors in such a cone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PSDEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PSDEvaluation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

noncomputable def evaluation (B : I → Matrix R R ℝ) : Matrix R R ℝ →ₗ[ℝ] (I → ℝ) where
  toFun A := fun i => (A * B i).trace
  map_add' A C := by ext i; simp [add_mul, Matrix.trace_add]
  map_smul' t A := by ext i; simp [Matrix.trace_smul]

omit [Fintype I] in
@[simp] lemma evaluation_apply (B : I → Matrix R R ℝ) (A : Matrix R R ℝ) (i : I) :
    evaluation B A i = (A * B i).trace := rfl

noncomputable def evaluationCone (B : I → Matrix R R ℝ) : Set (I → ℝ) :=
  evaluation B '' {A | A.PosSemidef}

end AffinePSD

end OAI


