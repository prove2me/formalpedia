-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
-- name    : OAI_Analysis_HyperbolicCones_PencilTopology
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:33:56.46043+00:00
-- url     : https://prove2.me/theorems/a88b99e1-d34b-4224-ad7a-636c40468150
-- title:
--   Evaluation of the quadratic form $v^{\mathsf T}Xv$ as a linear functional on symmetric matrices
-- statement:
--   Let $\mathrm{Sym}_n$ be the real vector space of symmetric real $n\times n$ matrices. For a vector $v\in\mathbb{R}^n$ the file defines the linear functional $q_v:\mathrm{Sym}_n\to\mathbb{R}$,
--
--   $$
--   q_v(X)=v^{\mathsf T}Xv=\sum_{i,j}v_i\,X_{ij}\,v_j .
--   $$
--
--   It is additive and homogeneous in $X$, so it is a linear map on $\mathrm{Sym}_n$.
--
--   A symmetric matrix $X$ is positive semidefinite exactly when $q_v(X)\ge0$ for every $v\in\mathbb{R}^n$. So the positive semidefinite cone in $\mathrm{Sym}_n$ is the intersection of the half-spaces $\{X: q_v(X)\ge0\}$. Each $q_v$ is a linear functional on a finite-dimensional space and hence continuous. This description is used to see that the positive semidefinite cone is closed, so that positive semidefiniteness passes to limits of symmetric matrices.
--
--   **Formalization Note** The definition is `quadraticEvaluation v`, a linear map from `Sym n` to the reals, written with `dotProduct` and `mulVec`. A separate version for symmetric matrices with an arbitrary finite index type is defined in the namespace `FiniteMatrix`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilTopology.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilTopology.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

def quadraticEvaluation {n : ℕ} (v : Fin n → ℝ) : Sym n →ₗ[ℝ] ℝ where
  toFun X := v ⬝ᵥ ((X : Mat n ℝ) *ᵥ v)
  map_add' X Y := by simp [add_mulVec, dotProduct_add]
  map_smul' c X := by simp [smul_mulVec, dotProduct_smul]

end Paper256

end

end OAI


