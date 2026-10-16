-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
-- name    : OAI_Analysis_HyperbolicCones_FiniteTopology
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:48:28.831623+00:00
-- url     : https://prove2.me/theorems/ccfb12da-f963-4403-8b89-e2a6c083dab6
-- title:
--   Quadratic-form evaluation on symmetric matrices indexed by an arbitrary finite set
-- statement:
--   Let $\iota$ be a finite index set and let $\mathrm{Sym}_\iota$ be the real vector space of symmetric real matrices whose rows and columns are indexed by $\iota$. For a vector $v\in\mathbb{R}^\iota$ the file defines the linear functional $q_v:\mathrm{Sym}_\iota\to\mathbb{R}$,
--
--   $$
--   q_v(X)=v^{\mathsf T}Xv=\sum_{i,j\in\iota}v_i\,X_{ij}\,v_j .
--   $$
--
--   It is additive and homogeneous in $X$.
--
--   This generalizes the corresponding functional on matrices indexed by $\{0,\dots,n-1\}$ to arbitrary finite index sets. The main example is the disjoint union $\iota=[a]\sqcup[c]$ of two index sets, which indexes two-block matrices. A symmetric $X$ is positive semidefinite exactly when $q_v(X)\ge0$ for all $v$. So the positive semidefinite cone in $\mathrm{Sym}_\iota$ is an intersection of closed half-spaces and is therefore closed. This is what lets positive semidefiniteness of the scaled two-block matrices pass to their limit as the scaling parameter tends to $0$.
--
--   **Formalization Note** The definition is `FiniteMatrix.quadraticEvaluation v`, a linear map from `selfAdjoint (Matrix ι ι ℝ)` to the reals for a `Fintype` index type with decidable equality. It is written with `dotProduct` and `mulVec`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/FiniteTopology.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/FiniteTopology.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u v

namespace Paper256.FiniteMatrix

def quadraticEvaluation {ι : Type u} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) : selfAdjoint (Matrix ι ι ℝ) →ₗ[ℝ] ℝ where
  toFun X := v ⬝ᵥ ((X : Matrix ι ι ℝ) *ᵥ v)
  map_add' X Y := by simp [add_mulVec, dotProduct_add]
  map_smul' c X := by simp [smul_mulVec, dotProduct_smul]

end Paper256.FiniteMatrix

end

end OAI


