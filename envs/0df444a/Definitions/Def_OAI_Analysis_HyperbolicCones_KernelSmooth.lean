-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
-- name    : OAI_Analysis_HyperbolicCones_KernelSmooth
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:01:28.626082+00:00
-- url     : https://prove2.me/theorems/e31eabcf-ba41-4184-be3e-23bc6a14c1bc
-- title:
--   Symmetric matrices as linear operators on Euclidean space
-- statement:
--   For a natural number $c$, let $\mathrm{Sym}_c$ be the real vector space of symmetric real $c\times c$ matrices. Let $\mathbb{R}^c$ carry its Euclidean inner product, and let $\mathcal L(\mathbb{R}^c)$ be the space of (bounded) linear operators on it. The file defines the linear map $\iota_c:\mathrm{Sym}_c\to\mathcal L(\mathbb{R}^c)$ that sends a symmetric matrix to the operator of matrix-vector multiplication:
--
--   $$
--   \iota_c(H)\,v=Hv\qquad(H\in\mathrm{Sym}_c,\ v\in\mathbb{R}^c).
--   $$
--
--   It is the restriction to $\mathrm{Sym}_c$ of the standard identification of $c\times c$ matrices with linear operators on $\mathbb{R}^c$, which is an isomorphism of algebras. In particular $\iota_c$ is injective, and its values are self-adjoint operators.
--
--   The map transports matrix-valued families, such as $u\mapsto E(I-uu^{\mathsf T})$ for a linear map $E$ into $\mathrm{Sym}_c$, to operator-valued families. Results about smooth families of self-adjoint operators and their kernel projections, which are formulated for operators on inner product spaces, then apply to such matrix families.
--
--   **Formalization Note** The definition is `symmetricOperatorLinear c`. It composes the inclusion of `Sym c` into all matrices with the algebra equivalence `Matrix.toEuclideanCLM` onto continuous linear maps of `Vec c`, the Euclidean space of dimension $c$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/KernelSmooth.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/KernelSmooth.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection

namespace OAI

noncomputable section

open scoped ContDiff Matrix.Norms.L2Operator
open Set Matrix ContinuousLinearMap

namespace Paper256

def symmetricOperatorLinear (c : ℕ) : Sym c →ₗ[ℝ] (Vec c →L[ℝ] Vec c) :=
  (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.comp
    (selfAdjoint.submodule ℝ (Mat c ℝ)).subtype

end Paper256

end

end OAI


