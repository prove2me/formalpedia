-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
-- name    : OAI_Analysis_HyperbolicCones_GramProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:58:24.102392+00:00
-- url     : https://prove2.me/theorems/e0c2ca02-5053-444e-a3aa-362e7cb4648e
-- title:
--   The Gram projection $T(T^*T)^{-1}T^*$ of an operator between Hilbert spaces
-- statement:
--   Let $E$ and $F$ be real Hilbert spaces, that is, complete real inner product spaces. Let $T:E\to F$ be a bounded linear operator with Hilbert-space adjoint $T^*:F\to E$. The Gram projection of $T$ is the bounded operator on $F$
--
--   $$
--   \Pi_T=T\,(T^*T)^{-1}\,T^* : F\to F .
--   $$
--
--   Here $(T^*T)^{-1}$ is the inverse of $T^*T$ in the algebra of bounded operators on $E$ when $T^*T$ is invertible. When $T^*T$ is not invertible it is taken to be $0$, so that $\Pi_T=0$ in that case.
--
--   When $T^*T$ is invertible, $\Pi_T$ is the orthogonal projection of $F$ onto the range of $T$. In addition, the formula depends smoothly on $T$ as long as $T^*T$ stays invertible, since operator inversion is smooth. Consequently $I-\Pi_T$ is the orthogonal projection onto the orthogonal complement of the range of $T$. If the range of $T$ coincides with the range of a self-adjoint operator $A$, then $I-\Pi_T$ is the orthogonal projection onto $\ker A$. This yields smooth local formulas for kernel projections of smoothly varying self-adjoint operators, which the argument needs in order to differentiate such projections.
--
--   **Formalization Note** The definition is `gramProjection T`, written with `ContinuousLinearMap.adjoint` and `Ring.inverse`, which returns $0$ on non-invertible elements. The section also declares a real normed space `W` that this definition does not use.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/GramProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/GramProjection.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped ContDiff
open ContinuousLinearMap

universe u v w

namespace Paper256

section Gram

variable {E : Type u} {F : Type v} {W : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace E] [CompleteSpace F]

def gramProjection (T : E →L[ℝ] F) : F →L[ℝ] F :=
  T.comp ((Ring.inverse (T.adjoint.comp T)).comp T.adjoint)

end Gram

end Paper256

end

end OAI


