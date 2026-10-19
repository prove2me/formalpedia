-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
-- name    : OAI_Combinatorics_MatchingPSD_SpectralContraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:37:02.378957+00:00
-- url     : https://prove2.me/theorems/e01a3253-5cbd-42ab-a5cb-24554d7a99ce
-- title:
--   Compression of a linear operator to a subspace
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $A : E \to E$ a linear map and $W \subseteq E$ a linear subspace. The **compression** of $A$ to $W$ is the linear map $A_W : W \to W$ obtained by applying $A$ to vectors of $W$ and projecting the result orthogonally back onto $W$:
--
--   $$
--   A_W = P_W \circ A \circ \iota_W ,
--   $$
--
--   where $\iota_W : W \to E$ is the inclusion and $P_W : E \to W$ is the orthogonal projection onto $W$. Equivalently, $A_W$ is determined by $\langle x, A_W y\rangle = \langle x, A y\rangle$ for all $x, y \in W$; in an orthonormal basis of $E$ extending one of $W$, its matrix is the corresponding principal block of the matrix of $A$.
--
--   Compressions of symmetric operators are symmetric, and for symmetric $A$ one has $\operatorname{tr}(A_W^2) \le \operatorname{tr}(A^2)$. This allows the spectrum of an operator on a subspace, such as the space of high-degree functions on perfect matchings, to be controlled by the Hilbert–Schmidt norm of the operator on the whole space: if every eigenvalue of $A_W$ has multiplicity at least $m$, then each eigenvalue $c$ satisfies $m c^2 \le \operatorname{tr}(A^2)$.
--
--   **Formalization Note** The definition is `compression A W := W.orthogonalProjectionOnto ∘ₗ (A ∘ₗ W.subtype)`, an element of `Module.End ℝ W`. Finite-dimensionality of `E` provides the orthogonal projection onto the subspace `W`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SpectralContraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SpectralContraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def compression (A : Module.End ℝ E) (W : Submodule ℝ E) :
    Module.End ℝ W := W.orthogonalProjectionOnto.toLinearMap.comp (A.comp W.subtype)

end MatchingSmoothing

end OAI


