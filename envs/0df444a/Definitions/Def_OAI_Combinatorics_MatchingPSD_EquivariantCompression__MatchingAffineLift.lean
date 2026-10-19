-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:17:57.985897+00:00
-- url     : https://prove2.me/theorems/247f4932-b7b3-4041-828d-dfac01a5066f
-- title:
--   Permutations of coordinates as isometries of $\ell^2(X)$
-- statement:
--   Let $X$ be a finite set and let $\ell^2(X) = \mathbb{R}^X$ carry the Euclidean inner product $\langle u, v\rangle = \sum_{x \in X} u(x) v(x)$. For a permutation $e$ of $X$, the module defines the linear isometric isomorphism $\Pi_e : \ell^2(X) \to \ell^2(X)$ that permutes coordinates,
--
--   $$
--   (\Pi_e v)(x) = v\bigl(e^{-1}(x)\bigr) \qquad (v \in \ell^2(X),\ x \in X),
--   $$
--
--   so the value of $v$ at $y$ is moved to position $e(y)$. It preserves the Euclidean norm and satisfies $\Pi_{e e'} = \Pi_e \Pi_{e'}$. A matrix $A$ indexed by $X \times X$ commutes with $\Pi_e$ exactly when $A(e(x), e(y)) = A(x, y)$ for all $x, y \in X$.
--
--   These isometries are the form in which symmetry enters the spectral arguments: taking $X$ to be the set of perfect matchings and $e$ a relabelling of matchings, one shows that the compression of an equivariant operator to a relabelling-invariant subspace is again equivariant, so its eigenspaces are invariant under all relabellings.
--
--   **Formalization Note** The definition is `permIso e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e` on `EuclideanSpace ℝ X`, together with its evaluation lemma `permIso_apply`: `permIso e v x = v (e.symm x)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EquivariantCompression.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EquivariantCompression.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

noncomputable def permIso (e : Equiv.Perm X) :
    EuclideanSpace ℝ X ≃ₗᵢ[ℝ] EuclideanSpace ℝ X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] lemma permIso_apply (e : Equiv.Perm X) (v : EuclideanSpace ℝ X) (x : X) :
    permIso e v x = v (e.symm x) := rfl

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end CompressionEquivariance
end MatchingSmoothing

end OAI


