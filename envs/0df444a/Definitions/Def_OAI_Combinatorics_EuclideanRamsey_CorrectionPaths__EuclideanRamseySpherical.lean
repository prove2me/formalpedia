-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:21:02.104093+00:00
-- url     : https://prove2.me/theorems/664f7fe1-839f-48ba-bafb-bcee009c2eed
-- title:
--   Coordinate permutations of Euclidean space
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   For a permutation $\sigma$ of $\{0,\dots,\ell-1\}$, this module defines the linear isometry $P_\sigma$ of $\mathbb R^\ell$ that permutes coordinates:
--   $$
--   (P_\sigma x)_j=x_{\sigma^{-1}(j)} .
--   $$
--   It records this formula and that the identity permutation acts trivially. Coordinate permutations are the symmetries used to move between congruent copies of a configuration placed in different coordinate blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseySpherical

namespace OAI

universe uGroup uIndex uAction uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [Fintype ι] [DecidableEq ι]
namespace GradedPaths
variable (P : GradedPaths ι G) (L : Subgroup G) [L.Normal]
variable (hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i)

end GradedPaths
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {H : Type uAction} {X : Type uPoint} [Fintype ι] [DecidableEq ι]
variable [Group H] [MulAction H X] [Fintype H] [Fintype X]

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators

noncomputable def permute {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ℓ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
@[simp] lemma permute_apply {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ))
    (x : EuclideanSpace ℝ (Fin ℓ)) (j : Fin ℓ) : permute σ x j=x (σ.symm j) := rfl
@[simp] lemma permute_one {ℓ : ℕ} (x : EuclideanSpace ℝ (Fin ℓ)) :
    permute 1 x=x := by ext j; rfl

end EuclideanRamsey

end

end OAI


