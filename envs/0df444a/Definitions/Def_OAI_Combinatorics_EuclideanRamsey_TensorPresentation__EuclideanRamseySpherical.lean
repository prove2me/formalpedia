-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:04:56.044136+00:00
-- url     : https://prove2.me/theorems/fc5d64b0-3902-41cd-a693-202ea3887239
-- title:
--   Real arrays as tensors of affine vectors
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   An affine vector of size $d$ is a function $w:\{0,1,\dots,d\}\to\mathbb R$, where the index $0$ stands for the constant term. Let $T=\mathbb R\otimes_{\mathbb Q}\mathbb R$. This module defines the $\mathbb Q$-linear isomorphism between the tensor product of two copies of the space of affine vectors over $\mathbb Q$ and the space of real arrays, matrices indexed by $\{0,\dots,d\}^2$ with entries in $T$. It sends a pure tensor $w\otimes z$ to the array
--   $$
--   (w\otimes z)_{\alpha\beta}=w_\alpha\otimes z_\beta .
--   $$
--   It lets rank-one test arrays be manipulated as tensors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean by skeleton subtraction
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

-- TensorProduct.inductionOn (the Lean 4.34 two-case eliminator) is already backported in the imported
-- module OAI.Combinatorics.EuclideanRamsey.TensorDescent.

namespace OAI

universe uVector

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

open scoped TensorProduct RealInnerProductSpace
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct BigOperators

abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ

def affineArray {d : ℕ} :
    (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) (fun _ : Option (Fin d) => ℝ)).trans
    (LinearEquiv.piCongrRight (fun _ => TensorProduct.piRight ℚ ℚ ℝ (fun _ : Option (Fin d) => ℝ)))

@[simp] lemma affineArray_tmul {d : ℕ} (w z : AffineVector d) (α β : Option (Fin d)) :
    affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := by
  rfl

end EuclideanRamsey

open scoped TensorProduct BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped TensorProduct
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

end EuclideanRamsey

end

end OAI


