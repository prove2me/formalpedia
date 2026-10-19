-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:59:27.051969+00:00
-- url     : https://prove2.me/theorems/1699ab4d-4e47-42ad-b302-0758434e8aeb
-- title:
--   Rescaling the vertical factor of a product space
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $H$ and $V$ be finite-dimensional real normed spaces and let $t\ne0$. This module defines the continuous linear automorphism
--   $$
--   \sigma_t:H\times V\to H\times V,\qquad\sigma_t(h,v)=(h,tv),
--   $$
--   whose inverse is $\sigma_{1/t}$. It records the formula for $\sigma_t$ on pairs. Rescaling the vertical directions is used when differential operators are split into horizontal and vertical parts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical

namespace OAI

universe uDomain uAction uVertical uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Operator
variable {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

end Operator

section Scale
variable (H : Type uAction) (V : Type uVertical) [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]

def scaleVertical (t : ℝ) (ht : t ≠ 0) : (H×V) ≃L[ℝ] H×V :=
  (show (H×V) ≃ₗ[ℝ] H×V from {
    toFun := fun x => (x.1,t • x.2)
    invFun := fun x => (x.1,t⁻¹ • x.2)
    left_inv := by intro x; simp [smul_smul, ht]
    right_inv := by intro x; simp [smul_smul, ht]
    map_add' := by intro x y; simp [smul_add]
    map_smul' := by intro c x; ext <;> simp [smul_smul, mul_comm]
  }).toContinuousLinearEquiv

@[simp] lemma scaleVertical_apply (t : ℝ) (ht : t ≠ 0) (x : H×V) :
    scaleVertical H V t ht x = (x.1,t • x.2) := rfl

end Scale

section SplitDifferential
variable {k d : ℕ} {H : Type uAction} {V : Type uVertical}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

end SplitDifferential
end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

end EuclideanRamsey

end

end OAI


