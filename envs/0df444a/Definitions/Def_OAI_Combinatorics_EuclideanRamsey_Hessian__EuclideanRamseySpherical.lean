-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:57:48.084603+00:00
-- url     : https://prove2.me/theorems/5d6bdb37-379a-46b7-9274-8723427ee2ed
-- title:
--   Splitting a vector space by a right inverse
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $E$ and $H$ be real vector spaces, and let $U:E\to H$ and $R:H\to E$ be linear maps with $U\circ R=\mathrm{id}_H$. This module defines the linear isomorphism
--   $$
--   \Phi:E\to H\times\ker U,\qquad\Phi(x)=\bigl(Ux,\;x-RUx\bigr),
--   $$
--   with inverse $(h,z)\mapsto Rh+z$. It records that the first component of $\Phi(x)$ is $Ux$, and that $\Phi(Ry)=(y,0)$ for every $y\in H$. The splitting identifies a space with the product of a horizontal factor, embedded by $R$, and a vertical factor $\ker U$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical

namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

end Trace

section MatrixContraction

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

def rightInverseSplit (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) : E ≃ₗ[ℝ] H × LinearMap.ker U where
  toFun x := (U x, ⟨x-R (U x), by
    change U (x-R (U x)) = 0
    simp only [map_sub, show U (R (U x)) = U x from LinearMap.congr_fun hUR (U x), sub_self]⟩)
  invFun v := R v.1 + v.2
  left_inv x := by simp
  right_inv v := by
    ext
    · simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
    · change R v.1 + (v.2:E) - R (U (R v.1 + v.2)) = v.2
      simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
      abel
  map_add' v w := by ext <;> simp [map_add] ; abel
  map_smul' c x := by ext <;> simp [map_smul, smul_sub]

@[simp] lemma rightInverseSplit_fst (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) (x : E) : (rightInverseSplit U R hUR x).1 = U x := rfl

@[simp] lemma rightInverseSplit_apply_R (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) (y : H) : (rightInverseSplit U R hUR (R y)) = (y,0) := by
  have h : U (R y) = y := LinearMap.congr_fun hUR y
  apply Prod.ext
  · exact h
  · apply Subtype.ext
    change R y - R (U (R y)) = 0
    rw [h, sub_self]

end Split

end EuclideanRamsey

end

end OAI


