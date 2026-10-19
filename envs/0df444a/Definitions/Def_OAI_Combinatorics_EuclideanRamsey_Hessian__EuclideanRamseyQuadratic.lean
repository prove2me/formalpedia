-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:26:08.831522+00:00
-- url     : https://prove2.me/theorems/aef7bddb-5793-4eb3-af37-762ab05c1c13
-- title:
--   The Hessian bilinear form and the splitting $E\cong H\times\ker U$ given by a right inverse
-- statement:
--   This file defines the second-derivative bilinear form used in the smoothing estimates, and a linear-algebra splitting used to separate directions.
--
--   1. **Hessian bilinear form.** Let $E$ be a real normed space and $f:E\to\mathbb{R}$. For $x\in E$, $\nabla^2f(x)$ is the Fréchet derivative at $x$ of the map $y\mapsto Df(y)$, where $Df(y)$ is the Fréchet derivative of $f$ at $y$ (a continuous linear functional on $E$). Thus $\nabla^2f(x)$ is a continuous bilinear form on $E$,
--   $$\nabla^2f(x)(v,w)=\Bigl(D\bigl(y\mapsto Df(y)\bigr)(x)\,v\Bigr)\,w ,\qquad v,w\in E,$$
--   namely the derivative in direction $v$ of $y\mapsto Df(y)w$. For $f$ of class $C^2$ it is the usual symmetric Hessian form.
--   2. **Splitting by a right inverse.** Let $E$ and $H$ be real vector spaces and let $U:E\to H$ and $R:H\to E$ be linear maps with $U\circ R=\mathrm{id}_H$. Then
--   $$\Phi:E\to H\times\ker U,\qquad \Phi(x)=\bigl(Ux,\;x-RUx\bigr),$$
--   is a linear isomorphism, with inverse $\Phi^{-1}(h,z)=Rh+z$. The file records that the first component of $\Phi(x)$ is $Ux$ and that $\Phi(Ry)=(y,0)$ for every $y\in H$.
--
--   The Hessian form is the object to which the chain rule for linear maps, the product rule and the rules for functions on product spaces are applied when second-order operators of product test functions are computed. The splitting identifies a space with the product of a horizontal factor $H$, embedded by $R$, and a vertical factor $\ker U$. In the compact smoothing argument, $U$ is the map $x\mapsto Ux$ given by the $d\times k$ matrix in the weight $\|Ux\|^2$, and $R$ is given by $CU^{\mathsf T}$, where $C$ is a symmetric $k\times k$ matrix with $UCU^{\mathsf T}=I_d$, so that $UR=I_d$.
--
--   **Formalization Note** `hessianB f x` is `fderiv ℝ (fun y => fderiv ℝ f y) x : E →L[ℝ] E →L[ℝ] ℝ`; by Lean's convention `fderiv` is $0$ at points where a function is not differentiable. `rightInverseSplit U R hUR : E ≃ₗ[ℝ] H × LinearMap.ker U` is stated for arbitrary real modules, with simp lemmas `rightInverseSplit_fst` and `rightInverseSplit_apply_R`. Two further sections of the file contain no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic

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

def hessianB (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

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


