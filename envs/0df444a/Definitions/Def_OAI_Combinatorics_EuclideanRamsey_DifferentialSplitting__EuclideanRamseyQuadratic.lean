-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:27:40.75931+00:00
-- url     : https://prove2.me/theorems/21b1dc67-54df-4b2a-b157-f992087c378b
-- title:
--   Constant-coefficient second-order operators along given directions and vertical rescaling of $H\times V$
-- statement:
--   This file defines a constant-coefficient second-order differential operator along prescribed directions, and the linear rescaling used to separate horizontal and vertical directions.
--
--   1. **Second-order operator along directions.** Let $E$ be a real normed space, $k\in\mathbb{N}$, $C=(C_{jl})$ a real $k\times k$ matrix and $v_1,\dots,v_k\in E$. For $f:E\to\mathbb{R}$ and $x\in E$,
--   $$L_{C,v}f(x)=\frac12\sum_{j=1}^{k}\sum_{l=1}^{k}C_{jl}\,\nabla^2f(x)(v_j,v_l),$$
--   where $\nabla^2f(x)$ is the Hessian bilinear form of $f$ at $x$, i.e. the Fréchet derivative at $x$ of $y\mapsto Df(y)$.
--   2. **Vertical rescaling.** Let $H$ and $V$ be finite-dimensional real normed spaces and let $t\neq0$ be a real number. Then
--   $$\Sigma_t:H\times V\to H\times V,\qquad \Sigma_t(h,z)=(h,\,tz),$$
--   is a continuous linear automorphism of $H\times V$, with inverse $(h,z)\mapsto(h,t^{-1}z)$. The formula $\Sigma_t(h,z)=(h,tz)$ is recorded as a simplification rule.
--
--   When $E=\mathbb{R}^k$ and $v_j=e_j$ are the standard basis vectors, $L_{C,v}$ is the operator $\tfrac12\sum_{j,l}C_{jl}\partial_j\partial_l$. In the smoothing construction, $\mathbb{R}^k$ is identified linearly with a product $H\times V$ of a horizontal and a vertical factor, and test functions of the form $f(h)\,g(tz)$ are considered, where $(h,z)$ are the coordinates of the point and $(h,tz)=\Sigma_t(h,z)$. When $C$ splits compatibly with this decomposition, the operator of such a function is the half-Laplacian of $f$ in the horizontal variables (multiplied by $g$) plus $t^2$ times a second-order operator of $g$ in the vertical variables (multiplied by $f$), so the vertical contribution can be made small by taking $t$ small.
--
--   **Formalization Note** `secondOperator C v f x` is `(1/2) * ∑ j, ∑ l, C j l * hessianB f x (v j) (v l)`, and `scaleVertical H V t ht : (H × V) ≃L[ℝ] H × V` takes the hypothesis `ht : t ≠ 0`; it is obtained from the linear equivalence by `toContinuousLinearEquiv`, which uses the finite dimensionality. Its simp lemma is `scaleVertical_apply`. The splitting formula described above is proved separately, and the remaining sections of the file are empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic

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

def secondOperator (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E)
    (f : E → ℝ) (x : E) : ℝ :=
  (1/2:ℝ)*∑ j, ∑ l, C j l*hessianB f x (v j) (v l)

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


