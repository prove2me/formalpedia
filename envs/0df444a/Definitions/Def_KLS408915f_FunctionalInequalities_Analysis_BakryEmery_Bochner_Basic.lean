-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:00:04.079405+00:00
-- url     : https://prove2.me/theorems/ede03ccc-821e-4c35-b0d8-5196ffe9436f
-- title:
--   Convex Hessians and standard-basis Hessian squares
-- statement:
--   `convexOn_line` states that restricting a convex function $U$ to every affine line $t\mapsto x+t v$ remains convex, and `hasDerivAt_line`, `deriv_line`, and `deriv_deriv_line` identify its first and second one-dimensional derivatives with directional derivatives and the Hessian form. Thus `bilinearIteratedFDerivTwo_nonneg_of_convexOn` states that a $C^2$ convex function has nonnegative Hessian quadratic form $D^2U(x)(v,v)$. The definition `hessianSqStdBasis` is the fixed-standard-basis sum $\sum_i\sum_j(D^2f(x)(e_i,e_j))^2$; no basis-independence assertion is included.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L63-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section ConvexHessian
/-- The restriction of a convex function to a line is convex. -/
theorem convexOn_line {U : E → ℝ} (hU : ConvexOn ℝ Set.univ U) (x v : E) :
    ConvexOn ℝ Set.univ (fun t : ℝ => U (x + t • v)) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have h := hU.2 (Set.mem_univ (x + s • v)) (Set.mem_univ (x + t • v)) ha hb hab
  have hpt : x + (a • s + b • t) • v = a • (x + s • v) + b • (x + t • v) := by
    have hx : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hx]
    simp only [smul_add, smul_smul, add_smul, smul_eq_mul]
    abel
  simp only [smul_eq_mul] at hpt ⊢
  rw [hpt]
  exact h
/-- The line `t ↦ x + t v` has derivative `v`. -/
theorem hasDerivAt_line (x v : E) (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x
/-- The derivative of a `C¹` function along a line is the directional derivative. -/
theorem deriv_line {U : E → ℝ} (hU : ContDiff ℝ 1 U) (x v : E) :
    deriv (fun t : ℝ => U (x + t • v)) = fun t => fderiv ℝ U (x + t • v) v :=
  funext fun t =>
    ((hU.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line x v t)).deriv
/-- The second derivative at `0` of a `C²` function along the line `t ↦ x + t v` is the Hessian
`D²U(x)(v, v)`. -/
theorem deriv_deriv_line {U : E → ℝ} (hU : ContDiff ℝ 2 U) (x v : E) :
    deriv (deriv (fun t : ℝ => U (x + t • v))) 0 = bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [deriv_line (hU.of_le (by norm_num)) x v]
  have hU1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (m := 1) (by norm_num)
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ U (x + t • v)) (fderiv ℝ (fderiv ℝ U) x v) 0 := by
    have hd : HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) x) (x + (0 : ℝ) • v) := by
      rw [hx0]
      exact (hU1.differentiable one_ne_zero x).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line x v 0)
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have h4 : deriv (fun t : ℝ => fderiv ℝ U (x + t • v) v) 0 = fderiv ℝ (fderiv ℝ U) x v v := by
    simpa using h3.deriv
  rw [h4]
  rfl
/-- **convex Hessian positivity**: the Hessian of a `C²` convex function is positive semidefinite,
`0 ≤ D²U(x)(v, v)` for all `x v`. -/
theorem bilinearIteratedFDerivTwo_nonneg_of_convexOn {U : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) (x v : E) :
    0 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [← deriv_deriv_line hU x v]
  have hφ : ∀ t : ℝ, DifferentiableAt ℝ (fun t : ℝ => U (x + t • v)) t := fun t =>
    ((hU.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_line x v t)).differentiableAt
  have hmono : Monotone (deriv (fun t : ℝ => U (x + t • v))) :=
    monotoneOn_univ.mp (ConvexOn.monotoneOn_deriv (convexOn_line hconv x v) fun t _ => hφ t)
  exact hmono.deriv_nonneg
end ConvexHessian
section HessianSq
variable [FiniteDimensional ℝ E]
/-- The sum of the squared Hessian entries in the **fixed** standard orthonormal basis,
`∑ᵢ ∑ⱼ (D²f(x)(eᵢ, eⱼ))²`. Basis independence is not proved here; this is not yet an invariant
Hilbert–Schmidt norm. -/
def hessianSqStdBasis (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j,
    (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2
end HessianSq
end BakryEmery
end Analysis
end FunctionalInequalities


