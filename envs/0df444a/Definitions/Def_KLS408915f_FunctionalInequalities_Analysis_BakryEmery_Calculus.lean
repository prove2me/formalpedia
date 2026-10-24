-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:58:27.114637+00:00
-- url     : https://prove2.me/theorems/e99d62ac-95f9-48b3-a0a3-2bf2f0e9c3d8
-- title:
--   Pointwise differential calculus for finite-dimensional Hilbert spaces
-- statement:
--   `laplacian_eq_sum_fderiv_fderiv` expresses the Laplacian as the trace of the second Fréchet derivative in the fixed standard orthonormal basis, and `inner_gradient_eq_sum_fderiv_mul_fderiv` expands the inner product of two gradients in that basis. The bundle also proves continuity and compact-support preservation for Laplacians and gradients, and records the directional identities `fderiv_fderiv_apply`, `bilinearIteratedFDerivTwo_eq_fderiv_apply`, and `contDiff_fderiv_apply` under the stated differentiability assumptions. For $C^2$ functions, `bilinearIteratedFDerivTwo_norm_sq` and `bilinearIteratedFDerivTwo_add_quadratic` give the Hessian identities for $\|x\|^2$ and for adding $\frac\delta2\|x\|^2$, while `bilinearIteratedFDerivTwo_comp_affine` and `bilinearIteratedFDerivTwo_comp_clm` give the corresponding affine and continuous-linear chain rules.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean#L47-L398 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Calculus`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
section PointwiseTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
section Pointwise
omit [CompleteSpace E] in
/-- The Laplacian of a function on a finite-dimensional inner product space is the trace of its
second Fréchet derivative in the standard orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (f : E → ℝ) (x : E) :
    Laplacian.laplacian f x =
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  rfl
/-- The inner product of two gradients is the sum of the products of the directional
derivatives in the standard orthonormal basis. -/
theorem inner_gradient_eq_sum_fderiv_mul_fderiv (f g : E → ℝ) (x : E) :
    ⟪gradient f x, gradient g x⟫ =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ g x (stdOrthonormalBasis ℝ E i) := by
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_gradient_left, real_inner_comm, inner_gradient_left]
omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) := h1.continuous_fderiv one_ne_zero
  have : Laplacian.laplacian f = fun x =>
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    (h2.clm_apply continuous_const).clm_apply continuous_const
omit [CompleteSpace E] in
/-- The Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_laplacian {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (Laplacian.laplacian f) := by
  have : Laplacian.laplacian f = (fun A : E →L[ℝ] E →L[ℝ] ℝ =>
      ∑ i, A (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) ∘ fderiv ℝ (fderiv ℝ f) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact ((hfc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)
omit [FiniteDimensional ℝ E] in
/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
omit [FiniteDimensional ℝ E] in
/-- The gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_gradient {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gradient f) := by
  change HasCompactSupport ((toDual ℝ E).symm ∘ fderiv ℝ f)
  exact (hfc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)
end Pointwise
end PointwiseTools
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Directional
/-- The directional derivative `y ↦ D f (y) v` of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem contDiff_fderiv_apply {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (v : E) : ContDiff ℝ m (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const
/-- The directional derivative of a `C²` function is differentiable. -/
theorem differentiable_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) :
    Differentiable ℝ (fun y => fderiv ℝ f y v) :=
  (contDiff_fderiv_apply hf (m := 1) (by norm_num) v).differentiable one_ne_zero
/-- The second derivative applied to `v, w` is the derivative in direction `v` of the directional
derivative in direction `w`. -/
theorem fderiv_fderiv_apply {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [(hf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp
/-- The bilinear Hessian of a `C²` function as an iterated directional derivative:
`D²f(x)(v, w) = D (y ↦ D f (y) w) x v`. -/
theorem bilinearIteratedFDerivTwo_eq_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_fderiv_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)]
  rfl
end Directional
section Quadratic
/-- The Hessian of `‖·‖²` is `2⟪v, v⟫`. -/
theorem bilinearIteratedFDerivTwo_norm_sq (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y : E => ‖y‖ ^ 2) x v v = 2 * ‖v‖ ^ 2 := by
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (contDiff_norm_sq ℝ) x v v]
  have hfun : (fun y : E => fderiv ℝ (fun z : E => ‖z‖ ^ 2) y v) =
      fun y => 2 * ⟪y, v⟫ := by
    funext y
    rw [(hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv]
    simp
  rw [hfun]
  have h : HasFDerivAt (fun y : E => 2 * ⟪y, v⟫) ((2 : ℝ) • innerSL ℝ v) x := by
    simpa only [innerSL_apply_apply, real_inner_comm] using ((innerSL ℝ v).hasFDerivAt (x := x)).const_mul 2
  rw [h.fderiv]
  simp
/-- Adding `δ/2 ‖·‖²` adds `δ‖v‖²` to the Hessian quadratic form. -/
theorem bilinearIteratedFDerivTwo_add_quadratic {f : E → ℝ} (hf : ContDiff ℝ 2 f) (δ : ℝ) (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => f y + δ / 2 * ‖y‖ ^ 2) x v v =
      bilinearIteratedFDerivTwo ℝ f x v v + δ * ‖v‖ ^ 2 := by
  let q : E → ℝ := fun y => δ / 2 * ‖y‖ ^ 2
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hsum := iteratedFDeriv_add_apply (x := x) hf.contDiffAt hq.contDiffAt
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (f + q) x) ![v, v] = _
  rw [hsum]
  simp only [add_apply]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  have heq : bilinearIteratedFDerivTwo ℝ q x v v = δ / 2 *
      bilinearIteratedFDerivTwo ℝ (fun y : E => ‖y‖ ^ 2) x v v := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hq,
      bilinearIteratedFDerivTwo_eq_fderiv_apply (contDiff_norm_sq ℝ)]
    have hfun : (fun y => fderiv ℝ q y v) =
        fun y => δ / 2 * fderiv ℝ (fun z : E => ‖z‖ ^ 2) y v := by
      funext y
      dsimp only [q]
      rw [fderiv_const_mul]
      rfl
      exact (show ContDiff ℝ 2 (fun z : E => ‖z‖ ^ 2) from contDiff_norm_sq ℝ).differentiable (by norm_num) y
    rw [hfun, fderiv_const_mul]
    rfl
    exact differentiable_fderiv_apply (contDiff_norm_sq ℝ) v x
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, heq, bilinearIteratedFDerivTwo_norm_sq]
  ring
/-- Chain rule for the Hessian quadratic form under an affine change of variables `y ↦ L y + c`. -/
theorem bilinearIteratedFDerivTwo_comp_affine {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (L : E ≃L[ℝ] E) (c x u v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => V (L y + c)) x u v =
      bilinearIteratedFDerivTwo ℝ V (L x + c) (L u) (L v) := by
  have hA (y : E) : HasFDerivAt (fun z => L z + c) (L : E →L[ℝ] E) y :=
    L.hasFDerivAt.add_const c
  have hW : ContDiff ℝ 2 (fun y => V (L y + c)) :=
    hV.comp (L.contDiff.add contDiff_const)
  have hfirst (y : E) : fderiv ℝ (fun z => V (L z + c)) y =
      (fderiv ℝ V (L y + c)).comp (L : E →L[ℝ] E) :=
    ((hV.differentiable (by norm_num) (L y + c)).hasFDerivAt.comp y (hA y)).fderiv
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hW x u v,
    bilinearIteratedFDerivTwo_eq_fderiv_apply hV (L x + c) (L u) (L v)]
  have hfun : (fun y => fderiv ℝ (fun z => V (L z + c)) y v) =
      fun y => fderiv ℝ V (L y + c) (L v) := by
    funext y
    rw [hfirst]
    rfl
  rw [hfun]
  have hsecond := ((differentiable_fderiv_apply hV (L v) (L x + c)).hasFDerivAt.comp x (hA x)).fderiv
  exact congrArg (fun T : E →L[ℝ] ℝ => T u) hsecond
section CrossType
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- Chain rule for the Hessian form under a continuous linear map `T : F → E` (possibly between
different spaces). -/
theorem bilinearIteratedFDerivTwo_comp_clm {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (T : F →L[ℝ] E) (x u v : F) :
    bilinearIteratedFDerivTwo ℝ (fun y => V (T y)) x u v =
      bilinearIteratedFDerivTwo ℝ V (T x) (T u) (T v) := by
  have hW : ContDiff ℝ 2 (fun y => V (T y)) := hV.comp T.contDiff
  have hfirst (y : F) : fderiv ℝ (fun z => V (T z)) y =
      (fderiv ℝ V (T y)).comp T :=
    ((hV.differentiable (by norm_num) (T y)).hasFDerivAt.comp y T.hasFDerivAt).fderiv
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hW x u v,
    bilinearIteratedFDerivTwo_eq_fderiv_apply hV (T x) (T u) (T v)]
  have hfun : (fun y => fderiv ℝ (fun z => V (T z)) y v) =
      fun y => fderiv ℝ V (T y) (T v) := by
    funext y
    rw [hfirst]
    rfl
  rw [hfun]
  have hsecond := ((differentiable_fderiv_apply hV (T v) (T x)).hasFDerivAt.comp x T.hasFDerivAt).fderiv
  exact congrArg (fun S : F →L[ℝ] ℝ => S u) hsecond
end CrossType
end Quadratic
end DifferentialTools
end BakryEmery
end Analysis
end FunctionalInequalities


