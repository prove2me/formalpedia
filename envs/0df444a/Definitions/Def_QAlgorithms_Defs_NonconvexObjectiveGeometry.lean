-- Prove2me | Definitions.Def_QAlgorithms_Defs_NonconvexObjectiveGeometry
-- name    : QAlgorithms_Defs_NonconvexObjectiveGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:06.165816+00:00
-- url     : https://prove2.me/theorems/6f8becf5-4c47-4bb1-9a07-7ad78f8e4aa3
-- title:
--   NonconvexObjectiveGeometry
-- statement:
--   NonconvexObjectiveGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NonconvexObjectiveGeometry.lean

import Mathlib

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Nonconvex

/-- Implementation helper; source: arxiv-2007.10253v3 PDF p.2. -/
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The selfadjoint real operator/matrix computed from the Frechet derivative of gradient f on EuclideanSpace R (Fin n), with global twice differentiability. It is not an arbitrary Hessian field constrained by one numerical bound. Source: arxiv-2007.10253v3 PDF p.2; arxiv-2007.10253v3 PDF p.13. -/
def hessian {d : ℕ} (f : Vector d → ℝ) (x : Vector d) : Vector d →L[ℝ] Vector d :=
  fderiv ℝ (gradient f) x

/-- Twice differentiability and the two global inequalities of p.2, with Euclidean gradient norm and operator Hessian norm, positive ell,rho. Hessian Lipschitzness implies its continuity; do not require analytic or C-infinity f. Source: arxiv-2007.10253v3 PDF p.2. -/
def IsSmoothHessianLipschitz {d : ℕ} (f : Vector d → ℝ) (ell rho : ℝ) : Prop :=
  0 < d ∧ 0 < ell ∧ 0 < rho ∧ Differentiable ℝ f ∧ Differentiable ℝ (gradient f) ∧
    (∀ x y, ‖gradient f x-gradient f y‖ ≤ ell*‖x-y‖) ∧
    ∀ x y, ‖hessian f x-hessian f y‖ ≤ rho*‖x-y‖

/-- Conjunction in Eq.(1). The Hessian inequality may equivalently quantify all real directions v: <v,Hess f(x)v> >= -sqrt(rho epsilon)||v||^2, with actual Hessian and positive-dimensional/differentiability guards. Source: arxiv-2007.10253v3 PDF p.2. -/
def IsApproxSecondOrderStationary {d : ℕ} (f : Vector d → ℝ) (rho eps : ℝ) (x : Vector d) : Prop :=
  0 < d ∧ 0 < rho ∧ 0 < eps ∧ Differentiable ℝ f ∧ Differentiable ℝ (gradient f) ∧
    ‖gradient f x‖ ≤ eps ∧ ∀ v, -Real.sqrt (rho*eps)*‖v‖^2 ≤ inner ℝ v (hessian f x v)

/-- Define f* as the actual minimum value under existence of a minimizer, and Delta=f(x0)-f*. Include finite lower boundedness/attainment before using real infima. Zero gap is a separate immediate-output branch before any schedule division. Source: arxiv-2007.10253v3 PDF p.16; arxiv-2007.10253v3 PDF p.18; arxiv-2007.10253v3 PDF p.23. -/
def minimumValue {d : ℕ} (f : Vector d → ℝ) (attained : ∃ x, ∀ y, f x ≤ f y) : ℝ :=
  f attained.choose

/-- Delta=f(x0)-minimumValue(f), where minimumValue is the actual attained global minimum. Guard attainment before real infimum and handle Delta=0 without schedule divisions. Source: arxiv-2007.10253v3 PDF p.16; arxiv-2007.10253v3 PDF p.18; arxiv-2007.10253v3 PDF p.23. -/
def initialGap {d : ℕ} (f : Vector d → ℝ) (attained : ∃ x, ∀ y, f x ≤ f y) (x0 : Vector d) : ℝ :=
  f x0-minimumValue f attained

example {d : ℕ} (f : Vector d → ℝ) (attained : ∃ x, ∀ y, f x ≤ f y) (x0 : Vector d) :
    0 ≤ initialGap f attained x0 := sub_nonneg.mpr (attained.choose_spec x0)

end QAlgorithms.Nonconvex


