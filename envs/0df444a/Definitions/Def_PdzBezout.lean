-- Prove2me | Definitions.Def_PdzBezout
-- name    : PdzBezout
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-17T01:35:29.672888+00:00
-- url     : https://prove2.me/theorems/eaaa675a-245a-4268-9a4f-18abf36f0aa0
-- title:
--   Bézout-layer plane setup: singularities and implicit-function adapter
-- statement:
--   The Bézout half's setup on top of the preliminaries bundle (imports `Definitions.Def_PdzPrelim`). It contains, inside `namespace PachDeZeeuw.Algebraic`:
--
--   - the implicit-function adapter section, with its variables over an `RCLike` field and complete normed spaces, and the noncomputable definition `cdImplicitFunction`, which wraps `ContDiffAt.implicitFunction` for a `ContDiffAt` proof with an invertible second-variable derivative;
--   - `SingularPointSet p`, the set of points of $\mathrm{PlaneCurveZeroSet}\,p$ at which both partial derivatives $\mathrm{pderiv}\,0\,p$ and $\mathrm{pderiv}\,1\,p$ evaluate to zero;
--   - `evalPlane p : ℝ × ℝ → ℝ`, the evaluation of $p$ at a pair of reals, used in the implicit-function argument;
--   - `mkPoint2 x y`, the point of $\mathrm{Point2}$ with coordinates $x, y$;
--   - `swapPoint z`, the point with the two coordinates of $z$ exchanged.
--
--   The abbreviation `PlanePoly`, the predicate `NoCommonCurveComponent` and the proposition `BezoutFiniteIntersectionStatement` are not defined here; they live in the preliminaries bundle `PdzPrelim`.
-- source:
--   Definitions supporting the formalization of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), Theorem 2.1; definition bundle skeleton-subtracted from https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L67-L460

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import Definitions.Def_PdzPrelim

/-!
# Bézout finite-intersection bound for real plane curves

This module discharges `PachDeZeeuw.Algebraic.BezoutFiniteIntersectionStatement`
(Pach--de Zeeuw, Theorem 2.1): two bounded-degree real plane curves with no
shared infinite irreducible component meet in a finite set whose cardinality is
bounded by a constant depending only on the two degrees. The achievable
existential constant proven here is `(d₁ + d₂ + 1) ^ 8`, obtained by a resultant
/ Sylvester-matrix elimination argument summed over the normalized irreducible
factor pairs.

This is the crude existential form. The sharp `d₁ · d₂` bound is **not**
proven here (it is not stated anywhere — see `ROADMAP.md`).

All supporting lemmas live in `namespace PachDeZeeuw.Algebraic` so they can see
the elimination / resultant machinery already established in `AlgebraicPrelim`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 16000000

namespace PachDeZeeuw.Algebraic

open EuclideanGeometry
open scoped Topology

/-! ### Implicit-function adapter

The v4.27 mathlib used `IsContDiffImplicitAt.implicitFunction` /
`IsContDiffImplicitAt.apply_implicitFunction` as projections of the
`IsContDiffImplicitAt` predicate. In v4.30 the implicit-function API moved to the
`ContDiffAt` namespace. The adapters below use the current API directly while
keeping the geometric argument below in the same projection style. -/
section ImplicitAdapter

variable {𝕜 E₁ E₂ F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F} {a : E₁ × E₂} {n : WithTop ℕ∞}



/-- The implicit function attached to a `ContDiffAt` proof and an invertible
second-variable derivative. -/
noncomputable def cdImplicitFunction (hf : ContDiffAt 𝕜 n f a) (hn : n ≠ 0)
    (hinv : ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible) :
    E₁ → E₂ :=
  hf.implicitFunction hn hinv



end ImplicitAdapter













/-! ## Singularity helpers -/

/-- The singular point set of a plane polynomial. -/
def SingularPointSet (p : PlanePoly) : Set Point2 :=
  PlaneCurveZeroSet p ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) p) = 0} ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) p) = 0}

/-- The standard plane evaluation map used in the implicit-function argument. -/
noncomputable def evalPlane (p : PlanePoly) : ℝ × ℝ → ℝ :=
  fun xy => MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p

/-- Build a plane point from its two coordinates. -/
noncomputable def mkPoint2 (x y : ℝ) : Point2 :=
  WithLp.toLp 2 ![x, y]

/-- Swap the two coordinates of a point in the plane. -/
noncomputable def swapPoint (z : Point2) : Point2 :=
  mkPoint2 (z 1) (z 0)











































end PachDeZeeuw.Algebraic


