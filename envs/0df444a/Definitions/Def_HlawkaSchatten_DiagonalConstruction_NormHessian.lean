-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
-- name    : HlawkaSchatten_DiagonalConstruction_NormHessian
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:46:14.472761+00:00
-- url     : https://prove2.me/theorems/daa25aef-a910-411a-9aa5-0b52fd6aa634
-- title:
--   Directional derivatives and Hessian of the finite coordinate norm
-- statement:
--   Seven definitions give power sums and expressions for derivatives of the finite coordinate power functional along a line. They accept any real exponent $p$ and real vectors $v,h$ indexed by a finite type; their derivative interpretations require the hypotheses stated here.
--
--   `powerSum` is the unrooted power sum,
--   $$
--   \operatorname{powerSum}(p,v) = \sum_i |v_i|^p,
--   $$
--   so that $\|v\|_p = \operatorname{powerSum}(p,v)^{1/p}$ for $p>0$, where $\|\cdot\|_p$ denotes `DiagonalConstruction.lpNorm`, a norm for $p\ge1$.
--
--   For fixed $p,v$, `powerPair` is linear in the direction $h$:
--   $$
--   \operatorname{powerPair}(p,v,h) = \sum_i |v_i|^{p-2}\,v_i\,h_i.
--   $$
--   For $p>1$, the directional derivative of `powerSum` at $v$ along $h$ is $p\,\operatorname{powerPair}(p,v,h)$. The dependence on the base vector $v$ is generally nonlinear.
--
--   `powerQuad` is the associated quadratic form
--   $$
--   \operatorname{powerQuad}(p,v,h) = \sum_i |v_i|^{p-2}\,h_i^2,
--   $$
--   and `powerResidual` is the same quadratic form evaluated at $h$ after subtracting a multiple of $v$:
--   $$
--   \operatorname{powerResidual}(p,v,h,a) = \sum_i |v_i|^{p-2}\,(h_i-a\,v_i)^2.
--   $$
--
--   `radialCoefficient` is defined by the totalized quotient
--   $$
--   \operatorname{radialCoefficient}(p,v,h) = \frac{\operatorname{powerPair}(p,v,h)}{\operatorname{powerSum}(p,v)}.
--   $$
--   For $p>2$ and $v\neq0$, it is the unique value of $a$ minimizing $\operatorname{powerResidual}(p,v,h,a)$, as established by the source's residual identities and minimum theorem. This is a projection coefficient for the weighted quadratic form with weights $|v_i|^{p-2}$; that form can be degenerate when a coordinate of $v$ vanishes. The displayed definition itself places no restriction on $p$ or $v$.
--
--   For $p>1$ and $v\neq0$, `normSlope` is the first derivative at $t=0$ of the line $t\mapsto\|v+th\|_p$, and for $p>4$ and $v\neq0$, `normHessian` is its second derivative at $t=0$:
--   $$
--   \operatorname{normSlope}(p,v,h) = \operatorname{powerSum}(p,v)^{1/p-1}\,\operatorname{powerPair}(p,v,h),
--   $$
--   $$
--   \operatorname{normHessian}(p,v,h) = (p-1)\,\operatorname{powerSum}(p,v)^{1/p-1}\,\operatorname{powerResidual}\big(p,v,h,\operatorname{radialCoefficient}(p,v,h)\big).
--   $$
--
--   That `normSlope` is the derivative of $t\mapsto\|v+th\|_p$ for $p>1$ and $v\neq0$, and `normHessian` its second derivative for $p>4$ and $v\neq0$, is established by derivative theorems in the same source module. These seven definitions supply the curvature computation used, together with the coefficients of the `HessianBounds` bundle, to prove convexity of the Hlawka deficit on the cyclic coordinate box.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/NormHessian.lean#L16-L34

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Directional second derivatives of the finite real coordinate norm -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

noncomputable def powerSum (p : ℝ) (v : ι → ℝ) : ℝ := ∑ i, |v i| ^ p

noncomputable def powerPair (p : ℝ) (v h : ι → ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * v i * h i

noncomputable def powerQuad (p : ℝ) (v h : ι → ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * (h i) ^ 2

noncomputable def powerResidual (p : ℝ) (v h : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * (h i - a * v i) ^ 2

noncomputable def radialCoefficient (p : ℝ) (v h : ι → ℝ) : ℝ :=
  powerPair p v h / powerSum p v

noncomputable def normSlope (p : ℝ) (v h : ι → ℝ) : ℝ :=
  powerSum p v ^ (1 / p - 1) * powerPair p v h

noncomputable def normHessian (p : ℝ) (v h : ι → ℝ) : ℝ :=
  (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h (radialCoefficient p v h)









































end HlawkaSchatten.DiagonalConstruction


