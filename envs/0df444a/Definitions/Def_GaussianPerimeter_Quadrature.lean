-- Prove2me | Definitions.Def_GaussianPerimeter_Quadrature
-- name    : GaussianPerimeter_Quadrature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:06:00.02488+00:00
-- url     : https://prove2.me/theorems/ccf97147-e75e-4866-b5f1-a9ce0d88230b
-- title:
--   Quadrature
-- statement:
--   Definitions and structural lemmas for Quadrature, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Quadrature.lean

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
open scoped Interval
namespace GaussianPerimeter
noncomputable def lowerBoundIntegrand (a b x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 - b * Real.exp (a ^ 2 * x))
local notation "a₀" => (6131 / 5000 : ℝ)
local notation "b₀" => (2387 / 1000 : ℝ)
local notation "F" => lowerBoundIntegrand a₀ b₀
end GaussianPerimeter


