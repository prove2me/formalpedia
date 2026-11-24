-- Prove2me | Definitions.Def_GaussianPerimeter_Radial
-- name    : GaussianPerimeter_Radial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:05:58.926256+00:00
-- url     : https://prove2.me/theorems/2f9b9aff-a812-4ab0-8cb8-42eb367560ef
-- title:
--   Radial
-- statement:
--   Definitions and structural lemmas for Radial, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Filter MeasureTheory Set
open scoped Topology
namespace GaussianPerimeter
@[expose]
noncomputable def radialKernel (n : ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun r => r ^ (n - 1) * Real.exp (-r ^ 2 / 2))
@[expose]
noncomputable def radialDensity (n : ℕ) (r : ℝ) : ℝ :=
  radialKernel n r / (∫ t : ℝ, radialKernel n t)
noncomputable def radialMode (n : ℕ) := Real.sqrt ((n - 1 : ℕ) : ℝ)
noncomputable def profileExponent (t w : ℝ) : ℝ :=
  t ^ 2 * Real.log (1 + w / t) - t * w - w ^ 2 / 2
noncomputable def radialProfile (n : ℕ) (w : ℝ) : ℝ :=
  if 0 < radialMode n + w then Real.exp (profileExponent (radialMode n) w) else 0
end GaussianPerimeter


