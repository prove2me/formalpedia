-- Prove2me | Definitions.Def_GaussianPerimeter_NazarovLimit
-- name    : GaussianPerimeter_NazarovLimit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:09:04.316665+00:00
-- url     : https://prove2.me/theorems/1bb4df24-eaa5-41f5-8905-b7294b2d9132
-- title:
--   Nazarov Limit
-- statement:
--   Definitions and structural lemmas for Nazarov Limit, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Filter MeasureTheory
open scoped ENNReal Topology
namespace GaussianPerimeter
@[expose] noncomputable def shiftedRadialDensity (n : ℕ) (w : ℝ) : ℝ :=
  radialDensity n (Real.sqrt ((n : ℝ) - 1) + w)
@[expose] noncomputable def shiftedCapTail (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if 2 ≤ n then capTail n (capThreshold a n w) else 0
end GaussianPerimeter


