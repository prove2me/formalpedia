-- Prove2me | Definitions.Def_GaussianPerimeter_Averaging
-- name    : GaussianPerimeter_Averaging
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:42.056273+00:00
-- url     : https://prove2.me/theorems/e642a7a6-6522-4def-be07-8eb9dee43000
-- title:
--   Averaging
-- statement:
--   Definitions and structural lemmas for Averaging, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Averaging.lean

module
public import Definitions.Def_GaussianPerimeter_Geometry
public import Definitions.Def_GaussianPerimeter_Sphere
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
namespace GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1
@[expose]
noncomputable def facetAcceptanceProbability (k : ℕ) (ρ r : ℝ) : ℝ≥0∞ :=
  uniformSphere (Euc (k + 1))
    {v | ⟪Real.sqrt (ρ ^ 2 + r ^ 2) • (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0),
      v.val⟫_ℝ < ρ}
end GaussianPerimeter


