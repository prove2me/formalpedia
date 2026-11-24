-- Prove2me | Definitions.Def_GaussianPerimeter_SphereSections
-- name    : GaussianPerimeter_SphereSections
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:23.243396+00:00
-- url     : https://prove2.me/theorems/3c67eef8-6ae9-4864-92ad-e2eb642ae6fa
-- title:
--   Sphere Sections
-- statement:
--   Definitions and structural lemmas for Sphere Sections, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereSections.lean

module
public import Definitions.Def_GaussianPerimeter_Sphere
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace GaussianPerimeter
local notation "Euc" n => EuclideanSpace ℝ (Fin n)
local notation "W" n => WithLp 2 (ℝ × Euc n)
local notation "axis" n => (WithLp.toLp 2 ((1 : ℝ), (0 : Euc n)))
end GaussianPerimeter


