-- Prove2me | Definitions.Def_GaussianPerimeter_Construction
-- name    : GaussianPerimeter_Construction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:09:42.276931+00:00
-- url     : https://prove2.me/theorems/f1849ac5-0e91-444c-b471-3966ba1c0230
-- title:
--   Construction
-- statement:
--   Definitions and structural lemmas for Construction, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Construction.lean

module
public import Definitions.Def_GaussianPerimeter_Averaging
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Definitions.Def_GaussianPerimeter_RadialIntegration
public import Definitions.Def_GaussianPerimeter_SphereCap
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace GaussianPerimeter
end GaussianPerimeter


