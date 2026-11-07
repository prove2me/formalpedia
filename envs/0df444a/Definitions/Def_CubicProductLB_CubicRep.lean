-- Prove2me | Definitions.Def_CubicProductLB_CubicRep
-- name    : CubicProductLB_CubicRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:49.238869+00:00
-- url     : https://prove2.me/theorems/6c389310-0879-45fd-89a5-a2a5d3cef096
-- title:
--   Cubic representations of $F_{p,n}$
-- statement:
--   A **cubic representation** of $F_{p,n}$ is a product representation whose factors have multilinear degree at most three on $X_n$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1, p.3

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep

namespace CubicProductLB

/-- A cubic representation of `F_{p,n}` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1, p.3). -/
abbrev CubicRep (p n : ℕ) := ProductRep 3 p n

end CubicProductLB


