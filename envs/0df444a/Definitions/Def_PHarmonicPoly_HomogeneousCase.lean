-- Prove2me | Definitions.Def_PHarmonicPoly_HomogeneousCase
-- name    : PHarmonicPoly_HomogeneousCase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:39:24.79992+00:00
-- url     : https://prove2.me/theorems/c2fdb02e-58bb-4953-a9c4-5e542ed7c04d
-- title:
--   Homogeneous Case
-- statement:
--   Definitions and structural lemmas for Homogeneous Case, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/HomogeneousCase.lean

module
public import Definitions.Def_PHarmonicPoly_PolarInequality
public import Definitions.Def_PHarmonicPoly_PolarContradiction
public import Definitions.Def_PHarmonicPoly_SphereMaxNormalize
public import Definitions.Def_PHarmonicPoly_LatitudeMaximizer
public import Definitions.Def_PHarmonicPoly_DeficitAtMax
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Definitions.Def_PHarmonicPoly_BernsteinSzegoSecond
public import Definitions.Def_PHarmonicPoly_CotBound
public import Theorems.Thm_BernsteinSzegoSecond
public import Theorems.Thm_CotBound
public import Theorems.Thm_DeficitAtMax
public import Theorems.Thm_GreatCircleTrigPoly
public import Theorems.Thm_LatitudeMaximizer
public import Theorems.Thm_PolarContradiction
public import Theorems.Thm_PolarInequality
public import Theorems.Thm_SphereMaxNormalize

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial Real


