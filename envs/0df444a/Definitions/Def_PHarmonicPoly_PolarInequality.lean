-- Prove2me | Definitions.Def_PHarmonicPoly_PolarInequality
-- name    : PHarmonicPoly_PolarInequality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:16:06.990441+00:00
-- url     : https://prove2.me/theorems/1796434c-0cf0-4913-9ad9-ddbdffb3f892
-- title:
--   Polar Inequality
-- statement:
--   Definitions and structural lemmas for Polar Inequality, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolarInequality.lean

module
public import Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_TangentialLaplacianBound

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial Real


