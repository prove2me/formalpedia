-- Prove2me | Definitions.Def_PHarmonicPoly_EpOpEvalPoly
-- name    : PHarmonicPoly_EpOpEvalPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:45:06.097804+00:00
-- url     : https://prove2.me/theorems/ab711b2d-e7a7-4b92-a0c5-a60f1980b0cb
-- title:
--   Ep Op Eval Poly
-- statement:
--   Definitions and structural lemmas for Ep Op Eval Poly, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpOpEvalPoly.lean

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpOp
public import Definitions.Def_PHarmonicPoly_MvPolyLaplacian
public import Theorems.Thm_MvPolyLaplacian

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


