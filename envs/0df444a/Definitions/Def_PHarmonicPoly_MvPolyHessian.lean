-- Prove2me | Definitions.Def_PHarmonicPoly_MvPolyHessian
-- name    : PHarmonicPoly_MvPolyHessian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T15:40:55.087818+00:00
-- url     : https://prove2.me/theorems/b69d6bd5-6c36-4a78-8fea-430796565909
-- title:
--   Mv Poly Hessian
-- statement:
--   Definitions and structural lemmas for Mv Poly Hessian, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyHessian.lean

module
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradient

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


