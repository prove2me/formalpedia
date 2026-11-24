-- Prove2me | Definitions.Def_PHarmonicPoly_MvPolyGradient
-- name    : PHarmonicPoly_MvPolyGradient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T14:58:42.306805+00:00
-- url     : https://prove2.me/theorems/f62626d1-9e63-4012-a7df-0ba11152922b
-- title:
--   Mv Poly Gradient
-- statement:
--   Definitions and structural lemmas for Mv Poly Gradient, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyGradient.lean

module
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Theorems.Thm_MvPolyFDeriv

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial ContinuousLinearMap InnerProductSpace


