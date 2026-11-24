-- Prove2me | Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
-- name    : PHarmonicPoly_GreatCircleTrigPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T15:54:12.528693+00:00
-- url     : https://prove2.me/theorems/8065d879-0e5e-4a9a-8095-523aae072ebf
-- title:
--   Great Circle Trig Poly
-- statement:
--   Definitions and structural lemmas for Great Circle Trig Poly, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GreatCircleTrigPoly.lean

module
public import Definitions.Def_PHarmonicPoly_TrigPolyMul
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolyMul

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


