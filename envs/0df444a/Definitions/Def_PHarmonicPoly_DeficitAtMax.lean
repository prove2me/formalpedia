-- Prove2me | Definitions.Def_PHarmonicPoly_DeficitAtMax
-- name    : PHarmonicPoly_DeficitAtMax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:22:27.750036+00:00
-- url     : https://prove2.me/theorems/fb97341b-dfb7-44ad-9138-fe8348a24da3
-- title:
--   Deficit At Max
-- statement:
--   Definitions and structural lemmas for Deficit At Max, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitAtMax.lean

module
public import Definitions.Def_PHarmonicPoly_TraceIdentity
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_DeficitBound
public import Theorems.Thm_DeficitBound
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_GreatCircleTrigPoly
public import Theorems.Thm_TraceIdentity

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


