-- Prove2me | Definitions.Def_PHarmonicPoly_TraceIdentity
-- name    : PHarmonicPoly_TraceIdentity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:02:24.769045+00:00
-- url     : https://prove2.me/theorems/6194a81f-cf74-471a-8f50-01ce51cd0092
-- title:
--   Trace Identity
-- statement:
--   Definitions and structural lemmas for Trace Identity, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TraceIdentity.lean

module
public import Definitions.Def_PHarmonicPoly_MaxPointDerivatives
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_MaxPointDerivatives

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


