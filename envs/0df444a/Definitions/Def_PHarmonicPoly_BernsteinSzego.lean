-- Prove2me | Definitions.Def_PHarmonicPoly_BernsteinSzego
-- name    : PHarmonicPoly_BernsteinSzego
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:39:36.136045+00:00
-- url     : https://prove2.me/theorems/3b8c7f66-2c4c-4ff8-8016-7eb28ec43433
-- title:
--   Bernstein Szego
-- statement:
--   Definitions and structural lemmas for Bernstein Szego, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/BernsteinSzego.lean

module
public import Definitions.Def_PHarmonicPoly_TrigPolyZeroCount
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_InteriorZeroOfSignChange
public import Definitions.Def_PHarmonicPoly_AngleOfUnitCirclePoint
public import Theorems.Thm_AngleOfUnitCirclePoint
public import Theorems.Thm_InteriorZeroOfSignChange
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolySmooth
public import Theorems.Thm_TrigPolyZeroCount

set_option autoImplicit false
@[expose] public section
@[expose] public section


