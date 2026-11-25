-- Prove2me | Definitions.Def_PHarmonicPoly_MainTheorem
-- name    : PHarmonicPoly_MainTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:02:13.653242+00:00
-- url     : https://prove2.me/theorems/e2575eda-6c24-50cc-b87a-c3d76918cd04
-- title:
--   Main Theorem
-- statement:
--   Definitions and structural lemmas for Main Theorem, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MainTheorem.lean

module
public import Definitions.Def_PHarmonicPoly_HomogeneousCase
public import Definitions.Def_PHarmonicPoly_TopComponent
public import Definitions.Def_PHarmonicPoly_TopComponentNeZero
public import Definitions.Def_PHarmonicPoly_AffineOfTotalDegreeLeOne
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Theorems.Thm_AffineOfTotalDegreeLeOne
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_HomogeneousCase
public import Theorems.Thm_TopComponent
public import Theorems.Thm_TopComponentNeZero

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


