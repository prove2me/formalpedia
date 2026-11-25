-- Prove2me | Definitions.Def_PHarmonicPoly_GradientEuler
-- name    : PHarmonicPoly_GradientEuler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:32:17.804883+00:00
-- url     : https://prove2.me/theorems/9ea46fb5-7722-4c77-ab79-74bb8d466204
-- title:
--   Gradient Euler
-- statement:
--   Definitions and structural lemmas for Gradient Euler, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GradientEuler.lean

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_MvPolyHessian

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


