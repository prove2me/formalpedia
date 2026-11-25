-- Prove2me | Definitions.Def_PHarmonicPoly_FrameHessian
-- name    : PHarmonicPoly_FrameHessian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:46:23.776342+00:00
-- url     : https://prove2.me/theorems/a3e133ab-a042-4842-8e0c-da74666d292c
-- title:
--   Frame Hessian
-- statement:
--   Definitions and structural lemmas for Frame Hessian, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/FrameHessian.lean

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


