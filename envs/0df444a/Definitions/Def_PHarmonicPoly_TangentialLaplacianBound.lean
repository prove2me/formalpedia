-- Prove2me | Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
-- name    : PHarmonicPoly_TangentialLaplacianBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:00:32.106169+00:00
-- url     : https://prove2.me/theorems/5639985a-01b1-4f48-94aa-eecfc604c7f3
-- title:
--   Tangential Laplacian Bound
-- statement:
--   Definitions and structural lemmas for Tangential Laplacian Bound, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TangentialLaplacianBound.lean

module
public import Definitions.Def_PHarmonicPoly_FrameHessian
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Definitions.Def_PHarmonicPoly_SecondDerivAtMaxNonpos
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_FrameHessian
public import Theorems.Thm_MvPolyContDiff
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_SecondDerivAtMaxNonpos

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


