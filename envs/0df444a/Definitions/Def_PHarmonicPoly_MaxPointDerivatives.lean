-- Prove2me | Definitions.Def_PHarmonicPoly_MaxPointDerivatives
-- name    : PHarmonicPoly_MaxPointDerivatives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:46:15.41935+00:00
-- url     : https://prove2.me/theorems/4f8861c0-aacf-41b8-9ab3-ddb89fb372dd
-- title:
--   Max Point Derivatives
-- statement:
--   Definitions and structural lemmas for Max Point Derivatives, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MaxPointDerivatives.lean

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_MvPolyFDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial


