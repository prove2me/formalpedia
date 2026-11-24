-- Prove2me | Definitions.Def_PHarmonicPoly_EpAlg
-- name    : PHarmonicPoly_EpAlg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T14:13:47.604189+00:00
-- url     : https://prove2.me/theorems/64ad92b5-41ab-408c-8e27-8409b7ae922f
-- title:
--   Ep Alg
-- statement:
--   Definitions and structural lemmas for Ep Alg, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpAlg.lean

module
public import Definitions.Def_PHarmonicPoly_Preamble
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MvPolynomial
noncomputable def EpAlg {n : ℕ} (p : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (∑ i, (pderiv i P) ^ 2) * (∑ i, pderiv i (pderiv i P))
    + C (p - 2) * ∑ i, ∑ j, pderiv i (pderiv j P) * pderiv i P * pderiv j P


