-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
-- name    : QEC_Coding_ExpanderCodes_LPSHeckePolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:28:38.479906+00:00
-- url     : https://prove2.me/theorems/5f5a6899-4b48-4891-96b5-b5af6c61fd11
-- title:
--   LPSHecke Polynomial
-- statement:
--   Definitions and structural lemmas for LPSHecke Polynomial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Polynomial
noncomputable def lpsHeckePolynomial
    (R : Type*) [CommRing R] (p : R) (n : ℕ) : R[X] :=
  Polynomial.dickson 2 p n
end QEC.Coding.TannerLiftedProduct


