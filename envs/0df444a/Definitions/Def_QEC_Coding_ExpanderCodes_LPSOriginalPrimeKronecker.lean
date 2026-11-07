-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:20:31.256214+00:00
-- url     : https://prove2.me/theorems/29a18589-995c-41b3-862c-f7be8acd5026
-- title:
--   LPSOriginal Prime Kronecker
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Kronecker, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalModPrimeJPolynomialEval (p : ℕ) [Fact p.Prime] :
    Polynomial (ZMod p) →+* lpsOriginalCuspSeriesRing (ZMod p) :=
  Polynomial.eval₂RingHom
    ((algebraMap (PowerSeries (ZMod p)) (lpsOriginalCuspSeriesRing (ZMod p))).comp PowerSeries.C)
    (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)
end
end QEC.Coding.TannerLiftedProduct


