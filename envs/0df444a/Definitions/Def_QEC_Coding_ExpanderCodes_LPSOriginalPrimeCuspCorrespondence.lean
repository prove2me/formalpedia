-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:17:41.750005+00:00
-- url     : https://prove2.me/theorems/d629f101-4ba6-4d5c-b2a3-1f791a6ad230
-- title:
--   LPSOriginal Prime Cusp Correspondence
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Cusp Correspondence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalAnalyticPrimeBranch (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    lpsOriginalAnalyticCuspLaurentRing :=
  match i with
  | none => lpsOriginalAnalyticCuspAffineBranch (p*p)
      (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos) 0
  | some m => lpsOriginalAnalyticCuspAffineBranch 1 (by decide) ((m.val:ℚ)/p)
def lpsOriginalAnalyticPrimeJ (p : ℕ) [Fact p.Prime] :
    lpsOriginalAnalyticCuspLaurentRing :=
  lpsOriginalAnalyticCuspAffineBranch p (Fact.out : p.Prime).pos 0
def lpsOriginalAnalyticPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalAnalyticCuspLaurentRing :=
  Polynomial.eval₂RingHom (Int.castRingHom lpsOriginalAnalyticCuspLaurentRing)
    (lpsOriginalAnalyticPrimeJ p)
def lpsOriginalCyclotomicPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) :=
  Polynomial.eval₂RingHom
    (Int.castRingHom (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p)))
    (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) p (Fact.out : p.Prime).ne_zero)
def lpsOriginalModPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (ZMod p) :=
  Polynomial.eval₂RingHom (Int.castRingHom (lpsOriginalCuspSeriesRing (ZMod p)))
    (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)
end
end QEC.Coding.TannerLiftedProduct


