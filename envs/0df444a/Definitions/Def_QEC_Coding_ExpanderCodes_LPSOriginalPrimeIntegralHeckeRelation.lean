-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:53:34.190472+00:00
-- url     : https://prove2.me/theorems/0a39c6ac-bbf1-4e97-a253-44a1fed18f9c
-- title:
--   LPSOriginal Prime Integral Hecke Relation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Integral Hecke Relation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalJNHolomorphicEvalZ (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* LPSOriginalHolomorphicRing :=
  Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicRing)
    (lpsOriginalJNHolomorphic N hN)
def lpsOriginalJNIntegerFractionEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* LPSOriginalHolomorphicFractionField :=
  (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
    (lpsOriginalJNHolomorphicEvalZ N hN)
def lpsOriginalIntegerNormalJN (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerAffineToNormal N hN
    (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))
def lpsOriginalIntegerNormalToHolomorphic (N : ℕ) (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact
    { toFun x := x.val.val
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
def lpsOriginalIntegerProductLevelCoefficientMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart (N*p) (Nat.mul_pos hN hp) :=
  (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN)
end
end QEC.Coding.TannerLiftedProduct


