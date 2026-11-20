-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:56:02.722353+00:00
-- url     : https://prove2.me/theorems/9d37f0b9-21d0-46a4-8fb5-9ade8e75f3bf
-- title:
--   LPSOriginal Integral Dual Relation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Dual Relation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
def lpsOriginalIntegerNormalBaseCoefficientMap
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact (lpsOriginalIntegerAffineToNormal N hN).toRingHom.comp
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN))
def lpsOriginalIntegerNormalJ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN :=
  lpsOriginalIntegerNormalBaseCoefficientMap N hN Polynomial.X
def lpsOriginalIntegerNormalZeroToGaussAffineOrder
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* LPSOriginalGaussAffineOrder N hN p := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  exact (lpsOriginalGaussNormalizationEquiv N hN p hpN).symm.toRingHom.comp
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)
end
end QEC.Coding.TannerLiftedProduct


