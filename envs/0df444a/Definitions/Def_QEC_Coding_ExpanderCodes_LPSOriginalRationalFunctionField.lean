-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:56:36.300198+00:00
-- url     : https://prove2.me/theorems/c105add4-ecc7-4297-b00a-03546cb153b6
-- title:
--   LPSOriginal Rational Function Field
-- statement:
--   Definitions and structural lemmas for LPSOriginal Rational Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalJHolomorphicEvalQ : Polynomial ℚ →+* LPSOriginalHolomorphicRing :=
  lpsOriginalJHolomorphicEval.toRingHom.comp (Polynomial.mapRingHom (algebraMap ℚ ℂ))
lemma lpsOriginalJHolomorphicEvalQ_injective :
    Function.Injective lpsOriginalJHolomorphicEvalQ :=
  lpsOriginalJHolomorphicEval_injective.comp
    (Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective)
def lpsOriginalJFractionEmbeddingQ :
    FractionRing (Polynomial ℚ) →+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.lift (g:=(algebraMap LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField).comp lpsOriginalJHolomorphicEvalQ)
    ((IsFractionRing.injective LPSOriginalHolomorphicRing
      LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalQ_injective)
def lpsOriginalGeneratedFunctionFieldQ (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IntermediateField (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.adjoin (FractionRing (Polynomial ℚ))
    {lpsOriginalJNInFractionField N hN}
end
end QEC.Coding.TannerLiftedProduct


