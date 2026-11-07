-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:10:32.542866+00:00
-- url     : https://prove2.me/theorems/b074c2fe-5eb1-4e6e-8888-facaaea7d85a
-- title:
--   LPSOriginal Rational Level Inclusion
-- statement:
--   Definitions and structural lemmas for LPSOriginal Rational Level Inclusion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalBivariateHolomorphicEval (M : ℕ) (hM : 0 < M) :
    Polynomial (Polynomial ℂ) →+* LPSOriginalHolomorphicRing :=
  Polynomial.eval₂RingHom lpsOriginalJHolomorphicEval.toRingHom
    (lpsOriginalJNHolomorphic M hM)
def lpsOriginalRationalMonomialHolomorphicSum
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) : LPSOriginalHolomorphicRing :=
  ∑ i, algebraMap ℚ LPSOriginalHolomorphicRing (a i) *
    lpsOriginalJHolomorphic ^ u i * lpsOriginalJNHolomorphic M hM ^ v i
def lpsOriginalFiniteClearedRationalSum
    {ι : Type*} [Fintype ι] (M B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) : ℂ → ℂ :=
  ∑ i, fun q => (a i : ℂ) * lpsOriginalClearedMonomial M B (u i) (v i) q
def lpsOriginalFiniteClearedComplexSum
    {ι : Type*} [Fintype ι] (M B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) : ℂ → ℂ :=
  ∑ i, fun q => a i * lpsOriginalClearedMonomial M B (u i) (v i) q
abbrev LPSOriginalBivariateSupport (P : Polynomial (Polynomial ℂ)) :=
  (k : P.support) × (P.coeff k.val).support
instance lpsOriginalBivariateSupport_fintype (P : Polynomial (Polynomial ℂ)) :
    Fintype (LPSOriginalBivariateSupport P) :=
  inferInstanceAs (Fintype ((k : P.support) × (P.coeff k.val).support))
end
end QEC.Coding.TannerLiftedProduct


