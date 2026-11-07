-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:35:51.499748+00:00
-- url     : https://prove2.me/theorems/6036df40-b2d8-4220-9227-afd7d78b8ec3
-- title:
--   LPSOriginal Holomorphic Integral
-- statement:
--   Definitions and structural lemmas for LPSOriginal Holomorphic Integral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalHolomorphicMonicEquation (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C (((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N))⁻¹)) *
    lpsOriginalMeromorphicRatioEquation N k A (lpsOriginalMeromorphicDeltaPowerAtLevel N k)
end
end QEC.Coding.TannerLiftedProduct


