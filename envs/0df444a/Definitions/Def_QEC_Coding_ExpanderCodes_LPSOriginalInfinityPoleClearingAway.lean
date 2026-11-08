-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:02:53.205131+00:00
-- url     : https://prove2.me/theorems/1b264da5-8db9-41cf-a0f2-52eafda939d9
-- title:
--   LPSOriginal Infinity Pole Clearing Away
-- statement:
--   Definitions and structural lemmas for LPSOriginal Infinity Pole Clearing Away, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPoleClearingAway.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityPoleClearingAwayDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
end
end QEC.Coding.TannerLiftedProduct


