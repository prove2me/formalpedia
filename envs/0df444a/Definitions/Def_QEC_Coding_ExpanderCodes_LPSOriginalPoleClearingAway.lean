-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:08:56.206687+00:00
-- url     : https://prove2.me/theorems/cbe17b64-8dd6-4b5d-9da2-acf8ddea5f7e
-- title:
--   LPSOriginal Pole Clearing Away
-- statement:
--   Definitions and structural lemmas for LPSOriginal Pole Clearing Away, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPoleClearingAway.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalPoleAwayDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalPoleAwayDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalPoleAwayDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalPoleAwayDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
end
end QEC.Coding.TannerLiftedProduct


