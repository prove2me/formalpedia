-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:06:56.424351+00:00
-- url     : https://prove2.me/theorems/a8394fb8-e689-4bcd-bf90-a879d865feae
-- title:
--   LPSOriginal JPower Pole Clearing
-- statement:
--   Definitions and structural lemmas for LPSOriginal JPower Pole Clearing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPowerPoleClearing.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalJPowerClearingDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalJPowerClearingDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalJPowerClearingDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalJPowerClearingDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
end
end QEC.Coding.TannerLiftedProduct


