-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:27:34.596826+00:00
-- url     : https://prove2.me/theorems/b78870ad-aac6-445c-b1fa-6c648e455d3d
-- title:
--   LPSOriginal Reciprocal Field Integral
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reciprocal Field Integral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local instance lpsOriginalReciprocalTransferDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local instance lpsOriginalReciprocalTransferDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalReciprocalTransferDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalReciprocalTransferDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalReciprocalCriterionDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local instance lpsOriginalReciprocalCriterionDictionary002 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalReciprocalCriterionDictionary003 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalReciprocalCriterionDictionary004 : IsScalarTower ℂ P K :=
  .of_algebraMap_eq' rfl
end
end QEC.Coding.TannerLiftedProduct


