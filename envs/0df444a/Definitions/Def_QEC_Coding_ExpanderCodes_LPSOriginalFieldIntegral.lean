-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:59:50.213039+00:00
-- url     : https://prove2.me/theorems/e656d716-cfce-4084-b49d-b179691b0734
-- title:
--   LPSOriginal Field Integral
-- statement:
--   Definitions and structural lemmas for LPSOriginal Field Integral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFieldIntegral.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalFieldIntegralDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
local instance lpsOriginalFieldIntegralDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalFieldIntegralDictionary003 : Algebra P E := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp (algebraMap P J)).toAlgebra
def lpsOriginalGeneratedRestrictionPolynomialAlgEquiv : K ≃ₐ[P] E :=
  { lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN with
    commutes' p := by apply Subtype.ext; rfl }
end
end QEC.Coding.TannerLiftedProduct


