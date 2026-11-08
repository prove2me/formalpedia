-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
-- name    : QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:52:51.350233+00:00
-- url     : https://prove2.me/theorems/44bf00e2-8572-4b67-b087-23f6cc2f11ec
-- title:
--   LPSGamma0 Petersson Domain
-- statement:
--   Definitions and structural lemmas for LPSGamma0 Petersson Domain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
def lpsGamma0CosetSection (N : ℕ) :
    lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N → lpsEffectiveModularGroup :=
  fun c => (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
    (Quotient.out ((lpsEffectiveGamma0CosetEquiv N).symm c))
def lpsGamma0PeterssonDomain (N : ℕ) : Set ℍ :=
  lpsCosetSectionDomain (lpsEffectiveGamma0 N) (lpsGamma0CosetSection N)
end
end QEC.Coding.TannerLiftedProduct


