-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
-- name    : QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:51:08.459688+00:00
-- url     : https://prove2.me/theorems/94a60f4e-b917-433b-a6af-068ed383fc57
-- title:
--   LPSCoset Section Domain
-- statement:
--   Definitions and structural lemmas for LPSCoset Section Domain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
def lpsCosetSectionDomain (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) : Set ℍ :=
  ⋃ c : lpsEffectiveModularGroup ⧸ H, (r c)⁻¹ • ModularGroup.fd
end
end QEC.Coding.TannerLiftedProduct


