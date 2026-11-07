-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
-- name    : QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:48:38.873831+00:00
-- url     : https://prove2.me/theorems/b111262d-89d8-4c18-ab9c-80e33671e26b
-- title:
--   LPSCharacter Eisenstein Cusps
-- statement:
--   Definitions and structural lemmas for LPSCharacter Eisenstein Cusps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsChi4EisensteinCuspConstant (γ : SL(2,ℤ)) : ℂ :=
  if γ 1 0%8=4 then 3*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*
    lpsChi4E2Character (((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4) else 0
noncomputable def lpsQuadraticEisensteinCuspConstant (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) : ℂ :=
  if (q:ℤ)∣γ 1 0 then
    if (q:ℤ)^2∣γ 1 0 then 0 else
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/((γ 1 0/(q:ℤ):ℤ):ZMod q))
  else 0
end QEC.Coding.TannerLiftedProduct


