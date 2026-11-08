-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
-- name    : QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:52:53.663173+00:00
-- url     : https://prove2.me/theorems/a18b0f7a-9529-4b9e-b5e0-9c440baecde8
-- title:
--   LPSGood Family Assembly
-- statement:
--   Definitions and structural lemmas for LPSGood Family Assembly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable local instance pk22LPSFamilyQubitDecidableEq
    {p : ℕ} {R R' : Type} (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    DecidableEq
      (FamilyQubitIndex (W := Fin (p + 1)) (R := R) (R' := R')
        (G := LPSVertexGroup hp hp4) n) :=
  Classical.decEq _
end QEC.Coding.TannerLiftedProduct


