-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:32:15.409217+00:00
-- url     : https://prove2.me/theorems/784fa684-922e-4258-8f1e-8b1936505c6f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0442PaddedInputs, GeneralCK/Certificates/E8TAxisProd0443PaddedInputs, GeneralCK/Certificates/E8TAxisProd0444PaddedInputs) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0441PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0441PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0441StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611229637, 1108008086961741616166050582946352244611360710⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0441StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0441StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1740694428920737654602028425796126814116227213496, 1740694428920737654602028425796126814116227344569⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0441StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0441StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨711911840244555793426059204632276334682645120858, 711911840244555793426059204632276334682645251931⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0441StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0441StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823373949832, 710524563403850356500890582610538039823374080905⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0441StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0441StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757532294, 1266295042977660303900587558721132456011255132⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0441StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0441StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1723388588656401691561562299164303724285171710469, 1758061084566505952455073141097382445118862903865⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0441StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0441StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨706022671539624411025582194983808140774018912860, 717818738077276547266346525406500350592538400045⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0441StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0441StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105661957302, 716228578308099727358082939138935890959899278031⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0441StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0441StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0441StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0441PaddedInputs

end


