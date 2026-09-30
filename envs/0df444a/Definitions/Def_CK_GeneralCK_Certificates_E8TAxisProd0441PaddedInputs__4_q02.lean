-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:42:00.116854+00:00
-- url     : https://prove2.me/theorems/a2bc0d30-a9d1-439a-92b2-ff5b69ab12d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0442PaddedInputs, GeneralCK/Certificates/E8TAxisProd0443PaddedInputs, GeneralCK/Certificates/E8TAxisProd0444PaddedInputs) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q01

-- ===== source module GeneralCK.Certificates.E8TAxisProd0443PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0443PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0443StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052156972690, 791434261379870553054051158387221052157103763⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0443StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0443StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1740101764728887394124126136018211302313109463472, 1740101764728887394124126136018211302313109594545⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0443StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0443StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨711515375350850948738973039777987219163675204342, 711515375350850948738973039777987219163675335415⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0443StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0443StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823373949832, 710524563403850356500890582610538039823374080905⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0443StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0443StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 949721161203312387564849132921065893757663367⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0443StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0443StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1722798026884796605435096683569979212267277765074, 1757466362974491736158182071073596293001983979321⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0443StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0443StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨705627393751618059150757717755430214801700022275, 717421077147708262788725994993917339219452816540⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0443StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0443StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105661957302, 716228578308099727358082939138935890959899278031⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0443StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0443StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0443StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0443PaddedInputs

end


