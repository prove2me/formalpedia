-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0079PaddedInputs__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0079PaddedInputs__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:36:13.05611+00:00
-- url     : https://prove2.me/theorems/f378a421-40ff-4097-a990-67074f2c5723
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0079PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0080PaddedInputs)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0079PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0080PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0079PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0080PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0079PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0080PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0079PaddedInputs (+1 modules: GeneralCK/Certificates/E8TAxisZero0080PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0079StableWitnesses__2

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0079PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0079StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1319306210611389980012831776206758859760100103054, 1319306210611389980012831776206758859760133657487⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0079StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0079StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨567848294031146470579397596369748635070119335727, 567848294031146470579397596369748635070152890160⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0079StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0079StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958605638136, 567663676182737085008043281595790637958639192569⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0079StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0079StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1303954626397188829779031121552643393842819157218, 1334744927095837707008945731211281100517775458953⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0079StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0079StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789366460941, 573348067014784918070662694275613453001276082452⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0079StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0079StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789366460941, 572977884517961874928161575521614457065513997358⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0079StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0079StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0079StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0079PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0080PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0080StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1289211086540730807145370793336689628180851818479, 1289211086540730807145370793336689628180885372912⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0080StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0080StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨557258769997157377871061809709403154248059024599, 557258769997157377871061809709403154248092579032⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0080StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0080StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨557075069631301290362165038182134082283938781109, 557075069631301290362165038182134082283972335542⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0080StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0080StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1274032259617610934704101070165693753025255051626, 1304478022594555801804565823310086935043489197582⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0080StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0080StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576069515674, 562731109413180805839587549857455580404994608878⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0080StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0080StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576069515674, 562362779591003425345044647758252905789400015374⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0080StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0080StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0080StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0080PaddedInputs

end


