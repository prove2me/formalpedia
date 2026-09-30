-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0288PaddedInputs__4_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0288PaddedInputs__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T02:50:58.030985+00:00
-- url     : https://prove2.me/theorems/fcffe6e6-2679-4024-996c-0d170b89a053
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0288PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0289PaddedInputs, GeneralCK.Certificates.E8TAxisProd0290Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0288PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0289PaddedInputs, GeneralCK.Certificates.E8TAxisProd0290PaddedInputs, GeneralCK.Certificates.E8TAxisProd0291PaddedInputs) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0288PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0289PaddedInputs, GeneralCK.Certificates.E8TAxisProd0290PaddedInputs, GeneralCK.Certificates.E8TAxisProd0291PaddedInputs) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0288PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0289PaddedInputs, GeneralCK.Certificates.E8TAxisProd0290PaddedInputs, GeneralCK.Certificates.E8TAxisProd0291PaddedInputs) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0288PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0289PaddedInputs, GeneralCK/Certificates/E8TAxisProd0290PaddedInputs, GeneralCK/Certificates/E8TAxisProd0291PaddedInputs) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0288StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0288PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0288PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0288StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191529989027, 4906913324212444341793886191975635191530120100⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0288StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0288StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1851202026516386844676125464232466200144171800244, 1851202026516386844676125464232466200144171931317⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0288StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0288StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨751261513194905100306220671515370146965089771075, 751261513194905100306220671515370146965089902148⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0288StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0288StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271654647, 745000746231477256788872225997272556554271785720⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0288StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0288StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681585802, 5065202303167835215808940955361609459283176271⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0288StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0288StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1833534741339132018980085123090063358998856595176, 1868921773151278088516694195306551882670944175957⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0288StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0288StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨745252807755324850087391349592380902383277872608, 757288810935202959796562750370416775604480301482⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0288StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0288StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786913409, 750806424999049798752938234956163650116084066834⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0288StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0288StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0288StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0288PaddedInputs

end


