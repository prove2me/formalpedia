-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisOneCellStableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisOneCellStableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:20:56.317407+00:00
-- url     : https://prove2.me/theorems/a384eee8-9c88-4112-8cc8-08a21860d3f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisOneCellStableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisOneCellStableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisOneCellStableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisOneCellStableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisOneCellStableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval
import Definitions.Def_GeneralCK_E8_first_cell_inputs

-- ===== source module GeneralCK.Certificates.E8TAxisOneCellStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisOneCellStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000



def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide





def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide





def centerDExpWitness : ExpWitness precision :=
  ⟨1425852095715601701956974364377367523605901149871, scale precision, 1425852095715601701956974364377367524705412777648, scale precision,
    0, 128, 0, 128, ⟨-36091532956806446805385153816125042837822662151, -36091532956806446805385153816125042837820564998⟩, ⟨-36091532956806446805385153816125041710820745831, -36091532956806446805385153816125041710818648678⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide





def centerCExpWitness : ExpWitness precision :=
  ⟨1418457285902836992172107953103186433402689089067, scale precision, 1418457285902836992172107953103186434502200716844, scale precision,
    0, 128, 0, 128, ⟨-43690953096831276119177782591972235922733345815, -43690953096831276119177782591972235922731248662⟩, ⟨-43690953096831276119177782591972234789856057065, -43690953096831276119177782591972234789853959912⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide





def centerBExpWitness : ExpWitness precision :=
  ⟨1383841469593821749822064582626245044568094900658, scale precision, 1383841469593821749822064582626245045667606528435, scale precision,
    0, 128, 0, 128, ⟨-79799626767567547014096931643122559203168403688, -79799626767567547014096931643122559203166306535⟩, ⟨-79799626767567547014096931643122558041952990240, -79799626767567547014096931643122558041950893087⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide





def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide





def wholeDExpWitness : ExpWitness precision :=
  ⟨1423999843327116683343282796578766320071393533169, scale precision, 1427706722737910795912950268245206060743153543936, scale precision,
    0, 128, 0, 128, ⟨-37991330095470232437237785869777168876302439825, -37991330095470232437237785869777168876300342672⟩, ⟨-34191771302081029651685946212427768366498148783, -34191771302081029651685946212427768366496051630⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide





def wholeCExpWitness : ExpWitness precision :=
  ⟨1414161070744739559008334114269995750876123665395, scale precision, 1422766325265285935775877612508304622076012167697, scale precision,
    0, 128, 0, 128, ⟨-48124257913736150150163174553888712921179265145, -48124257913736150150163174553888712921177167992⟩, ⟨-39257882157075460393625882481231640526225837338, -39257882157075460393625882481231640526223740185⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide





def wholeBExpWitness : ExpWitness precision :=
  ⟨1377853800896563995864571507763643414276346917837, scale precision, 1389854329341637920452395630847774506522186392372, scale precision,
    0, 128, 0, 128, ⟨-86137039450532460968088907419430722957626977305, -86137039450532460968088907419430722957624880152⟩, ⟨-73463086087256135796311921913602629993563805716, -73463086087256135796311921913602629993561708563⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisOneCellStableWitnesses

end


