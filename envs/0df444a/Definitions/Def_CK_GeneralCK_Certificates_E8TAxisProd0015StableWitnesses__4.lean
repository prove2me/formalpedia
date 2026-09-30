-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0015StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0015StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:27:49.711235+00:00
-- url     : https://prove2.me/theorems/a2c5f434-44a8-4aa0-9423-764a8d477cbf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0015StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0016StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0015StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0016StableWitnesses, GeneralCK.Certificates.E8TAxisProd0017StableWitnesses, GeneralCK.Certificates.E8TAxisProd0018StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0015StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0016StableWitnesses, GeneralCK.Certificates.E8TAxisProd0017StableWitnesses, GeneralCK.Certificates.E8TAxisProd0018StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0015StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0016StableWitnesses, GeneralCK.Certificates.E8TAxisProd0017StableWitnesses, GeneralCK.Certificates.E8TAxisProd0018StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0015StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0016StableWitnesses, GeneralCK/Certificates/E8TAxisProd0017StableWitnesses, GeneralCK/Certificates/E8TAxisProd0018StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0015StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0015StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨41959420742712281670701379146144140997527296443, 41959420742712281670701379146144140997527296444⟩
def centerDExp : DyadicInterval precision := ⟨1379946629933930331657679320297936454916277018329, 1379946629933930331657679320297936457115300273882⟩
def centerDLog : DyadicInterval precision := ⟨971678559134379732480531149474418344828596219705, 971678559134379732480531149474418347027619475258⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1379946629933930331657679320297936455466032832217, scale precision, 1379946629933930331657679320297936456565544459994, scale precision,
    0, 128, 0, 128, ⟨-83918841485424563341402758292288282577302088319, -83918841485424563341402758292288282577299991166⟩, ⟨-83918841485424563341402758292288281412809194607, -83918841485424563341402758292288281412807097454⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨46396168549892361123223624251302832188063645967, 46396168549892361123223624251302832188063645968⟩
def centerCExp : DyadicInterval precision := ⟨1371593678001290788087549877738404088010937503991, 1371593678001290788087549877738404090209960759544⟩
def centerCLog : DyadicInterval precision := ⟨967375882957617076806629587652136134880715996052, 967375882957617076806629587652136137079739251605⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1371593678001290788087549877738404088560693317879, scale precision, 1371593678001290788087549877738404089660204945656, scale precision,
    0, 128, 0, 128, ⟨-92792337099784722246447248502605664961920645490, -92792337099784722246447248502605664961918548337⟩, ⟨-92792337099784722246447248502605663790336035533, -92792337099784722246447248502605663790333938380⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨88449342971355302470485152083509965479350191858, 88449342971355302470485152083509965479350191859⟩
def centerBExp : DyadicInterval precision := ⟨1294889590511360688191276887190755562697257383357, 1294889590511360688191276887190755564896280638910⟩
def centerBLog : DyadicInterval precision := ⟨927261218964308206823929778080634459182431623851, 927261218964308206823929778080634461381454879404⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1294889590511360688191276887190755563247013197245, scale precision, 1294889590511360688191276887190755564346524825022, scale precision,
    0, 128, 0, 128, ⟨-176898685942710604940970304167019931579193733737, -176898685942710604940970304167019931579191636584⟩, ⟨-176898685942710604940970304167019930338209130852, -176898685942710604940970304167019930338207033699⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨39582967301423713423413965103485819080159470448, 44336132104644388932745897738796280177181849965⟩
def wholeDExp : DyadicInterval precision := ⟨1375465749469112915336031076552653132056969284860, 1384441619203923782885550597943121613215597964582⟩
def wholeDLog : DyadicInterval precision := ⟨969371994805781330198871946178310254294535145271, 973988734376663612812883207699140571860322172920⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1375465749469112915336031076552653132606725098748, scale precision, 1384441619203923782885550597943121612665842150694, scale precision,
    0, 128, 0, 128, ⟨-88672264209288777865491795477592560938507990487, -88672264209288777865491795477592560938505893334⟩, ⟨-79165934602847426846827930206971637579963973744, -79165934602847426846827930206971637579961876591⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨43385415673619159303918653523724014002199098407, 49407379045633827464414075058902870336018902476⟩
def wholeCExp : DyadicInterval precision := ⟨1365953370436910710094213347852217826469402750154, 1377256413094801759155106396529063143270087999927⟩
def wholeCLog : DyadicInterval precision := ⟨964463331704461220929462846819637724445475614936, 970294188078387503961473855714136033145720798694⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1365953370436910710094213347852217827019158564042, scale precision, 1377256413094801759155106396529063142720332186039, scale precision,
    0, 128, 0, 128, ⟨-98814758091267654928828150117805741260250017627, -98814758091267654928828150117805741260247920474⟩, ⟨-86770831347238318607837307047448027421015487299, -86770831347238318607837307047448027421013390146⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨83046043307877945193488452689099171381514026011, 93855440023069518713240579865342542906445159879⟩
def wholeBExp : DyadicInterval precision := ⟨1285345340625894062547175233719222220891616698031, 1304499716849142180193281360330416129368699833206⟩
def wholeBLog : DyadicInterval precision := ⟨922191857872443531889266984610450932228790104357, 932347865502707798009618186313188911522430125812⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1285345340625894062547175233719222221441372511919, scale precision, 1304499716849142180193281360330416128818944019318, scale precision,
    0, 128, 0, 128, ⟨-187710880046139037426481159730685086437991095805, -187710880046139037426481159730685086437988998652⟩, ⟨-166092086615755890386976905378198342147107907400, -166092086615755890386976905378198342147105810247⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0015StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0016StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0016StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨37206757161641482619932256052528860593904680845, 37206757161641482619932256052528860593904680846⟩
def centerDExp : DyadicInterval precision := ⟨1388950787845256886456725666204969956264618651552, 1388950787845256886456725666204969958463641907105⟩
def centerDLog : DyadicInterval precision := ⟨976302533872699309670390604038035412903529768221, 976302533872699309670390604038035415102553023774⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1388950787845256886456725666204969956814374465440, scale precision, 1388950787845256886456725666204969957913886093217, scale precision,
    0, 128, 0, 128, ⟨-74413514323282965239864512105057721766282325300, -74413514323282965239864512105057721766280228147⟩, ⟨-74413514323282965239864512105057720609338495235, -74413514323282965239864512105057720609336398082⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨41642545700922946318664417027088040134813591097, 41642545700922946318664417027088040134813591098⟩
def centerCExp : DyadicInterval precision := ⟨1380545145125792881769761660688122545195580384588, 1380545145125792881769761660688122547394603640141⟩
def centerCLog : DyadicInterval precision := ⟨971986373578997184320059528376138692810308280008, 971986373578997184320059528376138695009331535561⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1380545145125792881769761660688122545745336198476, scale precision, 1380545145125792881769761660688122546844847826253, scale precision,
    0, 128, 0, 128, ⟨-83285091401845892637328834054176080851622253182, -83285091401845892637328834054176080851620156029⟩, ⟨-83285091401845892637328834054176079687634208362, -83285091401845892637328834054176079687632111209⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨78915889156853585279154867647520131975925039836, 78915889156853585279154867647520131975925039837⟩
def centerBExp : DyadicInterval precision := ⟨1311893535926435096368422025749772037602832758559, 1311893535926435096368422025749772039801856014112⟩
def centerBLog : DyadicInterval precision := ⟨936249404253899257626472669937639839370265417466, 936249404253899257626472669937639841569288673019⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1311893535926435096368422025749772038152588572447, scale precision, 1311893535926435096368422025749772039252100200224, scale precision,
    0, 128, 0, 128, ⟨-157831778313707170558309735295040264564300995656, -157831778313707170558309735295040264564298898503⟩, ⟨-157831778313707170558309735295040263339401260842, -157831778313707170558309735295040263339399163689⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨34830775707694518323356855819802492385993843109, 39582967301423713423413965103485819080159470449⟩
def wholeDExp : DyadicInterval precision := ⟨1384441619203923782885550597943121611016574709029, 1393474206903787201785230037422771621528978564036⟩
def wholeDLog : DyadicInterval precision := ⟨973988734376663612812883207699140569661298917367, 978619971033722696354607064598753115511294545328⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1384441619203923782885550597943121611566330522917, scale precision, 1393474206903787201785230037422771620979222750148, scale precision,
    0, 128, 0, 128, ⟨-79165934602847426846827930206971638740676005201, -79165934602847426846827930206971638740673908048⟩, ⟨-69661551415389036646713711639604984195394623365, -69661551415389036646713711639604984195392526212⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨38632454867883059004928015843439109440062491346, 44653047225855363666791872108526513837291776536⟩
def wholeCExp : DyadicInterval precision := ⟨1374869360967745695625930110574407952461390162092, 1386243581168110757962356618682828764292913021236⟩
def wholeCLog : DyadicInterval precision := ⟨969064725006139730481551851127638481945447366716, 974913818515194634191299090803398237305451878346⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1374869360967745695625930110574407953011145975980, scale precision, 1386243581168110757962356618682828763743157207348, scale precision,
    0, 128, 0, 128, ⟨-89306094451710727333583744217053028258981232294, -89306094451710727333583744217053028258979135141⟩, ⟨-77264909735766118009856031686878218300524413599, -77264909735766118009856031686878218300522316446⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨73517107907555267916357274697553514970858694063, 84317165343519145459876495372617231162663726897⟩
def wholeBExp : DyadicInterval precision := ⟨1302232545947558403334995047843704355078721026318, 1321621686459769014250747742880888141658961980124⟩
def wholeBLog : DyadicInterval precision := ⟨931149445018404426052713782177447150401369534218, 941366897326883274359109794961412015104683542713⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1302232545947558403334995047843704355628476840206, scale precision, 1321621686459769014250747742880888141109206166236, scale precision,
    0, 128, 0, 128, ⟨-168634330687038290919752990745234462942322006816, -168634330687038290919752990745234462942319909663⟩, ⟨-147034215815110535832714549395107029333776670644, -147034215815110535832714549395107029333774573491⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0016StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0017StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0017StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨41959420742712281670701379146144140997527296443, 41959420742712281670701379146144140997527296444⟩
def centerDExp : DyadicInterval precision := ⟨1379946629933930331657679320297936454916277018329, 1379946629933930331657679320297936457115300273882⟩
def centerDLog : DyadicInterval precision := ⟨971678559134379732480531149474418344828596219705, 971678559134379732480531149474418347027619475258⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1379946629933930331657679320297936455466032832217, scale precision, 1379946629933930331657679320297936456565544459994, scale precision,
    0, 128, 0, 128, ⟨-83918841485424563341402758292288282577302088319, -83918841485424563341402758292288282577299991166⟩, ⟨-83918841485424563341402758292288281412809194607, -83918841485424563341402758292288281412807097454⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨45128429068276474895874415584520700163354642350, 45128429068276474895874415584520700163354642351⟩
def centerCExp : DyadicInterval precision := ⟨1373975245809584953617797629291784319028993784187, 1373975245809584953617797629291784321228017039740⟩
def centerCLog : DyadicInterval precision := ⟨968603940159382777845233748546489174816453986934, 968603940159382777845233748546489177015477242487⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1373975245809584953617797629291784319578749598075, scale precision, 1373975245809584953617797629291784320678261225852, scale precision,
    0, 128, 0, 128, ⟨-90256858136552949791748831169041400911487260359, -90256858136552949791748831169041400911485163206⟩, ⟨-90256858136552949791748831169041399741933406197, -90256858136552949791748831169041399741931309044⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨87177733031446937316788780256552774640368349422, 87177733031446937316788780256552774640368349423⟩
def centerBExp : DyadicInterval precision := ⟨1297144843488804201115883427901752812859846809325, 1297144843488804201115883427901752815058870064878⟩
def centerBLog : DyadicInterval precision := ⟨928456516721811008488201258314450137812977947155, 928456516721811008488201258314450140012001202708⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1297144843488804201115883427901752813409602623213, scale precision, 1297144843488804201115883427901752814509114250990, scale precision,
    0, 128, 0, 128, ⟨-174355466062893874633577560513105549900151243272, -174355466062893874633577560513105549900149146119⟩, ⟨-174355466062893874633577560513105548661324251571, -174355466062893874633577560513105548661322154418⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨39582967301423713423413965103485819080159470448, 44336132104644388932745897738796280177181849965⟩
def wholeDExp : DyadicInterval precision := ⟨1375465749469112915336031076552653132056969284860, 1384441619203923782885550597943121613215597964582⟩
def wholeDLog : DyadicInterval precision := ⟨969371994805781330198871946178310254294535145271, 973988734376663612812883207699140571860322172920⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1375465749469112915336031076552653132606725098748, scale precision, 1384441619203923782885550597943121612665842150694, scale precision,
    0, 128, 0, 128, ⟨-88672264209288777865491795477592560938507990487, -88672264209288777865491795477592560938505893334⟩, ⟨-79165934602847426846827930206971637579963973744, -79165934602847426846827930206971637579961876591⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨42117859980909830503480774531012101070616760209, 48139443258654111572486032703577432783283710517⟩
def wholeCExp : DyadicInterval precision := ⟨1368325512272832093860385387564911613155700345703, 1379647466406858027522323513753790951843933825925⟩
def wholeCLog : DyadicInterval precision := ⟨965688969487382976922535666450008843386281485576, 971524675986761039573550901211246880596052861008⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1368325512272832093860385387564911613705456159591, scale precision, 1379647466406858027522323513753790951294178012037, scale precision,
    0, 128, 0, 128, ⟨-96278886517308223144972065407154866153759905363, -96278886517308223144972065407154866153757808210⟩, ⟨-84235719961819661006961549062024201558861867494, -84235719961819661006961549062024201558859770341⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨81775066651422335775660018154838453034717622374, 92583156438057309662723508651133081399695069699⟩
def wholeBExp : DyadicInterval precision := ⟨1287585157761878472691080512611594148706620326785, 1306770574892044410141964846722889503619682838667⟩
def wholeBLog : DyadicInterval precision := ⟨923383100972513773832431775171399218419438987508, 933547250713536054780546866575375687641838410735⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1287585157761878472691080512611594149256376140673, scale precision, 1306770574892044410141964846722889503069927024779, scale precision,
    0, 128, 0, 128, ⟨-185166312876114619325447017302266163423403524002, -185166312876114619325447017302266163423401426849⟩, ⟨-163550133302844671551320036309676905454585425416, -163550133302844671551320036309676905454583328263⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0017StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0018StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0018StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨37206757161641482619932256052528860593904680845, 37206757161641482619932256052528860593904680846⟩
def centerDExp : DyadicInterval precision := ⟨1388950787845256886456725666204969956264618651552, 1388950787845256886456725666204969958463641907105⟩
def centerDLog : DyadicInterval precision := ⟨976302533872699309670390604038035412903529768221, 976302533872699309670390604038035415102553023774⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1388950787845256886456725666204969956814374465440, scale precision, 1388950787845256886456725666204969957913886093217, scale precision,
    0, 128, 0, 128, ⟨-74413514323282965239864512105057721766282325300, -74413514323282965239864512105057721766280228147⟩, ⟨-74413514323282965239864512105057720609338495235, -74413514323282965239864512105057720609336398082⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨40375090693159801851928927361794245008098218804, 40375090693159801851928927361794245008098218805⟩
def centerCExp : DyadicInterval precision := ⟨1382941717456140621235410042270780454636171050065, 1382941717456140621235410042270780456835194305618⟩
def centerCLog : DyadicInterval precision := ⟨973218273927939015702329193153137247247435970938, 973218273927939015702329193153137249446459226491⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1382941717456140621235410042270780455185926863953, scale precision, 1382941717456140621235410042270780456285438491730, scale precision,
    0, 128, 0, 128, ⟨-80750181386319603703857854723588490597182940589, -80750181386319603703857854723588490597180843436⟩, ⟨-80750181386319603703857854723588489435212031781, -80750181386319603703857854723588489435209934628⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨77645369570881856131634213456988849457071010819, 77645369570881856131634213456988849457071010820⟩
def centerBExp : DyadicInterval precision := ⟨1314176443052035035011635510670998525291054396787, 1314176443052035035011635510670998527490077652340⟩
def centerBLog : DyadicInterval precision := ⟨937451937555468337883787528928488125233036014436, 937451937555468337883787528928488127432059269989⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1314176443052035035011635510670998525840810210675, scale precision, 1314176443052035035011635510670998526940321838452, scale precision,
    0, 128, 0, 128, ⟨-155290739141763712263268426913977699525529027085, -155290739141763712263268426913977699525526929932⟩, ⟨-155290739141763712263268426913977698302757113347, -155290739141763712263268426913977698302755016194⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨34830775707694518323356855819802492385993843109, 39582967301423713423413965103485819080159470449⟩
def wholeDExp : DyadicInterval precision := ⟨1384441619203923782885550597943121611016574709029, 1393474206903787201785230037422771621528978564036⟩
def wholeDLog : DyadicInterval precision := ⟨973988734376663612812883207699140569661298917367, 978619971033722696354607064598753115511294545328⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1384441619203923782885550597943121611566330522917, scale precision, 1393474206903787201785230037422771620979222750148, scale precision,
    0, 128, 0, 128, ⟨-79165934602847426846827930206971638740676005201, -79165934602847426846827930206971638740673908048⟩, ⟨-69661551415389036646713711639604984195394623365, -69661551415389036646713711639604984195392526212⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨37365163894633166934139863628747988917988881050, 43385415673619159303918653523724014002199098408⟩
def wholeCExp : DyadicInterval precision := ⟨1377256413094801759155106396529063141071064744374, 1388649734044654119234359722553860935144562278464⟩
def wholeCLog : DyadicInterval precision := ⟨970294188078387503961473855714136030946697543141, 976148167549896511977221673672472963870626780054⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1377256413094801759155106396529063141620820558262, scale precision, 1388649734044654119234359722553860934594806464576, scale precision,
    0, 128, 0, 128, ⟨-86770831347238318607837307047448028587783003487, -86770831347238318607837307047448028587780906334⟩, ⟨-74730327789266333868279727257495977257381485210, -74730327789266333868279727257495977257379388057⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨72247150488409424271229859008789322648796023083, 83046043307877945193488452689099171381514026012⟩
def wholeBExp : DyadicInterval precision := ⟨1304499716849142180193281360330416127169676577653, 1323920503649282092956694500381848423718654121092⟩
def wholeBLog : DyadicInterval precision := ⟨932347865502707798009618186313188909323406870259, 942573576988029917998135757461079989709332828371⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1304499716849142180193281360330416127719432391541, scale precision, 1323920503649282092956694500381848423168898307204, scale precision,
    0, 128, 0, 128, ⟨-166092086615755890386976905378198343378950293799, -166092086615755890386976905378198343378948196646⟩, ⟨-144494300976818848542459718017578644690706941145, -144494300976818848542459718017578644690704843992⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0018StableWitnesses

end


