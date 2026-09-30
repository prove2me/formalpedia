-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0033StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0033StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:18:28.229142+00:00
-- url     : https://prove2.me/theorems/95ee58ea-e33a-4cca-9f90-1538b148abc8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0033StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0034StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0033StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0034StableWitnesses, GeneralCK.Certificates.E8TAxisProd0035StableWitnesses, GeneralCK.Certificates.E8TAxisProd0036StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0033StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0034StableWitnesses, GeneralCK.Certificates.E8TAxisProd0035StableWitnesses, GeneralCK.Certificates.E8TAxisProd0036StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0033StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0034StableWitnesses, GeneralCK.Certificates.E8TAxisProd0035StableWitnesses, GeneralCK.Certificates.E8TAxisProd0036StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0033StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0034StableWitnesses, GeneralCK/Certificates/E8TAxisProd0035StableWitnesses, GeneralCK/Certificates/E8TAxisProd0036StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0033StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0033StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨123008276316677968590567857617524352972070183257, 123008276316677968590567857617524352972070183258⟩
def centerDExp : DyadicInterval precision := ⟨1235076695440473766556638255203847372603080990588, 1235076695440473766556638255203847374802104246141⟩
def centerDLog : DyadicInterval precision := ⟨895197900350273137203831070133649824645107273249, 895197900350273137203831070133649826844130528802⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1235076695440473766556638255203847373152836804476, scale precision, 1235076695440473766556638255203847374252348432253, scale precision,
    0, 128, 0, 128, ⟨-246016552633355937181135715235048706594683219577, -246016552633355937181135715235048706594681122424⟩, ⟨-246016552633355937181135715235048705293599610606, -246016552633355937181135715235048705293597513453⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨127478106982542634123444623446702617095107226922, 127478106982542634123444623446702617095107226923⟩
def centerCExp : DyadicInterval precision := ⟨1227545080196374627818416944219024721448799562281, 1227545080196374627818416944219024723647822817834⟩
def centerCLog : DyadicInterval precision := ⟨891110176053093103777779719670505082787219136744, 891110176053093103777779719670505084986242392297⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1227545080196374627818416944219024721998555376169, scale precision, 1227545080196374627818416944219024723098067003946, scale precision,
    0, 128, 0, 128, ⟨-254956213965085268246889246893405234844748712721, -254956213965085268246889246893405234844746615568⟩, ⟨-254956213965085268246889246893405233535682292119, -254956213965085268246889246893405233535680194966⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨252629397574248137835203746750995613110135119104, 252629397574248137835203746750995613110135119105⟩
def centerBExp : DyadicInterval precision := ⟨1034328402193971172474688220210670670183156827944, 1034328402193971172474688220210670672382180083497⟩
def centerBLog : DyadicInterval precision := ⟨782132728214745566577792381463024518020002349200, 782132728214745566577792381463024520219025604753⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1034328402193971172474688220210670670732912641832, scale precision, 1034328402193971172474688220210670671832424269609, scale precision,
    0, 128, 0, 128, ⟨-505258795148496275670407493501991226997073915839, -505258795148496275670407493501991226997071818686⟩, ⟨-505258795148496275670407493501991225443468657730, -505258795148496275670407493501991225443466560577⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278241017, 126999067220414009923202423697912773180597398747⟩
def wholeDExp : DyadicInterval precision := ⟨1228350054579566692017908102915209765594934478659, 1241836591959774864289057338296444370704392702246⟩
def wholeDLog : DyadicInterval precision := ⟨891547615580027951955449639520829062035069301574, 898857069849833759981739512399832702035676431148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1228350054579566692017908102915209766144690292547, scale precision, 1241836591959774864289057338296444370154636888358, scale precision,
    0, 128, 0, 128, ⟨-253998134440828019846404847395825547015300121259, -253998134440828019846404847395825547015298024106⟩, ⟨-238039184664660159546675469840789440935556928976, -238039184664660159546675469840789440935554831823⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨122848688962441263613203278400959891368589806121, 132110463846210516044711664841215322615024907154⟩
def wholeCExp : DyadicInterval precision := ⟨1219788070376012291331212345706861179026867056585, 1235346451068630015043686617380955606919368727522⟩
def wholeCLog : DyadicInterval precision := ⟨886888134996521783257090466047055991317612458814, 895344096204919741620693735092813399579373706233⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1219788070376012291331212345706861179576622870473, scale precision, 1235346451068630015043686617380955606369612913634, scale precision,
    0, 128, 0, 128, ⟨-264220927692421032089423329682430645888746452424, -264220927692421032089423329682430645888744355271⟩, ⟨-245697377924882527226406556801919782086780911474, -245697377924882527226406556801919782086778814321⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨243797635752172854441566085746482099908275673539, 261481554085338207199210368615594053303071317312⟩
def wholeBExp : DyadicInterval precision := ⟨1021874357938466258669045575256879970086457865486, 1046905010795551553201549808992034661246932013298⟩
def wholeBLog : DyadicInterval precision := ⟨774821665406531776561079319035724441259170101514, 789478812706385577759978772296657462163373647542⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1021874357938466258669045575256879970636213679374, scale precision, 1046905010795551553201549808992034660697176199410, scale precision,
    0, 128, 0, 128, ⟨-522963108170676414398420737231188107392413556682, -522963108170676414398420737231188107392411459529⟩, ⟨-487595271504345708883132171492964199049081599505, -487595271504345708883132171492964199049079502352⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0033StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0034StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0034StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨115032946497916170088737142525822549131339623218, 115032946497916170088737142525822549131339623219⟩
def centerDExp : DyadicInterval precision := ⟨1248630004573113102149096526493550178299957551294, 1248630004573113102149096526493550180498980806847⟩
def centerDLog : DyadicInterval precision := ⟨902525175189120016129211831586767280434114094617, 902525175189120016129211831586767282633137350170⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1248630004573113102149096526493550178849713365182, scale precision, 1248630004573113102149096526493550179949224992959, scale precision,
    0, 128, 0, 128, ⟨-230065892995832340177474285051645098906160764959, -230065892995832340177474285051645098906158667806⟩, ⟨-230065892995832340177474285051645097619199825069, -230065892995832340177474285051645097619197727916⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨119498125441286525087546427440929322561322481355, 119498125441286525087546427440929322561322481356⟩
def centerCExp : DyadicInterval precision := ⟨1241023639888395997564761833039414711259689190788, 1241023639888395997564761833039414713458712446341⟩
def centerCLog : DyadicInterval precision := ⟨898417498709749459072188107379093239377237908975, 898417498709749459072188107379093241576261164528⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1241023639888395997564761833039414711809445004676, scale precision, 1241023639888395997564761833039414712908956632453, scale precision,
    0, 128, 0, 128, ⟨-238996250882573050175092854881858645770070440852, -238996250882573050175092854881858645770068343699⟩, ⟨-238996250882573050175092854881858644475221581724, -238996250882573050175092854881858644475219484571⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨236289822428373432150654949298107898906188217602, 236289822428373432150654949298107898906188217603⟩
def centerBExp : DyadicInterval precision := ⟨1057716470600957690177348546850699430402172016992, 1057716470600957690177348546850699432601195272545⟩
def centerBLog : DyadicInterval precision := ⟨795764480921592490878998218352018258725978223569, 795764480921592490878998218352018260925001479122⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1057716470600957690177348546850699430951927830880, scale precision, 1057716470600957690177348546850699432051439458657, scale precision,
    0, 128, 0, 128, ⟨-472579644856746864301309898596215798572003569281, -472579644856746864301309898596215798572001472128⟩, ⟨-472579644856746864301309898596215797052751398283, -472579644856746864301309898596215797052749301130⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨111048270122241576078328386047482676587330985904, 119019592332330079773337734920394720791278241018⟩
def wholeDExp : DyadicInterval precision := ⟨1241836591959774864289057338296444368505369446693, 1255457196643991312782767932801799989113568160976⟩
def wholeDLog : DyadicInterval precision := ⟨898857069849833759981739512399832699836653175595, 906202267987834631995011695345793201716926871713⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1241836591959774864289057338296444369055125260581, scale precision, 1255457196643991312782767932801799988563812347088, scale precision,
    0, 128, 0, 128, ⟨-238039184664660159546675469840789442229558132246, -238039184664660159546675469840789442229556035093⟩, ⟨-222096540244483152156656772094965352534681805353, -222096540244483152156656772094965352534679708200⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨114873522086229401550599629602980010984739621714, 124125482432655107267784619184625826590664438275⟩
def wholeCExp : DyadicInterval precision := ⟨1233189894958627491970848091783125044561964271681, 1248902441927408411362553828834974223518554551378⟩
def wholeCLog : DyadicInterval precision := ⟨894174927219586722108278281493878705517900685513, 902672085996534669099115243778699391521085448306⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1233189894958627491970848091783125045111720085569, scale precision, 1248902441927408411362553828834974222968798737490, scale precision,
    0, 128, 0, 128, ⟨-248250964865310214535569238369251653832867069092, -248250964865310214535569238369251653832864971939⟩, ⟨-229747044172458803101199259205960021326140191804, -229747044172458803101199259205960021326138094651⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨227493904775828364443481753968725214648101220906, 245104786449875745977549104126014224823483124985⟩
def wholeBExp : DyadicInterval precision := ⟨1045034004465915750166869454598200825920388086610, 1070524947694947175059872365104781310019638952323⟩
def wholeBLog : DyadicInterval precision := ⟨788388280140701814001405921433914844571445968825, 803176377000203245651677875656754748282636989136⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1045034004465915750166869454598200826470143900498, scale precision, 1070524947694947175059872365104781309469883138435, scale precision,
    0, 128, 0, 128, ⟨-490209572899751491955098208252028450415812157849, -490209572899751491955098208252028450415810060696⟩, ⟨-454987809551656728886963507937450428545666079879, -454987809551656728886963507937450428545663982726⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0034StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0035StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0035StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨123008276316677968590567857617524352972070183257, 123008276316677968590567857617524352972070183258⟩
def centerDExp : DyadicInterval precision := ⟨1235076695440473766556638255203847372603080990588, 1235076695440473766556638255203847374802104246141⟩
def centerDLog : DyadicInterval precision := ⟨895197900350273137203831070133649824645107273249, 895197900350273137203831070133649826844130528802⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1235076695440473766556638255203847373152836804476, scale precision, 1235076695440473766556638255203847374252348432253, scale precision,
    0, 128, 0, 128, ⟨-246016552633355937181135715235048706594683219577, -246016552633355937181135715235048706594681122424⟩, ⟨-246016552633355937181135715235048705293599610606, -246016552633355937181135715235048705293597513453⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨126200737182489831150770811154715072209053184578, 126200737182489831150770811154715072209053184579⟩
def centerCExp : DyadicInterval precision := ⟨1229692734702456445857835763839615529868543090535, 1229692734702456445857835763839615532067566346088⟩
def centerCLog : DyadicInterval precision := ⟨892276964191960084649067259273938349531657570183, 892276964191960084649067259273938351730680825736⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1229692734702456445857835763839615530418298904423, scale precision, 1229692734702456445857835763839615531517810532200, scale precision,
    0, 128, 0, 128, ⟨-252401474364979662301541622309430145071497487834, -252401474364979662301541622309430145071495390681⟩, ⟨-252401474364979662301541622309430143764717347632, -252401474364979662301541622309430143764715250479⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨251319719158077856123941449565787593282445443877, 251319719158077856123941449565787593282445443878⟩
def centerBExp : DyadicInterval precision := ⟨1036183825670844774535695031954842783979263822311, 1036183825670844774535695031954842786178287077864⟩
def centerBLog : DyadicInterval precision := ⟨783218818594485091996894003512475467208046130526, 783218818594485091996894003512475469407069386079⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1036183825670844774535695031954842784529019636199, scale precision, 1036183825670844774535695031954842785628531263976, scale precision,
    0, 128, 0, 128, ⟨-502639438316155712247882899131575187340303598071, -502639438316155712247882899131575187340301500918⟩, ⟨-502639438316155712247882899131575185789480274593, -502639438316155712247882899131575185789478177440⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278241017, 126999067220414009923202423697912773180597398747⟩
def wholeDExp : DyadicInterval precision := ⟨1228350054579566692017908102915209765594934478659, 1241836591959774864289057338296444370704392702246⟩
def wholeDLog : DyadicInterval precision := ⟨891547615580027951955449639520829062035069301574, 898857069849833759981739512399832702035676431148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1228350054579566692017908102915209766144690292547, scale precision, 1241836591959774864289057338296444370154636888358, scale precision,
    0, 128, 0, 128, ⟨-253998134440828019846404847395825547015300121259, -253998134440828019846404847395825547015298024106⟩, ⟨-238039184664660159546675469840789440935556928976, -238039184664660159546675469840789440935554831823⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨121572110958318617549910999863282960483547397040, 130832272587569695809414699320324921011080789364⟩
def wholeCExp : DyadicInterval precision := ⟨1221923527186106999084992706451107773922571225226, 1237506413596899800280902874213208099575987389128⟩
def wholeCLog : DyadicInterval precision := ⟨888051653976961835389995825692819349198360761300, 896514175190994470540006811065962632918549728880⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1221923527186106999084992706451107774472327039114, scale precision, 1237506413596899800280902874213208099026231575240, scale precision,
    0, 128, 0, 128, ⟨-261664545175139391618829398640649842679707067895, -261664545175139391618829398640649842679704970742⟩, ⟨-243144221916637235099821999726565920317831310934, -243144221916637235099821999726565920317829213781⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨242490916659753179449762138168969105284430212067, 260168808084051724207340356924670106199222168444⟩
def wholeBExp : DyadicInterval precision := ⟨1023711738189858330509771486033612622731514215510, 1048778747491402917119097353667193952174950851636⟩
def wholeBLog : DyadicInterval precision := ⟨775902589655979148194684620099574950716477926989, 790570121791082467784100830538504735231304343792⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1023711738189858330509771486033612623281270029398, scale precision, 1048778747491402917119097353667193951625195037748, scale precision,
    0, 128, 0, 128, ⟨-520337616168103448414680713849340213183304044553, -520337616168103448414680713849340213183301947400⟩, ⟨-484981833319506358899524276337938209802761831533, -484981833319506358899524276337938209802759734380⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0035StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0036StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0036StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨115032946497916170088737142525822549131339623218, 115032946497916170088737142525822549131339623219⟩
def centerDExp : DyadicInterval precision := ⟨1248630004573113102149096526493550178299957551294, 1248630004573113102149096526493550180498980806847⟩
def centerDLog : DyadicInterval precision := ⟨902525175189120016129211831586767280434114094617, 902525175189120016129211831586767282633137350170⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1248630004573113102149096526493550178849713365182, scale precision, 1248630004573113102149096526493550179949224992959, scale precision,
    0, 128, 0, 128, ⟨-230065892995832340177474285051645098906160764959, -230065892995832340177474285051645098906158667806⟩, ⟨-230065892995832340177474285051645097619199825069, -230065892995832340177474285051645097619197727916⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨118222102312682179801558145325863917459695885950, 118222102312682179801558145325863917459695885951⟩
def centerCExp : DyadicInterval precision := ⟨1243192584809659346332540780701660230398817559438, 1243192584809659346332540780701660232597840814991⟩
def centerCLog : DyadicInterval precision := ⟨899589974406026509770914735756673585866022427539, 899589974406026509770914735756673588065045683092⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1243192584809659346332540780701660230948573373326, scale precision, 1243192584809659346332540780701660232048085001103, scale precision,
    0, 128, 0, 128, ⟨-236444204625364359603116290651727835565687716335, -236444204625364359603116290651727835565685619182⟩, ⟨-236444204625364359603116290651727834273097924620, -236444204625364359603116290651727834273095827467⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨234985539199456772845014830690100987041247113914, 234985539199456772845014830690100987041247113915⟩
def centerBExp : DyadicInterval precision := ⟨1059606025438338833497597228890590279939812954341, 1059606025438338833497597228890590282138836209894⟩
def centerBLog : DyadicInterval precision := ⟨796860278194889237597851068653529001927470433564, 796860278194889237597851068653529004126493689117⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1059606025438338833497597228890590280489568768229, scale precision, 1059606025438338833497597228890590281589080396006, scale precision,
    0, 128, 0, 128, ⟨-469971078398913545690029661380201974840766749803, -469971078398913545690029661380201974840764652650⟩, ⟨-469971078398913545690029661380201973324223803007, -469971078398913545690029661380201973324221705854⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨111048270122241576078328386047482676587330985904, 119019592332330079773337734920394720791278241018⟩
def wholeDExp : DyadicInterval precision := ⟨1241836591959774864289057338296444368505369446693, 1255457196643991312782767932801799989113568160976⟩
def wholeDLog : DyadicInterval precision := ⟨898857069849833759981739512399832699836653175595, 906202267987834631995011695345793201716926871713⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1241836591959774864289057338296444369055125260581, scale precision, 1255457196643991312782767932801799988563812347088, scale precision,
    0, 128, 0, 128, ⟨-238039184664660159546675469840789442229558132246, -238039184664660159546675469840789442229556035093⟩, ⟨-222096540244483152156656772094965352534681805353, -222096540244483152156656772094965352534679708200⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨113598239705995084404205697354797805075838982126, 122848688962441263613203278400959891368589806122⟩
def wholeCExp : DyadicInterval precision := ⟨1235346451068630015043686617380955604720345471969, 1251083888480320811413471717281821798377569976454⟩
def wholeCLog : DyadicInterval precision := ⟨895344096204919741620693735092813397380350450680, 903847890529817803406659632589687595921909556463⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1235346451068630015043686617380955605270101285857, scale precision, 1251083888480320811413471717281821797827814162566, scale precision,
    0, 128, 0, 128, ⟨-245697377924882527226406556801919783387580410166, -245697377924882527226406556801919783387578313013⟩, ⟨-227196479411990168808411394709595609509460669578, -227196479411990168808411394709595609509458572425⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨226192381607875787764973691711067383103547195306, 243797635752172854441566085746482099908275673540⟩
def wholeBExp : DyadicInterval precision := ⟨1046905010795551553201549808992034659047908757745, 1072433333592369868803923397647789076681842146302⟩
def wholeBLog : DyadicInterval precision := ⟨789478812706385577759978772296657459964350391989, 804277494414882387092884188447412248693008087316⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1046905010795551553201549808992034659597664571633, scale precision, 1072433333592369868803923397647789076132086332414, scale precision,
    0, 128, 0, 128, ⟨-487595271504345708883132171492964200584023191808, -487595271504345708883132171492964200584021094655⟩, ⟨-452384763215751575529947383422134765457893603549, -452384763215751575529947383422134765457891506396⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0036StableWitnesses

end


