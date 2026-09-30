-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0079StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0079StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:23:36.360482+00:00
-- url     : https://prove2.me/theorems/a21bc92e-7f5c-436f-8154-83b56f7cb711
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0079StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0080StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0079StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0080StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0079StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0080StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0079StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0080StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0079StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisZero0080StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0079StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    0, 256, 0, 256, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨567848294031146470579397596369748635070136112943, 567848294031146470579397596369748635070136112944⟩
def centerCExp : DyadicInterval precision := ⟨671923547736147706177016959475045102288413533881, 671923547736147706177016959475045104487436789434⟩
def centerCLog : DyadicInterval precision := ⟨552833938214384674752563704591882553125183756476, 552833938214384674752563704591882555324207012029⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨671923547736147706177016959475045102838169347769, scale precision, 671923547736147706177016959475045103937680975546, scale precision,
    0, 256, 0, 256, ⟨-1135696588062292941158795192739497271336047741420, -1135696588062292941158795192739497271336045644267⟩, ⟨-1135696588062292941158795192739497268944498807505, -1135696588062292941158795192739497268944496710352⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1319306210611389980012831776206758859760116880270, 1319306210611389980012831776206758859760116880271⟩
def centerBExp : DyadicInterval precision := ⟨240280699969123675100133528125354500144287810817, 240280699969123675100133528125354502343311066370⟩
def centerBLog : DyadicInterval precision := ⟨222457662901072889736420183537155396555819107150, 222457662901072889736420183537155398754842362703⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨240280699969123675100133528125354500694043624705, scale precision, 240280699969123675100133528125354501793555252482, scale precision,
    0, 256, 0, 256, ⟨-2638612421222779960025663552413517722864111459362, -2638612421222779960025663552413517722864109362209⟩, ⟨-2638612421222779960025663552413517716176358158880, -2638612421222779960025663552413517716176356061727⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    0, 256, 0, 256, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 573348067014784918070662694275613453001259305236⟩
def wholeCExp : DyadicInterval precision := ⟨666885502686027590530453470696017552015831971802, 676986443527636285719880989929562988819692333983⟩
def wholeCLog : DyadicInterval precision := ⟨549378546959253084121969145508749829565791706081, 556298163020790248856133545839930270877081982575⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨666885502686027590530453470696017552565587785690, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    0, 256, 0, 256, ⟨-1146696134029569836141325388551226907207327709145, -1146696134029569836141325388551226907207325611992⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1303954626397188829779031121552643393842835934434, 1334744927095837707008945731211281100517758681737⟩
def wholeBExp : DyadicInterval precision := ⟨235257492285587973567792316238376575915740959527, 245381902706048985556125696915513656302573120713⟩
def wholeBLog : DyadicInterval precision := ⟨218137320382551861838188758000303994126729363009, 226832055690780285899759954522573968566016699148⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨235257492285587973567792316238376576465496773415, scale precision, 245381902706048985556125696915513655752817306825, scale precision,
    0, 256, 0, 256, ⟨-2669489854191675414017891462422562204450793370240, -2669489854191675414017891462422562204450791273087⟩, ⟨-2607909252794377659558062243105286784411311551469, -2607909252794377659558062243105286784411309454316⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0079StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0080StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨557075069631301290362165038182134082283955558325, 557075069631301290362165038182134082283955558326⟩
def centerDExp : DyadicInterval precision := ⟨681902880895464588128477464036409276306339175751, 681902880895464588128477464036409278505362431304⟩
def centerDLog : DyadicInterval precision := ⟨559654335205987407427227649575573486508888333329, 559654335205987407427227649575573488707911588882⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨681902880895464588128477464036409276856094989639, scale precision, 681902880895464588128477464036409277955606617416, scale precision,
    0, 256, 0, 256, ⟨-1114150139262602580724330076364268165746187026121, -1114150139262602580724330076364268165746184928968⟩, ⟨-1114150139262602580724330076364268163389637304333, -1114150139262602580724330076364268163389635207180⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨557258769997157377871061809709403154248075801815, 557258769997157377871061809709403154248075801816⟩
def centerCExp : DyadicInterval precision := ⟨681731481751191023075743744590502176409167342682, 681731481751191023075743744590502178608190598235⟩
def centerCLog : DyadicInterval precision := ⟨559537460325803359830892603376413511777291025210, 559537460325803359830892603376413513976314280763⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨681731481751191023075743744590502176958923156570, scale precision, 681731481751191023075743744590502178058434784347, scale precision,
    0, 256, 0, 256, ⟨-1114517539994314755742123619418806309674723751882, -1114517539994314755742123619418806309674721654729⟩, ⟨-1114517539994314755742123619418806307317581552533, -1114517539994314755742123619418806307317579455380⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1289211086540730807145370793336689628180868595695, 1289211086540730807145370793336689628180868595696⟩
def centerBExp : DyadicInterval precision := ⟨250382979112386790129325956464926003394575831256, 250382979112386790129325956464926005593599086809⟩
def centerBLog : DyadicInterval precision := ⟨231107915436303041556053545372254068568613319240, 231107915436303041556053545372254070767636574793⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨250382979112386790129325956464926003944331645144, scale precision, 250382979112386790129325956464926005043843272921, scale precision,
    0, 256, 0, 256, ⟨-2578422173081461614290741586673379259570698469527, -2578422173081461614290741586673379259570696372374⟩, ⟨-2578422173081461614290741586673379253152778010408, -2578422173081461614290741586673379253152775913255⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576086292890, 562362779591003425345044647758252905789383238158⟩
def wholeDExp : DyadicInterval precision := ⟨676986443527636285719880989929562986620669078430, 686842745746340006938348233447115253267032256778⟩
def wholeDLog : DyadicInterval precision := ⟨556298163020790248856133545839930268678058727022, 563018755595924057929845042473976397959717252098⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨676986443527636285719880989929562987170424892318, scale precision, 686842745746340006938348233447115252717276442890, scale precision,
    0, 256, 0, 256, ⟨-1124725559182006850690089295516505812765599299460, -1124725559182006850690089295516505812765597202307⟩, ⟨-1103600842485828909641620919934595875982373083786, -1103600842485828909641620919934595875982370986633⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576086292890, 562731109413180805839587549857455580404977831662⟩
def wholeCExp : DyadicInterval precision := ⟨676645299244374574149712381183709877916613542186, 686842745746340006938348233447115253267032256778⟩
def wholeCLog : DyadicInterval precision := ⟨556064997025759996947769307225918750787875486891, 563018755595924057929845042473976397959717252098⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨676645299244374574149712381183709878466369356074, scale precision, 686842745746340006938348233447115252717276442890, scale precision,
    0, 256, 0, 256, ⟨-1125462218826361611679175099714911161997386851483, -1125462218826361611679175099714911161997384754330⟩, ⟨-1103600842485828909641620919934595875982373083786, -1103600842485828909641620919934595875982370986633⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1274032259617610934704101070165693753025271828842, 1304478022594555801804565823310086935043472420366⟩
def wholeBExp : DyadicInterval precision := ⟨245206212213280183346701621037947492733329174206, 255638212317859769721570237654714803577288886836⟩
def wholeBLog : DyadicInterval precision := ⟨226681614754084983305211569741300249793778224442, 235587637306830322031458603850894454749299587498⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨245206212213280183346701621037947493283084988094, scale precision, 255638212317859769721570237654714803027533072948, scale precision,
    0, 256, 0, 256, ⟨-2608956045189111603609131646620173873363653338430, -2608956045189111603609131646620173873363651241277⟩, ⟨-2548064519235221869408202140331387502907552057214, -2548064519235221869408202140331387502907549960061⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0080StableWitnesses

end


