-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0656StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0656StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:43:37.166916+00:00
-- url     : https://prove2.me/theorems/e31f46ed-e1b1-41f6-83bd-d63d6ccc9cd6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0656StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0657StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0656StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0657StableWitnesses, GeneralCK.Certificates.E8TAxisProd0658StableWitnesses, GeneralCK.Certificates.E8TAxisProd0659StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0656StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0657StableWitnesses, GeneralCK.Certificates.E8TAxisProd0658StableWitnesses, GeneralCK.Certificates.E8TAxisProd0659StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0656StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0657StableWitnesses, GeneralCK.Certificates.E8TAxisProd0658StableWitnesses, GeneralCK.Certificates.E8TAxisProd0659StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0656StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0657StableWitnesses, GeneralCK/Certificates/E8TAxisProd0658StableWitnesses, GeneralCK/Certificates/E8TAxisProd0659StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0656StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0656StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    1, 128, 1, 128, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨569695359445498168827790685159966715114997376962, 569695359445498168827790685159966715114997376963⟩
def centerCExp : DyadicInterval precision := ⟨670227320331355657755015771564466160575838396500, 670227320331355657755015771564466162774861652053⟩
def centerCLog : DyadicInterval precision := ⟨551671476471091929340457503094624551269333252163, 551671476471091929340457503094624553468356507716⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨670227320331355657755015771564466161125594210388, scale precision, 670227320331355657755015771564466162225105838165, scale precision,
    1, 128, 1, 128, ⟨-1139390718890996337655581370319933431428796564208, -1139390718890996337655581370319933431428794467055⟩, ⟨-1139390718890996337655581370319933429031195040794, -1139390718890996337655581370319933429031192943641⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1321939148401082361866470548660947979352780463142, 1321939148401082361866470548660947979352780463143⟩
def centerBExp : DyadicInterval precision := ⟨239416512396960155624572397512519630159912923768, 239416512396960155624572397512519632358936179321⟩
def centerBLog : DyadicInterval precision := ⟨221715304539737072520148500046572117285482481373, 221715304539737072520148500046572119484505736926⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨239416512396960155624572397512519630709668737656, scale precision, 239416512396960155624572397512519631809180365433, scale precision,
    2, 128, 2, 128, ⟨-2643878296802164723732941097321895962061508538805, -2643878296802164723732941097321895962061506441652⟩, ⟨-2643878296802164723732941097321895955349615410916, -2643878296802164723732941097321895955349613313763⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    1, 128, 1, 128, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨564205067687189853845881125555872156660370192906, 575199956354761874027607352138967666646960359556⟩
def wholeCExp : DyadicInterval precision := ⟨665197602297262480394241949302208252998302479280, 675281849843595152205478389139814755356153150977⟩
def wholeCLog : DyadicInterval precision := ⟨548219054957857923084002447512401365469397647163, 555132732215949853827122422198232930680792640172⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨665197602297262480394241949302208253548058293168, scale precision, 675281849843595152205478389139814754806397337089, scale precision,
    1, 128, 1, 128, ⟨-1150399912709523748055214704277935334501786948432, -1150399912709523748055214704277935334501784851279⟩, ⟨-1128410135374379707691762251111744312130913776032, -1128410135374379707691762251111744312130911678879⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1306572631539740667678882765120761002674555975488, 1337392703662314096496633829876186941999603082722⟩
def wholeBExp : DyadicInterval precision := ⟨234406611099583502268620101840126288023763193563, 244504364588746798046209933348468434440968207606⟩
def wholeBLog : DyadicInterval precision := ⟨217404230967043559620593402306920621672402443510, 226080479404613096437813021508376152748083239832⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨234406611099583502268620101840126288573519007451, scale precision, 244504364588746798046209933348468433891212393718, scale precision,
    2, 128, 2, 128, ⟨-2674785407324628192993267659752373887426879404500, -2674785407324628192993267659752373887426877307347⟩, ⟨-2613145263079481335357765530241522002062999790563, -2613145263079481335357765530241522002062997693410⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0656StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0657StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0657StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨557075069631301290362165038182134082283955558325, 557075069631301290362165038182134082283955558326⟩
def centerDExp : DyadicInterval precision := ⟨681902880895464588128477464036409276306339175751, 681902880895464588128477464036409278505362431304⟩
def centerDLog : DyadicInterval precision := ⟨559654335205987407427227649575573486508888333329, 559654335205987407427227649575573488707911588882⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨681902880895464588128477464036409276856094989639, scale precision, 681902880895464588128477464036409277955606617416, scale precision,
    1, 128, 1, 128, ⟨-1114150139262602580724330076364268165746187026121, -1114150139262602580724330076364268165746184928968⟩, ⟨-1114150139262602580724330076364268163389637304333, -1114150139262602580724330076364268163389635207180⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨559096643938295444768441210219723585326011288331, 559096643938295444768441210219723585326011288332⟩
def centerCExp : DyadicInterval precision := ⟨680019048162278142566478875999567438596700656707, 680019048162278142566478875999567440795723912260⟩
def centerCLog : DyadicInterval precision := ⟨558369260358470676078275148669503361277725524154, 558369260358470676078275148669503363476748779707⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨680019048162278142566478875999567439146456470595, scale precision, 680019048162278142566478875999567440245968098372, scale precision,
    1, 128, 1, 128, ⟨-1118193287876590889536882420439447171833562619334, -1118193287876590889536882420439447171833560522181⟩, ⟨-1118193287876590889536882420439447169470484631147, -1118193287876590889536882420439447169470482533994⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1291814588266190244138778126186237175422196645198, 1291814588266190244138778126186237175422196645199⟩
def centerBExp : DyadicInterval precision := ⟨249492507776081805128094325883076439797217117861, 249492507776081805128094325883076441996240373414⟩
def centerBLog : DyadicInterval precision := ⟨230347488067396491568849698918072470849260977066, 230347488067396491568849698918072473048284232619⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨249492507776081805128094325883076440346972931749, scale precision, 249492507776081805128094325883076441446484559526, scale precision,
    2, 128, 2, 128, ⟨-2583629176532380488277556252372474354064807766584, -2583629176532380488277556252372474354064805669431⟩, ⟨-2583629176532380488277556252372474347623980911363, -2583629176532380488277556252372474347623978814210⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576086292890, 562362779591003425345044647758252905789383238158⟩
def wholeDExp : DyadicInterval precision := ⟨676986443527636285719880989929562986620669078430, 686842745746340006938348233447115253267032256778⟩
def wholeDLog : DyadicInterval precision := ⟨556298163020790248856133545839930268678058727022, 563018755595924057929845042473976397959717252098⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨676986443527636285719880989929562987170424892318, scale precision, 686842745746340006938348233447115252717276442890, scale precision,
    1, 128, 1, 128, ⟨-1124725559182006850690089295516505812765599299460, -1124725559182006850690089295516505812765597202307⟩, ⟨-1103600842485828909641620919934595875982373083786, -1103600842485828909641620919934595875982370986633⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨553633607897550914157789526569935476549321922278, 564573717212589988802049639886580833192784064296⟩
def wholeCExp : DyadicInterval precision := ⟨674941269245691112931987249859655392054778556104, 685121867823938455553124774054258056166973202202⟩
def wholeCLog : DyadicInterval precision := ⟨554899765807588364467034805815025070126713570744, 561847586869509954488003537012061233542146546610⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨674941269245691112931987249859655392604534369992, scale precision, 685121867823938455553124774054258055617217388314, scale precision,
    1, 128, 1, 128, ⟨-1129147434425179977604099279773161667575997231786, -1129147434425179977604099279773161667575995134633⟩, ⟨-1107267215795101828315579053139870951925906056637, -1107267215795101828315579053139870951925903959484⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1276620668557843420799081521959812638844280769426, 1307096539714816208897011159209337714689275829456⟩
def wholeBExp : DyadicInterval precision := ⟨244329131221096763726132404765801151527235922517, 254734312253380017210503759009619484675071365242⟩
def wholeBLog : DyadicInterval precision := ⟨225930352730220451826365155835375137015750538927, 234818102288242134203976341290218380118070065899⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨244329131221096763726132404765801152076991736405, scale precision, 254734312253380017210503759009619484125315551354, scale precision,
    2, 128, 2, 128, ⟨-2614193079429632417794022318418675432667022723794, -2614193079429632417794022318418675432667020626641⟩, ⟨-2553241337115686841598163043919625274534417333016, -2553241337115686841598163043919625274534415235863⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0657StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0658StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0658StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    1, 128, 1, 128, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨569325817228205769367198837274040251200767229140, 569325817228205769367198837274040251200767229141⟩
def centerCExp : DyadicInterval precision := ⟨670566341403569248332795188160678622665755800426, 670566341403569248332795188160678624864779055979⟩
def centerCLog : DyadicInterval precision := ⟨551903888971295430417460471562489158433141224965, 551903888971295430417460471562489160632164480518⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨670566341403569248332795188160678623215511614314, scale precision, 670566341403569248332795188160678624315023242091, scale precision,
    1, 128, 1, 128, ⟨-1138651634456411538734397674548080503599730185772, -1138651634456411538734397674548080503599728088619⟩, ⟨-1138651634456411538734397674548080501203340827939, -1138651634456411538734397674548080501203338730786⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1321412357280873820208320378945828991986417977257, 1321412357280873820208320378945828991986417977258⟩
def centerBExp : DyadicInterval precision := ⟨239589167645098337004148365238074491999124436199, 239589167645098337004148365238074494198147691752⟩
def centerBLog : DyadicInterval precision := ⟨221863649785986628315583887212898417275935973046, 221863649785986628315583887212898419474959228599⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨239589167645098337004148365238074492548880250087, scale precision, 239589167645098337004148365238074493648391877864, scale precision,
    2, 128, 2, 128, ⟨-2642824714561747640416640757891657987326365169778, -2642824714561747640416640757891657987326363072625⟩, ⟨-2642824714561747640416640757891657980619308836410, -2642824714561747640416640757891657980619306739257⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    1, 128, 1, 128, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨563836482186664586868762355269953816856601623546, 574829448098859215518237886076935244653154005077⟩
def wholeCExp : DyadicInterval precision := ⟨665534959011211340744417088981921266433906730018, 675622543106306835869801034784431139780402768783⟩
def wholeCLog : DyadicInterval precision := ⟨548450873486251373841944323417891072930663291464, 555365738542272130768338963573596590736534936518⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨665534959011211340744417088981921266983662543906, scale precision, 675622543106306835869801034784431139230646954895, scale precision,
    1, 128, 1, 128, ⟨-1149658896197718431036475772153870490513561977981, -1149658896197718431036475772153870490513559880828⟩, ⟨-1127672964373329173737524710539907632523976626569, -1127672964373329173737524710539907632523974529416⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1306048825720079839332440124863662368079828962765, 1336862946128872783326455698680329416807435664232⟩
def wholeBExp : DyadicInterval precision := ⟨234576605696187466204238219259251132188395913473, 244679689362136224332927205796418728371214430263⟩
def wholeBLog : DyadicInterval precision := ⟨217550721751784476750157391975104738432236294746, 226230668956898312611909370341621430606033968910⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨234576605696187466204238219259251132738151727361, scale precision, 244679689362136224332927205796418727821458616375, scale precision,
    2, 128, 2, 128, ⟨-2673725892257745566652911397360658837040060578336, -2673725892257745566652911397360658837040058481183⟩, ⟨-2612097651440159678664880249727324732875900423388, -2612097651440159678664880249727324732875898326235⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0658StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0659StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0659StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨557075069631301290362165038182134082283955558325, 557075069631301290362165038182134082283955558326⟩
def centerDExp : DyadicInterval precision := ⟨681902880895464588128477464036409276306339175751, 681902880895464588128477464036409278505362431304⟩
def centerDLog : DyadicInterval precision := ⟨559654335205987407427227649575573486508888333329, 559654335205987407427227649575573488707911588882⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨681902880895464588128477464036409276856094989639, scale precision, 681902880895464588128477464036409277955606617416, scale precision,
    1, 128, 1, 128, ⟨-1114150139262602580724330076364268165746187026121, -1114150139262602580724330076364268165746184928968⟩, ⟨-1114150139262602580724330076364268163389637304333, -1114150139262602580724330076364268163389635207180⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨558728942437224164740777857921864819994064845159, 558728942437224164740777857921864819994064845160⟩
def centerCExp : DyadicInterval precision := ⟨680361308393674666798823525639238831472540899914, 680361308393674666798823525639238833671564155467⟩
def centerCLog : DyadicInterval precision := ⟨558602820521514784254064404429501622644110757541, 558602820521514784254064404429501624843134013094⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨680361308393674666798823525639238832022296713802, scale precision, 680361308393674666798823525639238833121808341579, scale precision,
    1, 128, 1, 128, ⟨-1117457884874448329481555715843729641169075352027, -1117457884874448329481555715843729641169073254874⟩, ⟨-1117457884874448329481555715843729638807186125765, -1117457884874448329481555715843729638807184028612⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1291293682051940478814179554154457827114433973311, 1291293682051940478814179554154457827114433973312⟩
def centerBExp : DyadicInterval precision := ⟨249670418667630405497187512708287427733845417881, 249670418667630405497187512708287429932868673434⟩
def centerBLog : DyadicInterval precision := ⟨230499448576764817794397673845043439680911834136, 230499448576764817794397673845043441879935089689⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨249670418667630405497187512708287428283601231769, scale precision, 249670418667630405497187512708287429383112859546, scale precision,
    2, 128, 2, 128, ⟨-2582587364103880957628359108308915657446987611004, -2582587364103880957628359108308915657446985513851⟩, ⟨-2582587364103880957628359108308915651010750379393, -2582587364103880957628359108308915651010748282240⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576086292890, 562362779591003425345044647758252905789383238158⟩
def wholeDExp : DyadicInterval precision := ⟨676986443527636285719880989929562986620669078430, 686842745746340006938348233447115253267032256778⟩
def wholeDLog : DyadicInterval precision := ⟨556298163020790248856133545839930268678058727022, 563018755595924057929845042473976397959717252098⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨676986443527636285719880989929562987170424892318, scale precision, 686842745746340006938348233447115252717276442890, scale precision,
    1, 128, 1, 128, ⟨-1124725559182006850690089295516505812765599299460, -1124725559182006850690089295516505812765597202307⟩, ⟨-1103600842485828909641620919934595875982373083786, -1103600842485828909641620919934595875982370986633⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨553266845105825401578653874119041810733668328700, 564205067687189853845881125555872156660370192907⟩
def wholeCExp : DyadicInterval precision := ⟨675281849843595152205478389139814753157129895424, 685465815816718325286236828578716248540413638379⟩
def wholeCLog : DyadicInterval precision := ⟨555132732215949853827122422198232928481769384619, 562081740779633923807161822383196504726431513338⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨675281849843595152205478389139814753706885709312, scale precision, 685465815816718325286236828578716247990657824491, scale precision,
    1, 128, 1, 128, ⟨-1128410135374379707691762251111744314510569092745, -1128410135374379707691762251111744314510566995592⟩, ⟨-1106533690211650803157307748238083620295187317743, -1106533690211650803157307748238083620295185220590⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1276102779898324103612680011995866951452899594356, 1306572631539740667678882765120761002674555975489⟩
def wholeBExp : DyadicInterval precision := ⟨244504364588746798046209933348468432241944952053, 254914908384038885953418573325154939954116337867⟩
def wholeBLog : DyadicInterval precision := ⟨226080479404613096437813021508376150549059984279, 234971885137661664279191325295117983947356765028⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨244504364588746798046209933348468432791700765941, scale precision, 254914908384038885953418573325154939404360523979, scale precision,
    2, 128, 2, 128, ⟨-2613145263079481335357765530241522008635226208538, -2613145263079481335357765530241522008635224111385⟩, ⟨-2552205559796648207225360023991733899753889557667, -2552205559796648207225360023991733899753887460514⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0659StableWitnesses

end


