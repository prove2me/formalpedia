-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0649StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0649StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:41:15.514981+00:00
-- url     : https://prove2.me/theorems/584e727c-7766-426a-b868-ad3035cbb066
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0649StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0650StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0649StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0650StableWitnesses, GeneralCK.Certificates.E8TAxisProd0651StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0649StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0650StableWitnesses, GeneralCK.Certificates.E8TAxisProd0651StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0649StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0650StableWitnesses, GeneralCK.Certificates.E8TAxisProd0651StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0649StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0650StableWitnesses, GeneralCK/Certificates/E8TAxisProd0651StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0649StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0649StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨559832237304391780179534132609321768583233596123, 559832237304391780179534132609321768583233596124⟩
def centerCExp : DyadicInterval precision := ⟨679334867171768092808276961266907696055739934191, 679334867171768092808276961266907698254763189744⟩
def centerCLog : DyadicInterval precision := ⟨557902259778180435363823030149176458629549940208, 557902259778180435363823030149176460828573195761⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨679334867171768092808276961266907696605495748079, scale precision, 679334867171768092808276961266907697705007375856, scale precision,
    1, 128, 1, 128, ⟨-1119664474608783560359068265218643538349197202573, -1119664474608783560359068265218643538349195105420⟩, ⟨-1119664474608783560359068265218643535983739279074, -1119664474608783560359068265218643535983737181921⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1292856709371067593818087190420051297761852721804, 1292856709371067593818087190420051297761852721805⟩
def centerBExp : DyadicInterval precision := ⟨249136960993526905126134318574218697458045765349, 249136960993526905126134318574218699657069020902⟩
def centerBLog : DyadicInterval precision := ⟨230043754589442419180830415445676698546129931361, 230043754589442419180830415445676700745153186914⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨249136960993526905126134318574218698007801579237, scale precision, 249136960993526905126134318574218699107313207014, scale precision,
    2, 128, 2, 128, ⟨-2585713418742135187636174380840102598748715816079, -2585713418742135187636174380840102598748713718926⟩, ⟨-2585713418742135187636174380840102592298697168296, -2585713418742135187636174380840102592298695071143⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨554367321966725412501404840560804935824041534924, 565311208506485336356617145709055187973115398755⟩
def wholeCExp : DyadicInterval precision := ⟨674260445900196612400442935956116371784565410484, 684434312963729813210720852513958326789149513745⟩
def wholeCLog : DyadicInterval precision := ⟨554433952746197175533793686558852553507495090634, 561379398799910820490017985325895776145894628327⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨674260445900196612400442935956116372334321224372, scale precision, 684434312963729813210720852513958326239393699857, scale precision,
    1, 128, 1, 128, ⟨-1130622417012970672713234291418110377137861915764, -1130622417012970672713234291418110377137859818611⟩, ⟨-1108734643933450825002809681121609870474167196214, -1108734643933450825002809681121609870474165099061⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1277656756070646627611520284835694411902701476044, 1308144663050354424586377192523512508722977195421⟩
def wholeBExp : DyadicInterval precision := ⟨243978938664234210632066399729445589253278861036, 254373395756878607421932818328389432779750973040⟩
def wholeBLog : DyadicInterval precision := ⟨225630288065732009115102913342856962209799444726, 234510722920159910963279584564601633014762091959⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨243978938664234210632066399729445589803034674924, scale precision, 254373395756878607421932818328389432229995159152, scale precision,
    2, 128, 2, 128, ⟨-2616289326100708849172754385047025020739145525942, -2616289326100708849172754385047025020739143428789⟩, ⟨-2555313512141293255223040569671388820646783502087, -2555313512141293255223040569671388820646781404934⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0649StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0650StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0650StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨570064966314260557721028953970904897000065018732, 570064966314260557721028953970904897000065018733⟩
def centerCExp : DyadicInterval precision := ⟨669888411392651470720148223937885565986268317592, 669888411392651470720148223937885568185291573145⟩
def centerCLog : DyadicInterval precision := ⟨551439103896400134234211520026388351588277801208, 551439103896400134234211520026388353787301056761⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨669888411392651470720148223937885566536024131480, scale precision, 669888411392651470720148223937885567635535759257, scale precision,
    1, 128, 1, 128, ⟨-1140129932628521115442057907941809795199538343228, -1140129932628521115442057907941809795199536246075⟩, ⟨-1140129932628521115442057907941809792800723828853, -1140129932628521115442057907941809792800721731700⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1322466041258368850227635671365004731257517718201, 1322466041258368850227635671365004731257517718202⟩
def centerBExp : DyadicInterval precision := ⟨239243948261267134175407413231090795097457997809, 239243948261267134175407413231090797296481253362⟩
def centerBLog : DyadicInterval precision := ⟨221567022530285270899623367019449173101350935457, 221567022530285270899623367019449175300374191010⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨239243948261267134175407413231090795647213811697, scale precision, 239243948261267134175407413231090796746725439474, scale precision,
    2, 128, 2, 128, ⟨-2644932082516737700455271342730009465873403657774, -2644932082516737700455271342730009465873401560621⟩, ⟨-2644932082516737700455271342730009459156669312186, -2644932082516737700455271342730009459156667215033⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨564573717212589988802049639886580833192784064295, 575570529888895186894125723750830174364544602160⟩
def wholeCExp : DyadicInterval precision := ⟨664860357195718206921015152412430828588226085601, 674941269245691112931987249859655394253801811657⟩
def wholeCLog : DyadicInterval precision := ⟨547987276367338870454115335243794051658569342887, 554899765807588364467034805815025072325736826297⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨664860357195718206921015152412430829137981899489, scale precision, 674941269245691112931987249859655393704045997769, scale precision,
    1, 128, 1, 128, ⟨-1151141059777790373788251447501660349937568113598, -1151141059777790373788251447501660349937566016445⟩, ⟨-1129147434425179977604099279773161665195141122548, -1129147434425179977604099279773161665195139025395⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1307096539714816208897011159209337714689275829455, 1337922562257929098454499956600670000993129090162⟩
def wholeBExp : DyadicInterval precision := ⟨234236707301113389951991237045177443988521152645, 244329131221096763726132404765801153726259178070⟩
def wholeBLog : DyadicInterval precision := ⟨217257803753566517360725642633345753851756968255, 225930352730220451826365155835375139214773794480⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨234236707301113389951991237045177444538276966533, scale precision, 244329131221096763726132404765801153176503364182, scale precision,
    2, 128, 2, 128, ⟨-2675845124515858196908999913201340005416417684367, -2675845124515858196908999913201340005416415587214⟩, ⟨-2614193079429632417794022318418675426090082691185, -2614193079429632417794022318418675426090080594032⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0650StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0651StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0651StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨559464408879984511663588493001884773303676549345, 559464408879984511663588493001884773303676549346⟩
def centerCExp : DyadicInterval precision := ⟨679676901100538041171347359050893214378397471628, 679676901100538041171347359050893216577420727181⟩
def centerCLog : DyadicInterval precision := ⟨558135740110673900523927099133357937157785878733, 558135740110673900523927099133357939356809134286⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨679676901100538041171347359050893214928153285516, scale precision, 679676901100538041171347359050893216027664913293, scale precision,
    1, 128, 1, 128, ⟨-1118928817759969023327176986003769547789487924109, -1118928817759969023327176986003769547789485826956⟩, ⟨-1118928817759969023327176986003769545425220370425, -1118928817759969023327176986003769545425218273272⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1292335597378664498586091740723701315770072762051, 1292335597378664498586091740723701315770072762052⟩
def centerBExp : DyadicInterval precision := ⟨249314688554393141327265342402006574607244908363, 249314688554393141327265342402006576806268163916⟩
def centerBLog : DyadicInterval precision := ⟨230195590067151337710644840481568990154485559999, 230195590067151337710644840481568992353508815552⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨249314688554393141327265342402006575157000722251, scale precision, 249314688554393141327265342402006576256512350028, scale precision,
    2, 128, 2, 128, ⟨-2584671194757328997172183481447402634762856902300, -2584671194757328997172183481447402634762854805147⟩, ⟨-2584671194757328997172183481447402628317436243060, -2584671194757328997172183481447402628317434145907⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨554000433503825012123662242287602563121434110565, 564942430804982345369665948834805982555401644700⟩
def wholeCExp : DyadicInterval precision := ⟨674600801276555767032981701719573263344659852209, 684778033552071001269599362921260135936523380557⟩
def wholeCLog : DyadicInterval precision := ⟨554666839317544591819523572458185966636197088213, 561613472876357606435164045606356039849443743389⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨674600801276555767032981701719573263894415666097, scale precision, 684778033552071001269599362921260135386767566669, scale precision,
    1, 128, 1, 128, ⟨-1129884861609964690739331897669611966301833196243, -1129884861609964690739331897669611966301831099090⟩, ⟨-1108000867007650024247324484575205125069541588674, -1108000867007650024247324484575205125069539491521⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1277138660620720490328816060139948074117166135464, 1307620550225108951453861218728417427818316419909⟩
def wholeBExp : DyadicInterval precision := ⟨244153989249496857304327678935707645095471891777, 254553808047124850002238322115775943782643494172⟩
def wholeBLog : DyadicInterval precision := ⟨225780288946381983926347977281148734144393218493, 234664381544358065896158973909626127428570601881⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨244153989249496857304327678935707645645227705665, scale precision, 254553808047124850002238322115775943232887680284, scale precision,
    2, 128, 2, 128, ⟨-2615241100450217902907722437456834858927462863170, -2615241100450217902907722437456834858927460766017⟩, ⟨-2554277321241440980657632120279896145077951459442, -2554277321241440980657632120279896145077949362289⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0651StableWitnesses

end


