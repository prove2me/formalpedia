-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0098StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0098StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:49:21.862477+00:00
-- url     : https://prove2.me/theorems/4f8453d3-dc2f-44f9-956a-3ba0eebd6f24
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0098StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0099StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0098StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0099StableWitnesses, GeneralCK.Certificates.E8TAxisProd0100StableWitnesses, GeneralCK.Certificates.E8TAxisProd0101StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0098StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0099StableWitnesses, GeneralCK.Certificates.E8TAxisProd0100StableWitnesses, GeneralCK.Certificates.E8TAxisProd0101StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0098StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0099StableWitnesses, GeneralCK.Certificates.E8TAxisProd0100StableWitnesses, GeneralCK.Certificates.E8TAxisProd0101StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0098StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0099StableWitnesses, GeneralCK/Certificates/E8TAxisProd0100StableWitnesses, GeneralCK/Certificates/E8TAxisProd0101StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0098StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0098StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨521774884976969249658675544420781985592392356176, 521774884976969249658675544420781985592392356177⟩
def centerDExp : DyadicInterval precision := ⟨715651972798857079113875938009045310901254744990, 715651972798857079113875938009045313100278000543⟩
def centerDLog : DyadicInterval precision := ⟨582487198387037182294075308140412786716139382242, 582487198387037182294075308140412788915162637795⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨715651972798857079113875938009045311451010558878, scale precision, 715651972798857079113875938009045312550522186655, scale precision,
    1, 128, 1, 128, ⟨-1043549769953938499317351088841563972307494916592, -1043549769953938499317351088841563972307492819439⟩, ⟨-1043549769953938499317351088841563970062076605264, -1043549769953938499317351088841563970062074508111⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨526478861613850302028886964373422433379523083580, 526478861613850302028886964373422433379523083581⟩
def centerCExp : DyadicInterval precision := ⟨711059985780295810189542995482253678987001719091, 711059985780295810189542995482253681186024974644⟩
def centerCLog : DyadicInterval precision := ⟨579401387624920774589036381394031266287078043315, 579401387624920774589036381394031268486101298868⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨711059985780295810189542995482253679536757532979, scale precision, 711059985780295810189542995482253680636269160756, scale precision,
    1, 128, 1, 128, ⟨-1052957723227700604057773928746844867889006766546, -1052957723227700604057773928746844867889004669393⟩, ⟨-1052957723227700604057773928746844865629087664929, -1052957723227700604057773928746844865629085567776⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1196587188194301590119268398873116970050300724478, 1196587188194301590119268398873116970050300724479⟩
def centerBExp : DyadicInterval precision := ⟨284218511261966000192025146338382814509663797362, 284218511261966000192025146338382816708687052915⟩
def centerBLog : DyadicInterval precision := ⟨259712841443981964471114110510707626948382461026, 259712841443981964471114110510707629147405716579⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨284218511261966000192025146338382815059419611250, scale precision, 284218511261966000192025146338382816158931239027, scale precision,
    2, 128, 2, 128, ⟨-2393174376388603180238536797746233942927543707532, -2393174376388603180238536797746233942927541610379⟩, ⟨-2393174376388603180238536797746233937273661287539, -2393174376388603180238536797746233937273659190386⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207656619, 530829944683894805437507571749273968698214433228⟩
def wholeDExp : DyadicInterval precision := ⟨706838726837510462039096914346652691200364343781, 724538456853667540563062557829026726602043072281⟩
def wholeDLog : DyadicInterval precision := ⟨576558946667156773600005109862481905428300877399, 588440465573623044036052405976243775513762722746⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨706838726837510462039096914346652691750120157669, scale precision, 724538456853667540563062557829026726052287258393, scale precision,
    1, 128, 1, 128, ⟨-1061659889367789610875015143498547938533137613158, -1061659889367789610875015143498547938533135516005⟩, ⟨-1025513577573426628040534407815242047325477264753, -1025513577573426628040534407815242047325475167600⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨517080903253858724479821545266433656629178962643, 535917167730891734974320790035632740349206219595⟩
def wholeCExp : DyadicInterval precision := ⟨701935059713448710774949602322905770760906081659, 720263763078351723939126946140723372663436309961⟩
def wholeCLog : DyadicInterval precision := ⟨573250041111403925372130580605861775715407636155, 585579773194305697767237721657314088274161012885⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨701935059713448710774949602322905771310661895547, scale precision, 720263763078351723939126946140723372113680496073, scale precision,
    1, 128, 1, 128, ⟨-1071834335461783469948641580071265481843062142953, -1071834335461783469948641580071265481843060045800⟩, ⟨-1034161806507717448959643090532867312142838433587, -1034161806507717448959643090532867312142836336434⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1171144955587102782159908169153948354199385171152, 1222302780545042373853028266866491130114135756470⟩
def wholeBExp : DyadicInterval precision := ⟨274390617798940080959525412194042380237613179540, 294288303832079559270900740887785187589469331893⟩
def wholeBLog : DyadicInterval precision := ⟨251461767589292954756163572612693252937493334323, 268118962531160869082445484402528751578382204909⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨274390617798940080959525412194042380787368993428, scale precision, 294288303832079559270900740887785187039713518005, scale precision,
    2, 128, 2, 128, ⟨-2444605561090084747706056533732982263156466785411, -2444605561090084747706056533732982263156464688258⟩, ⟨-2342289911174205564319816338307896705668560873960, -2342289911174205564319816338307896705668558776807⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0098StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0099StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0099StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨503775002792062322984841617274484055444075625516, 503775002792062322984841617274484055444075625517⟩
def centerDExp : DyadicInterval precision := ⟨733498839633313504812043629918338881519303578660, 733498839633313504812043629918338883718326834213⟩
def centerDLog : DyadicInterval precision := ⟨594418786089508030264928688350882176985232861495, 594418786089508030264928688350882179184256117048⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨733498839633313504812043629918338882069059392548, scale precision, 733498839633313504812043629918338883168571020325, scale precision,
    0, 128, 0, 128, ⟨-1007550005584124645969683234548968111983544655694, -1007550005584124645969683234548968111983542558541⟩, ⟨-1007550005584124645969683234548968109792759943527, -1007550005584124645969683234548968109792757846374⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨508441040167376606838902034929793051743084682935, 508441040167376606838902034929793051743084682936⟩
def centerCExp : DyadicInterval precision := ⟨728830176603751787447408302984071750489798731807, 728830176603751787447408302984071752688821987360⟩
def centerCLog : DyadicInterval precision := ⟨591306930117352169181636152845170141476722691959, 591306930117352169181636152845170143675745947512⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨728830176603751787447408302984071751039554545695, scale precision, 728830176603751787447408302984071752139066173472, scale precision,
    1, 128, 1, 128, ⟨-1016882080334753213677804069859586104588579518685, -1016882080334753213677804069859586104588577421532⟩, ⟨-1016882080334753213677804069859586102383761310212, -1016882080334753213677804069859586102383759213059⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1146958416022670209602122673745317606680055048711, 1146958416022670209602122673745317606680055048712⟩
def centerBExp : DyadicInterval precision := ⟨304191706449954360834546871654950316240731543154, 304191706449954360834546871654950318439754798707⟩
def centerBLog : DyadicInterval precision := ⟨276339292504471584144944983901747984420211277888, 276339292504471584144944983901747986619234533441⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨304191706449954360834546871654950316790487357042, scale precision, 304191706449954360834546871654950317889998984819, scale precision,
    2, 128, 2, 128, ⟨-2293916832045340419204245347490635216001435695926, -2293916832045340419204245347490635216001433598773⟩, ⟨-2293916832045340419204245347490635210718786596074, -2293916832045340419204245347490635210718784498921⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨494828875109284674194281948410566590218630888609, 512756788786713314020267203907621024217207656620⟩
def wholeDExp : DyadicInterval precision := ⟨724538456853667540563062557829026724403019816728, 742533801492811413004049823802046285637355489138⟩
def wholeDLog : DyadicInterval precision := ⟨588440465573623044036052405976243773314739467193, 600422206098217740957049834384989022236361477122⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨724538456853667540563062557829026724952775630616, scale precision, 742533801492811413004049823802046285087599675250, scale precision,
    1, 128, 0, 128, ⟨-1025513577573426628040534407815242049543355458877, -1025513577573426628040534407815242049543353361724⟩, ⟨-989657750218569348388563896821133179355198924442, -989657750218569348388563896821133179355196827289⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨499118607398289371570928132321858375692748600603, 517802407414192458596602619857206278120042976221⟩
def wholeCExp : DyadicInterval precision := ⟨719552964234240380085322697203156706210064698294, 738187668517019050850553078864002936812619200002⟩
def wholeCLog : DyadicInterval precision := ⟨585103551996455244053877469859303467230213698372, 597537428828638861458087364241545119280449804656⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨719552964234240380085322697203156706759820512182, scale precision, 738187668517019050850553078864002936262863386114, scale precision,
    1, 128, 0, 128, ⟨-1035604814828384917193205239714412557356709490352, -1035604814828384917193205239714412557356707393199⟩, ⟨-998237214796578743141856264643716750297063619408, -998237214796578743141856264643716750297061522255⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1122053208859200700154292179899125256064598893419, 1172137532782407255992094556070555879213430571069⟩
def wholeBExp : DyadicInterval precision := ⟨293888844044208371914310153888165330355381513854, 314737760101076424029552099602696282158309778498⟩
def wholeBLog : DyadicInterval precision := ⟨267786418448382937857984319900609370521124917705, 285042518315165146381454777827418238556269984099⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨293888844044208371914310153888165330905137327742, scale precision, 314737760101076424029552099602696281608553964610, scale precision,
    2, 128, 2, 128, ⟨-2344275065564814511984189112141111761160783666172, -2344275065564814511984189112141111761160781569019⟩, ⟨-2244106417718401400308584359798250509576378284516, -2244106417718401400308584359798250509576376187363⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0099StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0100StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0100StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨485917755434160891773462032334740628415117575842, 485917755434160891773462032334740628415117575843⟩
def centerDExp : DyadicInterval precision := ⟨751644042802555100556006121456236859448629838317, 751644042802555100556006121456236861647653093870⟩
def centerDLog : DyadicInterval precision := ⟨606450780028547033690895338790838686899984128629, 606450780028547033690895338790838689099007384182⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨751644042802555100556006121456236859998385652205, scale precision, 751644042802555100556006121456236861097897279982, scale precision,
    0, 128, 0, 128, ⟨-971835510868321783546924064669481257899185032921, -971835510868321783546924064669481257899182935768⟩, ⟨-971835510868321783546924064669481255761287367599, -971835510868321783546924064669481255761285270446⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨491260262639210688503725366833109179054857067928, 491260262639210688503725366833109179054857067929⟩
def centerCExp : DyadicInterval precision := ⟨746168824582666118646004178152567264352531769318, 746168824582666118646004178152567266551555024871⟩
def centerCLog : DyadicInterval precision := ⟨602830613874854851411479568809979205723748720369, 602830613874854851411479568809979207922771975922⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨746168824582666118646004178152567264902287583206, scale precision, 746168824582666118646004178152567266001799210983, scale precision,
    0, 128, 0, 128, ⟨-982520525278421377007450733666218359186507722073, -982520525278421377007450733666218359186505624920⟩, ⟨-982520525278421377007450733666218357032922646793, -982520525278421377007450733666218357032920549640⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1099343553233376023428059844788492620459352566382, 1099343553233376023428059844788492620459352566383⟩
def centerBExp : DyadicInterval precision := ⟨324672485839547658972099739765453066967529900514, 324672485839547658972099739765453069166553156067⟩
def centerBLog : DyadicInterval precision := ⟨293194101779609656321609083509852594322702602221, 293194101779609656321609083509852596521725857774⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨324672485839547658972099739765453067517285714402, scale precision, 324672485839547658972099739765453068616797342179, scale precision,
    2, 128, 2, 128, ⟨-2198687106466752046856119689576985243393412407380, -2198687106466752046856119689576985243393410310227⟩, ⟨-2198687106466752046856119689576985238443999955305, -2198687106466752046856119689576985238443997858152⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660670039, 494828875109284674194281948410566590218630888610⟩
def wholeDExp : DyadicInterval precision := ⟨742533801492811413004049823802046283438332233585, 760830284245465294695388294487623571972247912142⟩
def wholeDLog : DyadicInterval precision := ⟨600422206098217740957049834384989020037338221569, 612504570538325940964339858761912612235438761042⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨742533801492811413004049823802046283988088047473, scale precision, 760830284245465294695388294487623571422492098254, scale precision,
    0, 128, 0, 128, ⟨-989657750218569348388563896821133181519326727149, -989657750218569348388563896821133181519324629996⟩, ⟨-954081990347252967270622047885287015887280011311, -954081990347252967270622047885287015887277914158⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨482007786130042976079423016479978656483757791435, 500550322985418952666290655314410717262742449184⟩
def wholeCExp : DyadicInterval precision := ⟨736742798248134475464905005390791339684068173481, 755676582462510672810870636297793316747703244389⟩
def wholeCLog : DyadicInterval precision := ⟨596577123165191194143973799773058819722819201776, 609111337168988866760315408143063291199349435482⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨736742798248134475464905005390791340233823987369, scale precision, 755676582462510672810870636297793316197947430501, scale precision,
    0, 128, 0, 128, ⟨-1001100645970837905332581310628821435616055171427, -1001100645970837905332581310628821435616053074274⟩, ⟨-964015572260085952158846032959957311904272062571, -964015572260085952158846032959957311904269965418⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1074963222308169530738355822332334674092166935416, 1123996665544878201776350498448307710419648388093⟩
def wholeBExp : DyadicInterval precision := ⟨313901816413754710054927527111402017448199317670, 335687389019916391127786100804902468095355986963⟩
def wholeBLog : DyadicInterval precision := ⟨284354536363436548255244512211034327770576236354, 302179152451433942014594394836555380007291007228⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨313901816413754710054927527111402017997955131558, scale precision, 335687389019916391127786100804902467545600173075, scale precision,
    2, 128, 2, 128, ⟨-2247993331089756403552700996896615423398916725058, -2247993331089756403552700996896615423398914627905⟩, ⟨-2149926444616339061476711644664669345790831176313, -2149926444616339061476711644664669345790829079160⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0100StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0101StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0101StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423975668, 468197947567212351774406011872494977440423975669⟩
def centerDExp : DyadicInterval precision := ⟨770093267120006045819929989156897110520154385328, 770093267120006045819929989156897112719177640881⟩
def centerDLog : DyadicInterval precision := ⟨618583648477847123240200594096127216349000772546, 618583648477847123240200594096127218548024028099⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨770093267120006045819929989156897111069910199216, scale precision, 770093267120006045819929989156897112169421826993, scale precision,
    0, 128, 0, 128, ⟨-936395895134424703548812023744989955924188886698, -936395895134424703548812023744989955924186789545⟩, ⟨-936395895134424703548812023744989953837509113130, -936395895134424703548812023744989953837507015977⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨473499766766969430535194678971917222337722408434, 473499766766969430535194678971917222337722408435⟩
def centerCExp : DyadicInterval precision := ⟨764526226211062276210152717028259384498280409473, 764526226211062276210152717028259386697303665026⟩
def centerCLog : DyadicInterval precision := ⟨614933162980520603857715028219585012854342644243, 614933162980520603857715028219585015053365899796⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨764526226211062276210152717028259385048036223361, scale precision, 764526226211062276210152717028259386147547851138, scale precision,
    0, 128, 0, 128, ⟨-946999533533938861070389357943834445726383027030, -946999533533938861070389357943834445726380929877⟩, ⟨-946999533533938861070389357943834443624508703863, -946999533533938861070389357943834443624506606710⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1051794805098048310997254241086461388309395687097, 1051794805098048310997254241086461388309395687098⟩
def centerBExp : DyadicInterval precision := ⟨346500854857844218084700810375518373066973766248, 346500854857844218084700810375518375265997021801⟩
def centerBLog : DyadicInterval precision := ⟨310946478869210105361260377803755421747577408728, 310946478869210105361260377803755423946600664281⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨346500854857844218084700810375518373616729580136, scale precision, 346500854857844218084700810375518374716241207913, scale precision,
    2, 128, 2, 128, ⟨-2103589610196096621994508482172922778937600618672, -2103589610196096621994508482172922778937598521519⟩, ⟨-2103589610196096621994508482172922774299984226875, -2103589610196096621994508482172922774299982129722⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 477040995173626483635311023942643508471660670040⟩
def wholeDExp : DyadicInterval precision := ⟨760830284245465294695388294487623569773224656589, 779433753649515438129873373659005449491648691216⟩
def wholeDLog : DyadicInterval precision := ⟨612504570538325940964339858761912610036415505489, 624688092853175616303270580088334960516446661035⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨760830284245465294695388294487623570322980470477, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 128, 0, 128, ⟨-954081990347252967270622047885287017999364766000, -954081990347252967270622047885287017999362668847⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨464317520570543262685438368413322148488176723288, 482718197352636543622438493700548396440629975996⟩
def wholeCExp : DyadicInterval precision := ⟨754942296237604903475162707468836664480824508748, 774193486905237225075220857173521085012262777837⟩
def wholeCLog : DyadicInterval precision := ⟨608627236137074120034196491672862212953790171103, 621266473892704420673683486048983723288348836865⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨754942296237604903475162707468836665030580322636, scale precision, 774193486905237225075220857173521084462506963949, scale precision,
    0, 128, 0, 128, ⟨-965436394705273087244876987401096793945539722443, -965436394705273087244876987401096793945537625290⟩, ⟨-928635041141086525370876736826644295938540259151, -928635041141086525370876736826644295938538161998⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1027945442466337676253244334030770129808762546613, 1075914188409084406234053045767879973346554861303⟩
def wholeBExp : DyadicInterval precision := ⟨335250824741947781310587095664936025324142010644, 357996094801976668402723771470780134615192916776⟩
def wholeBLog : DyadicInterval precision := ⟨301824088568371474149304468235106268985714911103, 320209258854130237353084392786872702854828049554⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨335250824741947781310587095664936025873897824532, scale precision, 357996094801976668402723771470780134065437102888, scale precision,
    2, 128, 2, 128, ⟨-2151828376818168812468106091535759949089731339521, -2151828376818168812468106091535759949089729242368⟩, ⟨-2055890884932675352506488668061540257373174782120, -2055890884932675352506488668061540257373172684967⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0101StableWitnesses

end


