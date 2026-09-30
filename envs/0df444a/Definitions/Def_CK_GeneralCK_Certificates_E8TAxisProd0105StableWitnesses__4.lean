-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0105StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0105StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:20:04.497217+00:00
-- url     : https://prove2.me/theorems/4c5f6da8-c8a5-4a90-a541-344a368e283d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0105StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0106StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0105StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0106StableWitnesses, GeneralCK.Certificates.E8TAxisProd0107StableWitnesses, GeneralCK.Certificates.E8TAxisProd0108StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0105StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0106StableWitnesses, GeneralCK.Certificates.E8TAxisProd0107StableWitnesses, GeneralCK.Certificates.E8TAxisProd0108StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0105StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0106StableWitnesses, GeneralCK.Certificates.E8TAxisProd0107StableWitnesses, GeneralCK.Certificates.E8TAxisProd0108StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0105StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0106StableWitnesses, GeneralCK/Certificates/E8TAxisProd0107StableWitnesses, GeneralCK/Certificates/E8TAxisProd0108StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0105StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0105StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨507722557010769154305650749367581798758032415118, 507722557010769154305650749367581798758032415119⟩
def centerCExp : DyadicInterval precision := ⟨729547123759412894980635572566989095739506419533, 729547123759412894980635572566989097938529675086⟩
def centerCLog : DyadicInterval precision := ⟨591785235725955800449648385601065453094649063577, 591785235725955800449648385601065455293672319130⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨729547123759412894980635572566989096289262233421, scale precision, 729547123759412894980635572566989097388773861198, scale precision,
    1, 128, 1, 128, ⟨-1015445114021538308611301498735163598617391613593, -1015445114021538308611301498735163598617389516440⟩, ⟨-1015445114021538308611301498735163596414740144035, -1015445114021538308611301498735163596414738046882⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1145976582175476597014753812657980168745360623862, 1145976582175476597014753812657980168745360623863⟩
def centerBExp : DyadicInterval precision := ⟨304600691891651259908859969565694911635909456168, 304600691891651259908859969565694913834932711721⟩
def centerBLog : DyadicInterval precision := ⟨276677779184165629545282411551707561112875931311, 276677779184165629545282411551707563311899186864⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨304600691891651259908859969565694912185665270056, scale precision, 304600691891651259908859969565694913285176897833, scale precision,
    2, 128, 2, 128, ⟨-2291953164350953194029507625315960340128500356293, -2291953164350953194029507625315960340128498259140⟩, ⟨-2291953164350953194029507625315960334852944236309, -2291953164350953194029507625315960334852942139156⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨498403088841403716691900621082853263505200073820, 517080903253858724479821545266433656629178962644⟩
def wholeCExp : DyadicInterval precision := ⟨720263763078351723939126946140723370464413054408, 738910822887504142320836990661289073696853549819⟩
def wholeCLog : DyadicInterval precision := ⟨585579773194305697767237721657314086075137757332, 598017822856874087207046540887019996694390588620⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨720263763078351723939126946140723371014168868296, scale precision, 738910822887504142320836990661289073147097735931, scale precision,
    1, 128, 0, 128, ⟨-1034161806507717448959643090532867314373879514139, -1034161806507717448959643090532867314373877416986⟩, ⟨-996806177682807433383801242165706525923031790815, -996806177682807433383801242165706525923029693662⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1121082111583694487816978874813616567839818458994, 1171144955587102782159908169153948354199385171153⟩
def wholeBExp : DyadicInterval precision := ⟨294288303832079559270900740887785185390446076340, 315156294226780944930623079599417868701486439346⟩
def wholeBLog : DyadicInterval precision := ⟨268118962531160869082445484402528749379358949356, 285386850422842140637473368842542941283288282373⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨294288303832079559270900740887785185940201890228, scale precision, 315156294226780944930623079599417868151730625458, scale precision,
    2, 128, 2, 128, ⟨-2342289911174205564319816338307896711128981907809, -2342289911174205564319816338307896711128979810656⟩, ⟨-2242164223167388975633957749627233133130207614550, -2242164223167388975633957749627233133130205517397⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0105StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0106StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0106StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨525030414114121795123384426163503389064600103020, 525030414114121795123384426163503389064600103021⟩
def centerCExp : DyadicInterval precision := ⟨712470801123454174025828475395733100551999331076, 712470801123454174025828475395733102751022586629⟩
def centerCLog : DyadicInterval precision := ⟨580350147706955188358994362502745539689441653525, 580350147706955188358994362502745541888464909078⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨712470801123454174025828475395733101101755144964, scale precision, 712470801123454174025828475395733102201266772741, scale precision,
    1, 128, 1, 128, ⟨-1050060828228243590246768852327006779256923290190, -1050060828228243590246768852327006779256921193037⟩, ⟨-1050060828228243590246768852327006777001479219042, -1050060828228243590246768852327006777001477121889⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1194581830404721260242223227006357749158941894153, 1194581830404721260242223227006357749158941894154⟩
def centerBExp : DyadicInterval precision := ⟨284999547096464951341122585071967103380008365968, 284999547096464951341122585071967105579031621521⟩
def centerBLog : DyadicInterval precision := ⟨260366571583691778627595810614960445965748090502, 260366571583691778627595810614960448164771346055⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨284999547096464951341122585071967103929764179856, scale precision, 284999547096464951341122585071967105029275807633, scale precision,
    2, 128, 2, 128, ⟨-2389163660809442520484446454012715501137078868296, -2389163660809442520484446454012715501137076771143⟩, ⟨-2389163660809442520484446454012715495498690805467, -2389163660809442520484446454012715495498688708314⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨515638597770044866598548001891700747220249700387, 534462464943461988627643447017480232956872335844⟩
def wholeCExp : DyadicInterval precision := ⟨703333790844970445594430493989792987188966438685, 721686773794484313367713103686592934112203819597⟩
def wholeCLog : DyadicInterval precision := ⟨574194643415014070803989257396184403389201966771, 586532696251475426780028142470714115783725098168⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨703333790844970445594430493989792987738722252573, scale precision, 721686773794484313367713103686592933562448005709, scale precision,
    1, 128, 1, 128, ⟨-1068924929886923977255286894034960467056117994409, -1068924929886923977255286894034960467056115897256⟩, ⟨-1031277195540089733197096003783401493327179475066, -1031277195540089733197096003783401493327177377913⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1169161064866908489201243437207684303447781003992, 1220276011489811637820224973169820958582993525708⟩
def wholeBExp : DyadicInterval precision := ⟨275152708422481421135963576643696939738866590592, 295088342717945834601186042078933561855586445825⟩
def wholeBLog : DyadicInterval precision := ⟨252103254567004538347859354165711364741799522227, 268784755063900212695142217247054483647915854260⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨275152708422481421135963576643696940288622404480, scale precision, 295088342717945834601186042078933561305830631937, scale precision,
    2, 128, 2, 128, ⟨-2440552022979623275640449946339641920086072102569, -2440552022979623275640449946339641920086070005416⟩, ⟨-2338322129733816978402486874415368604172754643561, -2338322129733816978402486874415368604172752546408⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0106StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0107StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0107StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨507004303901063781088449868274237350112289341617, 507004303901063781088449868274237350112289341618⟩
def centerCExp : DyadicInterval precision := ⟨730264546279096963661310522406402996798969895774, 730264546279096963661310522406402998997993151327⟩
def centerCLog : DyadicInterval precision := ⟨592263701830398084180580190186818772360966099623, 592263701830398084180580190186818774559989355176⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨730264546279096963661310522406402997348725709662, scale precision, 730264546279096963661310522406402998448237337439, scale precision,
    1, 128, 1, 128, ⟨-1014008607802127562176899736548474701324823508158, -1014008607802127562176899736548474701324821411005⟩, ⟨-1014008607802127562176899736548474699124335955465, -1014008607802127562176899736548474699124333858312⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1144995169612467681252171646195897760517516913855, 1144995169612467681252171646195897760517516913856⟩
def centerBExp : DyadicInterval precision := ⟨305010051372870290722565156714843882709466577023, 305010051372870290722565156714843884908489832576⟩
def centerBLog : DyadicInterval precision := ⟨277016496944838318996924825512301147140596630815, 277016496944838318996924825512301149339619886368⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨305010051372870290722565156714843883259222390911, scale precision, 305010051372870290722565156714843884358734018688, scale precision,
    2, 128, 2, 128, ⟨-2289990339224935362504343292391795523669272726855, -2289990339224935362504343292391795523669270629702⟩, ⟨-2289990339224935362504343292391795518400797025718, -2289990339224935362504343292391795518400794928565⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨497687795998397117649244397984432485175960451123, 516359633483965550769306828629969539074360786555⟩
def wholeCExp : DyadicInterval precision := ⟨720975032818824115508540015583366917188737582963, 739634457227329619408055627098249372995739319291⟩
def wholeCLog : DyadicInterval precision := ⟨586056154606097964526562885964265142333704434633, 598498377720168544671336610201384666902698356016⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨720975032818824115508540015583366917738493396851, scale precision, 739634457227329619408055627098249372445983505403, scale precision,
    1, 128, 0, 128, ⟨-1032719266967931101538613657259939079263142657826, -1032719266967931101538613657259939079263140560673⟩, ⟨-995375591996794235298488795968864969265616392342, -995375591996794235298488795968864969265614295189⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1120111434970572534491071289146400107461811295751, 1170152799610028500750178694985132719235415026852⟩
def wholeBExp : DyadicInterval precision := ⟨294688136710228054637150045266429996848090199314, 315575203250281295540434403773685687322616394429⟩
def wholeBLog : DyadicInterval precision := ⟨268451741451305337972973757642834438287827155719, 285731409747513246383899902660110217191448861587⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨294688136710228054637150045266429997397846013202, scale precision, 315575203250281295540434403773685686772860580541, scale precision,
    2, 128, 2, 128, ⟨-2340305599220057001500357389970265441197337269444, -2340305599220057001500357389970265441197335172291⟩, ⟨-2240222869941145068982142578292800212377577519043, -2240222869941145068982142578292800212377575421890⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0107StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0108StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0108StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨489834376697085099430521604677665982489919474073, 489834376697085099430521604677665982489919474074⟩
def centerCExp : DyadicInterval precision := ⟨747626216500184418176514719557368289624034682847, 747626216500184418176514719557368291823057938400⟩
def centerCLog : DyadicInterval precision := ⟨603795104711303171387084722442290079893479180515, 603795104711303171387084722442290082092502436068⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨747626216500184418176514719557368290173790496735, scale precision, 747626216500184418176514719557368291273302124512, scale precision,
    0, 128, 0, 128, ⟨-979668753394170198861043209355331966054533479104, -979668753394170198861043209355331966054531381951⟩, ⟨-979668753394170198861043209355331963905146514342, -979668753394170198861043209355331963905144417189⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1097421525250179997417631550735392695150242228857, 1097421525250179997417631550735392695150242228858⟩
def centerBExp : DyadicInterval precision := ⟨325527566629843929237035077137899757212697161000, 325527566629843929237035077137899759411720416553⟩
def centerBLog : DyadicInterval precision := ⟨293893587302548984277502716606660103294574830307, 293893587302548984277502716606660105493598085860⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨325527566629843929237035077137899757762452974888, scale precision, 325527566629843929237035077137899758861964602665, scale precision,
    2, 128, 2, 128, ⟨-2194843050500359994835263101470785392768691288211, -2194843050500359994835263101470785392768689191058⟩, ⟨-2194843050500359994835263101470785387832279724370, -2194843050500359994835263101470785387832277627217⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨480587617583154446417785413694201341604360523168, 499118607398289371570928132321858375692748600604⟩
def wholeCExp : DyadicInterval precision := ⟨738187668517019050850553078864002934613595944449, 757146620674580303634324056305096656174866483946⟩
def wholeCLog : DyadicInterval precision := ⟨597537428828638861458087364241545117081426549103, 610080023993545524805315611001473674845953090121⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨738187668517019050850553078864002935163351758337, scale precision, 757146620674580303634324056305096655625110670058, scale precision,
    0, 128, 0, 128, ⟨-998237214796578743141856264643716752473932880160, -998237214796578743141856264643716752473930783007⟩, ⟨-961175235166308892835570827388402682147541868798, -961175235166308892835570827388402682147539771645⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1073062543092661343514112144831798520728251141347, 1122053208859200700154292179899125256064598893420⟩
def wholeBExp : DyadicInterval precision := ⟨314737760101076424029552099602696279959286522945, 336561646712749141840991121443245691165944998603⟩
def wholeBLog : DyadicInterval precision := ⟨285042518315165146381454777827418236357246728546, 302889939325008755919040991410275143322424591058⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨314737760101076424029552099602696280509042336833, scale precision, 336561646712749141840991121443245690616189184715, scale precision,
    2, 128, 2, 128, ⟨-2244106417718401400308584359798250514682019386316, -2244106417718401400308584359798250514682017289163⟩, ⟨-2146125086185322687028224289663597039069216990186, -2146125086185322687028224289663597039069214893033⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0108StableWitnesses

end


