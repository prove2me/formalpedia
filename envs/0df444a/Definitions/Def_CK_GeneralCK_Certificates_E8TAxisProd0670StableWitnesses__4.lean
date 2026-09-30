-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0670StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0670StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:13:08.837653+00:00
-- url     : https://prove2.me/theorems/7067388f-de5e-4ce7-9bb3-2263221549ff
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0670StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0671StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0670StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0671StableWitnesses, GeneralCK.Certificates.E8TAxisProd0672StableWitnesses, GeneralCK.Certificates.E8TAxisProd0673StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0670StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0671StableWitnesses, GeneralCK.Certificates.E8TAxisProd0672StableWitnesses, GeneralCK.Certificates.E8TAxisProd0673StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0670StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0671StableWitnesses, GeneralCK.Certificates.E8TAxisProd0672StableWitnesses, GeneralCK.Certificates.E8TAxisProd0673StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0670StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0671StableWitnesses, GeneralCK/Certificates/E8TAxisProd0672StableWitnesses, GeneralCK/Certificates/E8TAxisProd0673StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0670StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0670StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052157038226, 791434261379870553054051158387221052157038227⟩
def centerAExp : DyadicInterval precision := ⟨1459919625655795613670423245226319210257330755284, 1459919625655795613670423245226319212456354010837⟩
def centerALog : DyadicInterval precision := ⟨1012244519327522357560934184367326742088532965455, 1012244519327522357560934184367326744287556221008⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459919625655795613670423245226319210807086569172, scale precision, 1459919625655795613670423245226319211906598196949, scale precision,
    0, 128, 0, 128, ⟨-1582868522759741106108102316774442654666670423, -1582868522759741106108102316774442654664573270⟩, ⟨-1582868522759741106108102316774441553963579636, -1582868522759741106108102316774441553961482483⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨589001631572899351572124980299114401874513713575, 589001631572899351572124980299114401874513713576⟩
def centerDExp : DyadicInterval precision := ⟨652751929826838909185228475799900996561578066054, 652751929826838909185228475799900998760601321607⟩
def centerDLog : DyadicInterval precision := ⟨539641066124454758744190885645098755336345326342, 539641066124454758744190885645098757535368581895⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨652751929826838909185228475799900997111333879942, scale precision, 652751929826838909185228475799900998210845507719, scale precision,
    1, 128, 1, 128, ⟨-1178003263145798703144249960598228804979923376863, -1178003263145798703144249960598228804979921279710⟩, ⟨-1178003263145798703144249960598228802518133574591, -1178003263145798703144249960598228802518131477438⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨589934324024306817548051351085823430563957571879, 589934324024306817548051351085823430563957571880⟩
def centerCExp : DyadicInterval precision := ⟨651919322573856354332621085943656494530945503652, 651919322573856354332621085943656496729968759205⟩
def centerCLog : DyadicInterval precision := ⟨539065403607659496582268779207739308011366429279, 539065403607659496582268779207739310210389684832⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨651919322573856354332621085943656495080701317540, scale precision, 651919322573856354332621085943656496180212945317, scale precision,
    1, 128, 1, 128, ⟨-1179868648048613635096102702171646862360383146924, -1179868648048613635096102702171646862360381049771⟩, ⟨-1179868648048613635096102702171646859895449237747, -1179868648048613635096102702171646859895447140594⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1381577940722227156121621543884729404849336661420, 1381577940722227156121621543884729404849336661421⟩
def centerBExp : DyadicInterval precision := ⟨220653087769258421034275361173206293285767707467, 220653087769258421034275361173206295484790963020⟩
def centerBLog : DyadicInterval precision := ⟨205503382408681938176482619202896826092495011820, 205503382408681938176482619202896828291518267373⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨220653087769258421034275361173206293835523521355, scale precision, 220653087769258421034275361173206294935035149132, scale precision,
    2, 128, 2, 128, ⟨-2763155881444454312243243087769458813339996730660, -2763155881444454312243243087769458813339994633507⟩, ⟨-2763155881444454312243243087769458806057352012174, -2763155881444454312243243087769458806057349915021⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 949721161203312387564849132921065893757597831⟩
def wholeAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨583646737036782134467503622221012937253099239179, 594370338528145575810628189240163754488538282194⟩
def wholeDExp : DyadicInterval precision := ⟨647973841382699837641744325099416506198004171002, 657552822402718366845230970835233707672091898233⟩
def wholeDLog : DyadicInterval precision := ⟨536334420746670162773197764634792505120063760737, 542955975091047008060968952594356693577949672231⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨647973841382699837641744325099416506747759984890, scale precision, 657552822402718366845230970835233707122336084345, scale precision,
    1, 128, 1, 128, ⟨-1188740677056291151621256378480327510217048998869, -1188740677056291151621256378480327510217046901716⟩, ⟨-1167293474073564268935007244442025873284291575580, -1167293474073564268935007244442025873284289478427⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨584390943313010917063853457687796339564376962960, 595492518037508676307971004760304209776734300945⟩
def wholeCExp : DyadicInterval precision := ⟨646979542211247811187581126492466525394723535579, 656883502811556797789804848532940459198259071502⟩
def wholeCLog : DyadicInterval precision := ⟨535645380999831357468656828595370673105130120750, 542494275678720680653370244367560869658098471921⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨646979542211247811187581126492466525944479349467, scale precision, 656883502811556797789804848532940458648503257614, scale precision,
    1, 128, 1, 128, ⟨-1190985036075017352615942009520608420795346664666, -1190985036075017352615942009520608420795344567513⟩, ⟨-1168781886626021834127706915375592677905601982087, -1168781886626021834127706915375592677905599884934⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1365881432539980601586145671997514523529515315844, 1397359021411209685781702041949358426767112365912⟩
def wholeBExp : DyadicInterval precision := ⟨215939013395001516640234041908514697661518484147, 225443980152307449673780545039568995951403959654⟩
def wholeBLog : DyadicInterval precision := ⟨201401917102669927707754411393625410198977690633, 209659923366008372683222747301197949647052204000⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨215939013395001516640234041908514698211274298035, scale precision, 225443980152307449673780545039568995401648145766, scale precision,
    2, 128, 2, 128, ⟨-2794718042822419371563404083898716857255040326589, -2794718042822419371563404083898716857255038229436⟩, ⟨-2731762865079961203172291343995029043495090777574, -2731762865079961203172291343995029043495088680421⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0670StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0671StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0671StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052157038226, 791434261379870553054051158387221052157038227⟩
def centerAExp : DyadicInterval precision := ⟨1459919625655795613670423245226319210257330755284, 1459919625655795613670423245226319212456354010837⟩
def centerALog : DyadicInterval precision := ⟨1012244519327522357560934184367326742088532965455, 1012244519327522357560934184367326744287556221008⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459919625655795613670423245226319210807086569172, scale precision, 1459919625655795613670423245226319211906598196949, scale precision,
    0, 128, 0, 128, ⟨-1582868522759741106108102316774442654666670423, -1582868522759741106108102316774442654664573270⟩, ⟨-1582868522759741106108102316774441553963579636, -1582868522759741106108102316774441553961482483⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨578305529745348302256248804406759576517080537351, 578305529745348302256248804406759576517080537352⟩
def centerDExp : DyadicInterval precision := ⟨662376618137962680502649166797816345145246286664, 662376618137962680502649166797816347344269542217⟩
def centerDLog : DyadicInterval precision := ⟨546279142756386118646189338978646827486920449598, 546279142756386118646189338978646829685943705151⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨662376618137962680502649166797816345695002100552, scale precision, 662376618137962680502649166797816346794513728329, scale precision,
    1, 128, 1, 128, ⟨-1156611059490696604512497608813519154247171459854, -1156611059490696604512497608813519154247169362701⟩, ⟨-1156611059490696604512497608813519151821152786705, -1156611059490696604512497608813519151821150689552⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨579233457630059924726732386078815853907177197517, 579233457630059924726732386078815853907177197518⟩
def centerCExp : DyadicInterval precision := ⟨661536047533766872031045855148474328777358794557, 661536047533766872031045855148474330976382050110⟩
def centerCLog : DyadicInterval precision := ⟨545700607486262675674358693878309904129731992337, 545700607486262675674358693878309906328755247890⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨661536047533766872031045855148474329327114608445, scale precision, 661536047533766872031045855148474330426626236222, scale precision,
    1, 128, 1, 128, ⟨-1158466915260119849453464772157631709028906071843, -1158466915260119849453464772157631709028903974690⟩, ⟨-1158466915260119849453464772157631706599804815379, -1158466915260119849453464772157631706599802718226⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1350802508543710626346479234733362121204170743181, 1350802508543710626346479234733362121204170743182⟩
def centerBExp : DyadicInterval precision := ⟨230144308397459194662737786364922938074479008212, 230144308397459194662737786364922940273502263765⟩
def centerBLog : DyadicInterval precision := ⟨213726435538121997963652608771548777296392485761, 213726435538121997963652608771548779495415741314⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨230144308397459194662737786364922938624234822100, scale precision, 230144308397459194662737786364922939723746449877, scale precision,
    2, 128, 2, 128, ⟨-2701605017087421252692958469466724245899495662843, -2701605017087421252692958469466724245899493565690⟩, ⟨-2701605017087421252692958469466724238917189407042, -2701605017087421252692958469466724238917187309889⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 949721161203312387564849132921065893757597831⟩
def wholeAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨572977884517961874928161575521614457065497220141, 583646737036782134467503622221012937253099239180⟩
def wholeDExp : DyadicInterval precision := ⟨657552822402718366845230970835233705473068642680, 667223417983630662234844101180676645055775852155⟩
def wholeDLog : DyadicInterval precision := ⟨542955975091047008060968952594356691378926416678, 549610565162722028431892812520915520687805740148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨657552822402718366845230970835233706022824456568, scale precision, 667223417983630662234844101180676644506020038267, scale precision,
    1, 128, 1, 128, ⟨-1167293474073564268935007244442025875728107478292, -1167293474073564268935007244442025875728105381139⟩, ⟨-1145955769035923749856323151043228912926797613794, -1145955769035923749856323151043228912926795516641⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨573718314579148943489517727126920588578980759463, 584763145911908392038919199224416620241062004578⟩
def wholeCExp : DyadicInterval precision := ⟨656549009184327413967846368386844889837072014413, 666547699174858633758149570772159723684385324502⟩
def wholeCLog : DyadicInterval precision := ⟨542263485925490851692795803789698902277373767781, 549146568688965630197729286642646526733797610475⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨656549009184327413967846368386844890386827828301, scale precision, 666547699174858633758149570772159723134629510614, scale precision,
    1, 128, 1, 128, ⟨-1169526291823816784077838398448833241705901212885, -1169526291823816784077838398448833241705899115732⟩, ⟨-1147436629158297886979035454253841175952543925861, -1147436629158297886979035454253841175952541828708⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1335274280141250576209924124725630424338682417773, 1366416661232769814667055738288509335369282604567⟩
def wholeBExp : DyadicInterval precision := ⟨225278917171741248745467274522371810261091493963, 235087134385689132804028875743960484926229469224⟩
def wholeBLog : DyadicInterval precision := ⟨209516912461000209608729395421954246312642400451, 217990575423247351721593852572270283702073046056⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨225278917171741248745467274522371810810847307851, scale precision, 235087134385689132804028875743960484376473655336, scale precision,
    2, 128, 2, 128, ⟨-2732833322465539629334111476577018674305118477590, -2732833322465539629334111476577018674305116380437⟩, ⟨-2670548560282501152419848249451260845259616017759, -2670548560282501152419848249451260845259613920606⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0671StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0672StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0672StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨610560585232978838677636124558316081121189005779, 610560585232978838677636124558316081121189005780⟩
def centerDExp : DyadicInterval precision := ⟨633775439067498409587600235923873634184078301602, 633775439067498409587600235923873636383101557155⟩
def centerDLog : DyadicInterval precision := ⟨526464129056309766045029930608943037858964020595, 526464129056309766045029930608943040057987276148⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨633775439067498409587600235923873634733834115490, scale precision, 633775439067498409587600235923873635833345743267, scale precision,
    1, 128, 1, 128, ⟨-1221121170465957677355272249116632163510129390304, -1221121170465957677355272249116632163510127293151⟩, ⟨-1221121170465957677355272249116632160974628729968, -1221121170465957677355272249116632160974626632815⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨611126022883744318618305590284199991800235916809, 611126022883744318618305590284199991800235916810⟩
def centerCExp : DyadicInterval precision := ⟨633285228346474539006972716545089190578842133404, 633285228346474539006972716545089192777865388957⟩
def centerCLog : DyadicInterval precision := ⟨526122156339622585591598586604470088946466265973, 526122156339622585591598586604470091145489521526⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨633285228346474539006972716545089191128597947292, scale precision, 633285228346474539006972716545089192228109575069, scale precision,
    1, 128, 1, 128, ⟨-1222252045767488637236611180568399984869204547116, -1222252045767488637236611180568399984869202449963⟩, ⟨-1222252045767488637236611180568399982331741217273, -1222252045767488637236611180568399982331739120120⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1443554064218929070059968903394572604042944910631, 1443554064218929070059968903394572604042944910632⟩
def centerBExp : DyadicInterval precision := ⟨202710765095936591263909638977209875430516742068, 202710765095936591263909638977209877629539997621⟩
def centerBLog : DyadicInterval precision := ⟨189830872935121176987681699060043777181758901302, 189830872935121176987681699060043779380782156855⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨202710765095936591263909638977209875980272555956, scale precision, 202710765095936591263909638977209877079784183733, scale precision,
    2, 128, 2, 128, ⟨-2887108128437858140119937806789145212049513728002, -2887108128437858140119937806789145212049511630849⟩, ⟨-2887108128437858140119937806789145204122268011673, -2887108128437858140119937806789145204122265914520⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124295302837, 615985792935344704096715461380744242879788980550⟩
def wholeDExp : DyadicInterval precision := ⟨629087614762237432177832619094338710911004411584, 638485690296710810307667032247350013857008098659⟩
def wholeDLog : DyadicInterval precision := ⟨523190605620864448684409715253755539004186757001, 529745944986552956313550471423206443941852059644⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338711460760225472, scale precision, 638485690296710810307667032247350013307252284771, scale precision,
    1, 128, 1, 128, ⟨-1231971585870689408193430922761488487036776340025, -1231971585870689408193430922761488487036774242872⟩, ⟨-1210299380539672039779788485684622624990193800798, -1210299380539672039779788485684622624990191703645⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨605525639754255905015627397518030978757082458823, 616741745697140777487395869458383159746233566792⟩
def wholeCExp : DyadicInterval precision := ⟨628437167836026135801691191395540316850229339986, 638157292949424889611811082552144836021373651054⟩
def wholeCLog : DyadicInterval precision := ⟨522735816540487508417634540299405893993750465680, 529517376563282544334914908910001491693706978494⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨628437167836026135801691191395540317399985153874, scale precision, 638157292949424889611811082552144835471617837166, scale precision,
    1, 128, 1, 128, ⟨-1233483491394281554974791738916766320770987441129, -1233483491394281554974791738916766320770985343976⟩, ⟨-1211051279508511810031254795036061956255120538071, -1211051279508511810031254795036061956255118440918⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1427532357011884353116380646773615700350616453586, 1459657159822916175325280960888566675307257886470⟩
def wholeBExp : DyadicInterval precision := ⟨198292614410830060753300977589285114499982532968, 207204277487123306070497951639103123545847980712⟩
def wholeBLog : DyadicInterval precision := ⟨185945719302999434024368369614182904442174514507, 193771731408745391637673883239025319071007578645⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨198292614410830060753300977589285115049738346856, scale precision, 207204277487123306070497951639103122996092166824, scale precision,
    2, 128, 2, 128, ⟨-2919314319645832350650561921777133354666453019529, -2919314319645832350650561921777133354666450922376⟩, ⟨-2855064714023768706232761293547231396823567761430, -2855064714023768706232761293547231396823565664277⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0672StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0673StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0673StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    1, 128, 1, 128, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨600315458424560704129193335907329532639801675264, 600315458424560704129193335907329532639801675265⟩
def centerCExp : DyadicInterval precision := ⟨642723550704769403482572604380827673891531290514, 642723550704769403482572604380827676090554546067⟩
def centerCLog : DyadicInterval precision := ⟨532692343152587214431177301323283960548237365128, 532692343152587214431177301323283962747260620681⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨642723550704769403482572604380827674441287104402, scale precision, 642723550704769403482572604380827675540798732179, scale precision,
    1, 128, 1, 128, ⟨-1200630916849121408258386671814659066529704883595, -1200630916849121408258386671814659066529702786442⟩, ⟨-1200630916849121408258386671814659064029503914612, -1200630916849121408258386671814659064029501817459⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1412136486967960825197692353002697754717467866569, 1412136486967960825197692353002697754717467866570⟩
def centerBExp : DyadicInterval precision := ⟨211616086010865970091675146575337737965413600906, 211616086010865970091675146575337740164436856459⟩
def centerBLog : DyadicInterval precision := ⟨197630623932790199893307032864802839309683126924, 197630623932790199893307032864802841508706382477⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨211616086010865970091675146575337738515169414794, scale precision, 211616086010865970091675146575337739614681042571, scale precision,
    2, 128, 2, 128, ⟨-2824272973935921650395384706005395513231760724909, -2824272973935921650395384706005395513231758627756⟩, ⟨-2824272973935921650395384706005395505638112838529, -2824272973935921650395384706005395505638110741376⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    1, 128, 1, 128, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨594744330860052389027389161313773445021387305465, 605901657939842918058081508420489878790405438430⟩
def wholeCExp : DyadicInterval precision := ⟨637829004544146637410168805807523803531125493219, 647642298482951318824865167693805807400691469988⟩
def wholeCLog : DyadicInterval precision := ⟨529288848230661694077429559053757717259290166725, 536104700810258324974082061428404159760662622196⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨637829004544146637410168805807523804080881307107, scale precision, 647642298482951318824865167693805806850935656100, scale precision,
    1, 128, 1, 128, ⟨-1211803315879685836116163016840979758840505379960, -1211803315879685836116163016840979758840503282807⟩, ⟨-1189488661720104778054778322627546888802169503900, -1189488661720104778054778322627546888802167406747⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1396277294727754898993757472472361982396946679570, 1428078754383307564160729268749082555702441368841⟩
def wholeBExp : DyadicInterval precision := ⟨207049404508114995265403921379615213770296027726, 216258903514821547674149009457818935715803419294⟩
def wholeBLog : DyadicInterval precision := ⟨193636082811408623125844070530892918300229233549, 201680600799179076763764949226107753173601309162⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨207049404508114995265403921379615214320051841614, scale precision, 216258903514821547674149009457818935166047605406, scale precision,
    2, 128, 2, 128, ⟨-2856157508766615128321458537498165115285450475349, -2856157508766615128321458537498165115285448378196⟩, ⟨-2792554589455509797987514944944723961078583689536, -2792554589455509797987514944944723961078581592383⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0673StableWitnesses

end


