-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0094StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0094StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:38:40.035988+00:00
-- url     : https://prove2.me/theorems/dbe4c0b8-5f0d-4d9d-b27f-f06af717075b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0094StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0095StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0094StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0095StableWitnesses, GeneralCK.Certificates.E8TAxisProd0096StableWitnesses, GeneralCK.Certificates.E8TAxisProd0097StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0094StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0095StableWitnesses, GeneralCK.Certificates.E8TAxisProd0096StableWitnesses, GeneralCK.Certificates.E8TAxisProd0097StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0094StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0095StableWitnesses, GeneralCK.Certificates.E8TAxisProd0096StableWitnesses, GeneralCK.Certificates.E8TAxisProd0097StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0094StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0095StableWitnesses, GeneralCK/Certificates/E8TAxisProd0096StableWitnesses, GeneralCK/Certificates/E8TAxisProd0097StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0094StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0094StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨138984770367679047606875056826648434719489737964, 138984770367679047606875056826648434719489737965⟩
def centerDExp : DyadicInterval precision := ⟨1208367104819141335120726173598708722736266317802, 1208367104819141335120726173598708724935289573355⟩
def centerDLog : DyadicInterval precision := ⟨880649566147303539816976282535028842882764309855, 880649566147303539816976282535028845081787565408⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1208367104819141335120726173598708723286022131690, scale precision, 1208367104819141335120726173598708724385533759467, scale precision,
    0, 128, 0, 128, ⟨-277969540735358095213750113653296870103901821126, -277969540735358095213750113653296870103899723973⟩, ⟨-277969540735358095213750113653296868774059227885, -277969540735358095213750113653296868774057130732⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨139944528349104098617862340693891168676258187818, 139944528349104098617862340693891168676258187819⟩
def centerCExp : DyadicInterval precision := ⟨1206781093987734162656730572806583813753962946115, 1206781093987734162656730572806583815952986201668⟩
def centerCLog : DyadicInterval precision := ⟨879781116645017419867668445062220957058208427715, 879781116645017419867668445062220959257231683268⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1206781093987734162656730572806583814303718760003, scale precision, 1206781093987734162656730572806583815403230387780, scale precision,
    0, 128, 0, 128, ⟨-279889056698208197235724681387782338018312592975, -279889056698208197235724681387782338018310495822⟩, ⟨-279889056698208197235724681387782336686722255451, -279889056698208197235724681387782336686720158298⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨281889891187500602225492145883405813174137005050, 281889891187500602225492145883405813174137005051⟩
def centerBExp : DyadicInterval precision := ⟨993730381583379599097308682273953379443783315800, 993730381583379599097308682273953381642806571353⟩
def centerBLog : DyadicInterval precision := ⟨758163970490706976153581311423354385165468494720, 758163970490706976153581311423354387364491750273⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨993730381583379599097308682273953379993539129688, scale precision, 993730381583379599097308682273953381093050757465, scale precision,
    0, 128, 0, 128, ⟨-563779782375001204450984291766811627156813307100, -563779782375001204450984291766811627156811209947⟩, ⟨-563779782375001204450984291766811625539736810254, -563779782375001204450984291766811625539734713101⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨134987245269836870215393179468011326867547174258, 142984678294030808430193174439689638732873799525⟩
def wholeDExp : DyadicInterval precision := ⟨1201770939647839765988959733979548164468536451217, 1214995512532168524628632240632930004533537374880⟩
def wholeDLog : DyadicInterval precision := ⟨877034319321159546816789449956018115998925220947, 884273498322789745939213484257675327336644869096⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1201770939647839765988959733979548165018292265105, scale precision, 1214995512532168524628632240632930003983781560992, scale precision,
    0, 128, 0, 128, ⟨-285969356588061616860386348879379278134319500540, -285969356588061616860386348879379278134317403387⟩, ⟨-269974490539673740430786358936022653073801578439, -269974490539673740430786358936022653073799481286⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨135626692008785377142630029624202994261554904099, 144265163383122164482546534975845208150899296287⟩
def wholeCExp : DyadicInterval precision := ⟨1199666936116860123325924274283438621574934428979, 1213932790367752907470564320597495061739282852591⟩
def wholeCLog : DyadicInterval precision := ⟨875879266733045019226793172335071307114073904507, 883693083502000011870295132974730815797916609356⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1199666936116860123325924274283438622124690242867, scale precision, 1213932790367752907470564320597495061189527038703, scale precision,
    0, 128, 0, 128, ⟨-288530326766244328965093069951690416971543049041, -288530326766244328965093069951690416971540951888⟩, ⟨-271253384017570754285260059248405987861238116781, -271253384017570754285260059248405987861236019628⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨273317421200188951886965822796529956432845743030, 290483523917795193092868089669284608761847021739⟩
def wholeBExp : DyadicInterval precision := ⟨982112554815529200933538642394290479384834490112, 1005456521844459780778513696130758001103534370433⟩
def wholeBLog : DyadicInterval precision := ⟨751231928150900893187639013654524025954953593514, 765127458284635026651998529297265612673788156792⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨982112554815529200933538642394290479934590304000, scale precision, 1005456521844459780778513696130758000553778556545, scale precision,
    0, 128, 0, 128, ⟨-580967047835590386185736179338569218341797883012, -580967047835590386185736179338569218341795785859⟩, ⟨-546634842400377903773931645593059912066583866411, -546634842400377903773931645593059912066581769258⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0094StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0095StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0095StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨130992033893699994791369923976531926829092122734, 130992033893699994791369923976531926829092122735⟩
def centerDExp : DyadicInterval precision := ⟨1221656411836274069288773586476386668146918568609, 1221656411836274069288773586476386670345941824162⟩
def centerDLog : DyadicInterval precision := ⟨887906164936387943905585824070712899195502313636, 887906164936387943905585824070712901394525569189⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1221656411836274069288773586476386668696674382497, scale precision, 1221656411836274069288773586476386669796186010274, scale precision,
    0, 128, 0, 128, ⟨-261984067787399989582739847953063854315873506824, -261984067787399989582739847953063854315871409671⟩, ⟨-261984067787399989582739847953063853000497081267, -261984067787399989582739847953063853000494984114⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨131950677306774987160038351684938346001427256983, 131950677306774987160038351684938346001427256984⟩
def centerCExp : DyadicInterval precision := ⟨1220054819342009398577397661813366527361392607693, 1220054819342009398577397661813366529560415863246⟩
def centerCLog : DyadicInterval precision := ⟨887033525723360837415558011423000943042163653750, 887033525723360837415558011423000945241186909303⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1220054819342009398577397661813366527911148421581, scale precision, 1220054819342009398577397661813366529010660049358, scale precision,
    0, 128, 0, 128, ⟨-263901354613549974320076703369876692661407136942, -263901354613549974320076703369876692661405039789⟩, ⟨-263901354613549974320076703369876691344303988145, -263901354613549974320076703369876691344301890992⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨265422583803151174472145889972799573614074303170, 265422583803151174472145889972799573614074303171⟩
def centerBExp : DyadicInterval precision := ⟨1016378097227541860396043359255007668086400657818, 1016378097227541860396043359255007670285423913371⟩
def centerBLog : DyadicInterval precision := ⟨771583454053650768603597651634296496291784930023, 771583454053650768603597651634296498490808185576⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1016378097227541860396043359255007668636156471706, scale precision, 1016378097227541860396043359255007669735668099483, scale precision,
    0, 128, 0, 128, ⟨-530845167606302348944291779945599148018671434481, -530845167606302348944291779945599148018669337328⟩, ⟨-530845167606302348944291779945599146437627875353, -530845167606302348944291779945599146437625778200⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 134987245269836870215393179468011326867547174259⟩
def wholeDExp : DyadicInterval precision := ⟨1214995512532168524628632240632930002334514119327, 1228350054579566692017908102915209767793957734212⟩
def wholeDLog : DyadicInterval precision := ⟨884273498322789745939213484257675325137621613543, 891547615580027951955449639520829064234092557127⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1214995512532168524628632240632930002884269933215, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-269974490539673740430786358936022654396389215748, -269974490539673740430786358936022654396387118595⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨127637793886269361116932363704697199557851472762, 136266198261734498948575488111049025967412961209⟩
def wholeCExp : DyadicInterval precision := ⟨1212870898957361524245949366676067228040756624494, 1227276860918746536859142683167439710054296689978⟩
def wholeCLog : DyadicInterval precision := ⟨883112892079848277879085868200353354791862865325, 890964391131488665497475745900424409253870580662⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1212870898957361524245949366676067228590512438382, scale precision, 1227276860918746536859142683167439709504540876090, scale precision,
    0, 128, 0, 128, ⟨-272532396523468997897150976222098052597279193090, -272532396523468997897150976222098052597277095937⟩, ⟨-255275587772538722233864727409394398461027736678, -255275587772538722233864727409394398461025639525⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨256888956081337702934193299911104684499841158149, 273976105689032250524369501682889416191129069479⟩
def wholeBExp : DyadicInterval precision := ⟨1004550631347444800692433751777440834696748855736, 1028316822792456288805504901327625679521528299792⟩
def wholeBLog : DyadicInterval precision := ⟨764590682423778549323092247085816655120177178032, 778608236908616865199884766058755225780285862419⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1004550631347444800692433751777440835246504669624, scale precision, 1028316822792456288805504901327625678971772485904, scale precision,
    0, 128, 0, 128, ⟨-547952211378064501048739003365778833182088481407, -547952211378064501048739003365778833182086384254⟩, ⟨-513777912162675405868386599822209368218339517999, -513777912162675405868386599822209368218337420846⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0095StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0096StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0096StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨527203443311289659574641921624530008639338292893, 527203443311289659574641921624530008639338292894⟩
def centerCExp : DyadicInterval precision := ⟨710355278119359509193211608550770504050821359421, 710355278119359509193211608550770506249844614974⟩
def centerCLog : DyadicInterval precision := ⟨578927247575940930634384817906084539111828019611, 578927247575940930634384817906084541310851275164⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨710355278119359509193211608550770504600577173309, scale precision, 710355278119359509193211608550770505700088801086, scale precision,
    1, 128, 1, 128, ⟨-1054406886622579319149283843249060018409758161079, -1054406886622579319149283843249060018409756063926⟩, ⟨-1054406886622579319149283843249060016147597107648, -1054406886622579319149283843249060016147595010495⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1197590497787172821108656203161498811126636800129, 1197590497787172821108656203161498811126636800130⟩
def centerBExp : DyadicInterval precision := ⟨283828551399395356835445556020319979978466323528, 283828551399395356835445556020319982177489579081⟩
def centerBLog : DyadicInterval precision := ⟨259386333989238270639731645607384246573740196530, 259386333989238270639731645607384248772763452083⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨283828551399395356835445556020319980528222137416, scale precision, 283828551399395356835445556020319981627733765193, scale precision,
    2, 128, 2, 128, ⟨-2395180995574345642217312406322997625084099871206, -2395180995574345642217312406322997625084097774053⟩, ⟨-2395180995574345642217312406322997619422449426465, -2395180995574345642217312406322997619422447329312⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨517802407414192458596602619857206278120042976220, 536644883613847459699420042076475693246390244490⟩
def wholeCExp : DyadicInterval precision := ⟨701236387855383963878193299001347845372983630384, 719552964234240380085322697203156708409087953847⟩
def wholeCLog : DyadicInterval precision := ⟨572777979699668047747697419547858731524408609304, 585103551996455244053877469859303469429236953925⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨701236387855383963878193299001347845922739444272, scale precision, 719552964234240380085322697203156707859332139959, scale precision,
    1, 128, 1, 128, ⟨-1073289767227694919398840084152951387638570655242, -1073289767227694919398840084152951387638568558089⟩, ⟨-1035604814828384917193205239714412555123464511686, -1035604814828384917193205239714412555123462414533⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1172137532782407255992094556070555879213430571068, 1223316793567807601648305299541803074736178381544⟩
def wholeBExp : DyadicInterval precision := ⟨274010128721656477169653367254255508475693723126, 293888844044208371914310153888165332554404769407⟩
def wholeBLog : DyadicInterval precision := ⟨251141386897059978015625016631020027577631211622, 267786418448382937857984319900609372720148173258⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨274010128721656477169653367254255509025449537014, scale precision, 293888844044208371914310153888165332004648955519, scale precision,
    2, 128, 2, 128, ⟨-2446633587135615203296610599083606152404618111231, -2446633587135615203296610599083606152404616014078⟩, ⟨-2344275065564814511984189112141111755692940715255, -2344275065564814511984189112141111755692938618102⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0096StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0097StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0097StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨509159753704644154553376033995061142475264372654, 509159753704644154553376033995061142475264372655⟩
def centerCExp : DyadicInterval precision := ⟨728113704463586941407105649716069992823868290382, 728113704463586941407105649716069995022891545935⟩
def centerCLog : DyadicInterval precision := ⟨590828784980864377715021086521975299586757692267, 590828784980864377715021086521975301785780947820⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨728113704463586941407105649716069993373624104270, scale precision, 728113704463586941407105649716069994473135732047, scale precision,
    1, 128, 1, 128, ⟨-1018319507409288309106752067990122286054023681179, -1018319507409288309106752067990122286054021584026⟩, ⟨-1018319507409288309106752067990122283847035906592, -1018319507409288309106752067990122283847033809439⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1147940671164520719597992607836350511878883321717, 1147940671164520719597992607836350511878883321718⟩
def centerBExp : DyadicInterval precision := ⟨303783095012456219830962217863185373303511893992, 303783095012456219830962217863185375502535149545⟩
def centerBLog : DyadicInterval precision := ⟨276001037055286286247255601863604932969080512280, 276001037055286286247255601863604935168103767833⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨303783095012456219830962217863185373853267707880, scale precision, 303783095012456219830962217863185374952779335657, scale precision,
    2, 128, 2, 128, ⟨-2295881342329041439195985215672701026402645024957, -2295881342329041439195985215672701026402642927804⟩, ⟨-2295881342329041439195985215672701021112890359068, -2295881342329041439195985215672701021112888261915⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨499834352001967452246684675724903806560487911744, 518524146299490819305691036671646977232102681050⟩
def wholeCExp : DyadicInterval precision := ⟨718842635948465511342261660578218207766646009804, 737464993756683934745624401112757861761573426836⟩
def wholeCLog : DyadicInterval precision := ⟨584627490993243923376359976809247260698431004723, 597057195607339694932217877067103467010448693552⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨718842635948465511342261660578218208316401823692, scale precision, 737464993756683934745624401112757861211817612948, scale precision,
    1, 128, 0, 128, ⟨-1037048292598981638611382073343293955581932296634, -1037048292598981638611382073343293955581930199481⟩, ⟨-999668704003934904493369351449807612031475636167, -999668704003934904493369351449807612031473539014⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1123024726834227304425043771477334302024773184292, 1173130531179138678107716856054881218488248508364⟩
def wholeBExp : DyadicInterval precision := ⟨293489757307138750738161500449820708639354804341, 314319600840866932582623791703532701673820851759⟩
def wholeBLog : DyadicInterval precision := ⟨267454109347676430925301290798463617162605488616, 284698413577673479259307387067412650381329966213⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨293489757307138750738161500449820709189110618229, scale precision, 314319600840866932582623791703532701124065037871, scale precision,
    2, 128, 2, 128, ⟨-2346261062358277356215433712109762439714137121271, -2346261062358277356215433712109762439714135024118⟩, ⟨-2246049453668454608850087542954668601493330687500, -2246049453668454608850087542954668601493328590347⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0097StableWitnesses

end


