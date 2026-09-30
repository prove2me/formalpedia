-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0227StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0227StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:13:03.128991+00:00
-- url     : https://prove2.me/theorems/78f07672-b216-47a0-ae08-463409b8bbe5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0227StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0228StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0227StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0228StableWitnesses, GeneralCK.Certificates.E8TAxisProd0229StableWitnesses, GeneralCK.Certificates.E8TAxisProd0230StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0227StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0228StableWitnesses, GeneralCK.Certificates.E8TAxisProd0229StableWitnesses, GeneralCK.Certificates.E8TAxisProd0230StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0227StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0228StableWitnesses, GeneralCK.Certificates.E8TAxisProd0229StableWitnesses, GeneralCK.Certificates.E8TAxisProd0230StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0227StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0228StableWitnesses, GeneralCK/Certificates/E8TAxisProd0229StableWitnesses, GeneralCK/Certificates/E8TAxisProd0230StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0227StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0227StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005680170, 827900739799584217789378743685278152778005680171⟩
def centerDExp : DyadicInterval precision := ⟨470725140515848859951996893419642374006683999039, 470725140515848859951996893419642376205707254592⟩
def centerDLog : DyadicInterval precision := ⟨408063947160780491089293755661542510045178856930, 408063947160780491089293755661542512244202112483⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642374556439812927, scale precision, 470725140515848859951996893419642375655951440704, scale precision,
    1, 128, 1, 128, ⟨-1655801479599168435578757487370556307262887510703, -1655801479599168435578757487370556307262885413550⟩, ⟨-1655801479599168435578757487370556303849137307135, -1655801479599168435578757487370556303849135209982⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨834012359820473104910654562238149462945977569212, 834012359820473104910654562238149462945977569213⟩
def centerCExp : DyadicInterval precision := ⟨466804657405890865307531032620340836859940799404, 466804657405890865307531032620340839058964054957⟩
def centerCLog : DyadicInterval precision := ⟨405095551684656079329226429321077441355484290912, 405095551684656079329226429321077443554507546465⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨466804657405890865307531032620340837409696613292, scale precision, 466804657405890865307531032620340838509208241069, scale precision,
    1, 128, 1, 128, ⟨-1668024719640946209821309124476298927613166567794, -1668024719640946209821309124476298927613164470641⟩, ⟨-1668024719640946209821309124476298924170745806205, -1668024719640946209821309124476298924170743709052⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2098460751600358644274459971521448059063004090372, 2098460751600358644274459971521448059063004090373⟩
def centerBExp : DyadicInterval precision := ⟨82728940099226509370883825486507155198845758047, 82728940099226509370883825486507157397869013600⟩
def centerBLog : DyadicInterval precision := ⟨80472256524868701434444590486133212686521838379, 80472256524868701434444590486133214885545093932⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨82728940099226509370883825486507155748601571935, scale precision, 82728940099226509370883825486507156848113199712, scale precision,
    4, 128, 4, 128, ⟨-4196921503200717288548919943042896127838076387031, -4196921503200717288548919943042896127838074289878⟩, ⟨-4196921503200717288548919943042896108413942071602, -4196921503200717288548919943042896108413939974449⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 833959591445470778384083818034390997094871334899⟩
def wholeDExp : DyadicInterval precision := ⟨466838367135635595432846250236128801963479725593, 474632069948069015840646238761706424600391594793⟩
def wholeDLog : DyadicInterval precision := ⟨405121100734994108525530084726425875355168584540, 411016094834480306545789264008568525844426144161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128802513235539481, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1667919182890941556768167636068781995910829813032, -1667919182890941556768167636068781995910827715879⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨827742934726258889335747550897857786398624680867, 840302015960313978486926784705237237311706866130⟩
def wholeCExp : DyadicInterval precision := ⟨462804057668486221151458613372465630206119845195, 470826804222071529292250711349709995516340291800⟩
def wholeCLog : DyadicInterval precision := ⟨402060267994699466374521672621850859409798172698, 408140841739690874982870542572813658918934740027⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨462804057668486221151458613372465630755875659083, scale precision, 470826804222071529292250711349709994966584477912, scale precision,
    1, 128, 1, 128, ⟨-1680604031920627956973853569410474476359503755895, -1680604031920627956973853569410474476359501658742⟩, ⟨-1655485869452517778671495101795715571090743867087, -1655485869452517778671495101795715571090741769934⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2080185123292582211430960669141065011665144036437, 2116771726207796799616898568013188661314063189372⟩
def wholeBExp : DyadicInterval precision := ⟨80681695425644621687662897281547622501417126711, 84824029228841828273337384597001458896350952068⟩
def wholeBLog : DyadicInterval precision := ⟨78533403235363846810446899808563371839742080049, 82453761743085784535297494888303992868225682421⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨80681695425644621687662897281547623051172940599, scale precision, 84824029228841828273337384597001458346595138180, scale precision,
    4, 128, 4, 128, ⟨-4233543452415593599233797136026377332586631867401, -4233543452415593599233797136026377332586629770248⟩, ⟨-4160370246585164422861921338282130013858102649820, -4160370246585164422861921338282130013858100552667⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0227StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0228StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0228StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191530054563, 4906913324212444341793886191975635191530054564⟩
def centerAExp : DyadicInterval precision := ⟨1451720686451934407431403951699999116082005297895, 1451720686451934407431403951699999118281028553448⟩
def centerALog : DyadicInterval precision := ⟨1008137063309063130766142500412726798681612460495, 1008137063309063130766142500412726800880635716048⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1451720686451934407431403951699999116631761111783, scale precision, 1451720686451934407431403951699999117731272739560, scale precision,
    0, 128, 0, 128, ⟨-9813826648424888683587772383951270936520944858, -9813826648424888683587772383951270936518847705⟩, ⟨-9813826648424888683587772383951269829601370550, -9813826648424888683587772383951269829599273397⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨822332702906161561702402133128319807945137679176, 822332702906161561702402133128319807945137679177⟩
def centerCExp : DyadicInterval precision := ⟨474325582484951867834548316332558276930604153498, 474325582484951867834548316332558279129627409051⟩
def centerCLog : DyadicInterval precision := ⟨410784722701064323364480367802742620349413620173, 410784722701064323364480367802742622548436875726⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨474325582484951867834548316332558277480359967386, scale precision, 474325582484951867834548316332558278579871595163, scale precision,
    1, 128, 1, 128, ⟨-1644665405812323123404804266256639617584195208276, -1644665405812323123404804266256639617584193111123⟩, ⟨-1644665405812323123404804266256639614196357605585, -1644665405812323123404804266256639614196355508432⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2063191924998042261928343882770103134146339059635, 2063191924998042261928343882770103134146339059636⟩
def centerBExp : DyadicInterval precision := ⟨86819678118866266539855322019385716455250655457, 86819678118866266539855322019385718654273911010⟩
def centerBLog : DyadicInterval precision := ⟨84338722801047015733306715334664835220173241425, 84338722801047015733306715334664837419196496978⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨86819678118866266539855322019385717005006469345, scale precision, 86819678118866266539855322019385718104518097122, scale precision,
    4, 128, 4, 128, ⟨-4126383849996084523856687765540206277547136677248, -4126383849996084523856687765540206277547134580095⟩, ⟨-4126383849996084523856687765540206259038221658462, -4126383849996084523856687765540206259038219561309⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452035179538035812075122148102075718654446240893⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008294829281404787796718047455216465384960373552⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨816100712451065231583769515852576908630373977136, 828584709567330989627003268471763045440203324450⟩
def wholeCExp : DyadicInterval precision := ⟨470284756285592138984784621420327341609750138791, 478388024818681307253634944007464436783909882429⟩
def wholeCLog : DyadicInterval precision := ⟨407730810472161019111647784342939430040626383970, 413848552427284792140153405959388131317719688376⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨470284756285592138984784621420327342159505952679, scale precision, 478388024818681307253634944007464436234154068541, scale precision,
    1, 128, 1, 128, ⟨-1657169419134661979254006536943526092588881151890, -1657169419134661979254006536943526092588879054737⟩, ⟨-1632201424902130463167539031705153815581214858083, -1632201424902130463167539031705153815581212760930⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2044987844475906101620209456222347648922278069935, 2081433589632586853918219910267368495007702029271⟩
def wholeBExp : DyadicInterval precision := ⟨84679233587654760249946988532574735592936807656, 89009648778591189001521249406744908087722861902⟩
def wholeBLog : DyadicInterval precision := ⟨82316902490396555189764256220298365299446834398, 86404433763377888901088096256528796918260473271⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨84679233587654760249946988532574736142692621544, scale precision, 89009648778591189001521249406744907537967048014, scale precision,
    4, 128, 4, 128, ⟨-4162867179265173707836439820534736999503788363435, -4162867179265173707836439820534736999503786266282⟩, ⟨-4089975688951812203240418912444695288817793987423, -4089975688951812203240418912444695288817791890270⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0228StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0229StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0229StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191530054563, 4906913324212444341793886191975635191530054564⟩
def centerAExp : DyadicInterval precision := ⟨1451720686451934407431403951699999116082005297895, 1451720686451934407431403951699999118281028553448⟩
def centerALog : DyadicInterval precision := ⟨1008137063309063130766142500412726798681612460495, 1008137063309063130766142500412726800880635716048⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1451720686451934407431403951699999116631761111783, scale precision, 1451720686451934407431403951699999117731272739560, scale precision,
    0, 128, 0, 128, ⟨-9813826648424888683587772383951270936520944858, -9813826648424888683587772383951270936518847705⟩, ⟨-9813826648424888683587772383951269829601370550, -9813826648424888683587772383951269829599273397⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    1, 128, 1, 128, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨810305619251825162551057364229575233842214512477, 810305619251825162551057364229575233842214512478⟩
def centerCExp : DyadicInterval precision := ⟨482196881230644729652946651683621410566889881126, 482196881230644729652946651683621412765913136679⟩
def centerCLog : DyadicInterval precision := ⟨416715309358370637769645270144588200136641164187, 416715309358370637769645270144588202335664419740⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨482196881230644729652946651683621411116645695014, scale precision, 482196881230644729652946651683621412216157322791, scale precision,
    1, 128, 1, 128, ⟨-1620611238503650325102114728459150469350697636440, -1620611238503650325102114728459150469350695539287⟩, ⟨-1620611238503650325102114728459150466018162510624, -1620611238503650325102114728459150466018160413471⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2027442916490927762952629445032516000443139439945, 2027442916490927762952629445032516000443139439946⟩
def centerBExp : DyadicInterval precision := ⟨91172583361673108848956047732708676333109251319, 91172583361673108848956047732708678532132506872⟩
def centerBLog : DyadicInterval precision := ⟨88441780831153165257809311535957152644008956427, 88441780831153165257809311535957154843032211980⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨91172583361673108848956047732708676882865065207, scale precision, 91172583361673108848956047732708677982376692984, scale precision,
    4, 128, 4, 128, ⟨-4054885832981855525905258890065032009698896534300, -4054885832981855525905258890065032009698894437147⟩, ⟨-4054885832981855525905258890065031992073663322624, -4054885832981855525905258890065031992073661225471⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452035179538035812075122148102075718654446240893⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008294829281404787796718047455216465384960373552⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    1, 128, 1, 128, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨804111982908458854188916950074028028489953280093, 816519044566734147547882899938413303642935167648⟩
def wholeCExp : DyadicInterval precision := ⟨478114240927289536508520817954248893030551193466, 486301214019752412880487542436287190255991924015⟩
def wholeCLog : DyadicInterval precision := ⟨413642270672024755970907793581287248597264070316, 419798176738040102520251135252064422437198001138⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨478114240927289536508520817954248893580307007354, scale precision, 486301214019752412880487542436287189706236110127, scale precision,
    1, 128, 1, 128, ⟨-1633038089133468295095765799876826608966367284958, -1633038089133468295095765799876826608966365187805⟩, ⟨-1608223965816917708377833900148056055327703174625, -1608223965816917708377833900148056055327701077472⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2009316190367930134783022535351107671657362747385, 2045609572931906542858223845380941814984392615047⟩
def wholeBExp : DyadicInterval precision := ⟨88933950886795804491024260123740399004197059173, 93462459171534921490411862096746543255661538835⟩
def wholeBLog : DyadicInterval precision := ⟨86333079691665563064768368905701522764143609826, 90595607956126884055040489011360065198690576759⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨88933950886795804491024260123740399553952873061, scale precision, 93462459171534921490411862096746542705905724947, scale precision,
    4, 128, 3, 128, ⟨-4091219145863813085716447690761883639003232787774, -4091219145863813085716447690761883639003230690621⟩, ⟨-4018632380735860269566045070702215334718023340236, -4018632380735860269566045070702215334718021243083⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0229StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0230StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0230StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨821913119280391561443626590054490934771952900552, 821913119280391561443626590054490934771952900553⟩
def centerCExp : DyadicInterval precision := ⟨474598009679195268833242720504430559221807723455, 474598009679195268833242720504430561420830979008⟩
def centerCLog : DyadicInterval precision := ⟨410990384018951558465485374500073776937671364255, 410990384018951558465485374500073779136694619808⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨474598009679195268833242720504430559771563537343, scale precision, 474598009679195268833242720504430560871075165120, scale precision,
    1, 128, 1, 128, ⟨-1643826238560783122887253180108981871236853313305, -1643826238560783122887253180108981871236851216152⟩, ⟨-1643826238560783122887253180108981867850960386054, -1643826238560783122887253180108981867850958288901⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2062568936076181911955734751884215027166781026364, 2062568936076181911955734751884215027166781026365⟩
def centerBExp : DyadicInterval precision := ⟨86893726287684500539890374416780897019389983695, 86893726287684500539890374416780899218413239248⟩
def centerBLog : DyadicInterval precision := ⟨84408617164145411003965475991816297681880191831, 84408617164145411003965475991816299880903447384⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨86893726287684500539890374416780897569145797583, scale precision, 86893726287684500539890374416780898668657425360, scale precision,
    4, 128, 4, 128, ⟨-4125137872152363823911469503768430063580134245814, -4125137872152363823911469503768430063580132148661⟩, ⟨-4125137872152363823911469503768430045086991956804, -4125137872152363823911469503768430045086989859651⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨815682470269431448095708128029636649613579913243, 828163776671353447616614156752623726995953103289⟩
def wholeCExp : DyadicInterval precision := ⟨470555731486785679845618215889148237866067197398, 478661906578433611030461684702374523389958627674⟩
def wholeCLog : DyadicInterval precision := ⟨407935803595702954827445446261590080251174841227, 414054878794331926931321513169732080455341390650⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨470555731486785679845618215889148238415823011286, scale precision, 478661906578433611030461684702374522840202813786, scale precision,
    1, 128, 1, 128, ⟨-1656327553342706895233228313505247455699396864496, -1656327553342706895233228313505247455699394767343⟩, ⟨-1631364940538862896191416256059273297548587729618, -1631364940538862896191416256059273297548585632465⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2044366161332604023485325733918617247156030923800, 2080809335157903734556500614249674245808084811521⟩
def wholeBExp : DyadicInterval precision := ⟨84751602956753204244840564965076637963146964639, 89085405578100038612366137756880017005887003727⟩
def wholeBLog : DyadicInterval precision := ⟨82385306826686865613281479933767301091169605522, 86475839874888193764750603916308934372657686347⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨84751602956753204244840564965076638512902778527, scale precision, 89085405578100038612366137756880016456131189839, scale precision,
    4, 128, 4, 128, ⟨-4161618670315807469113001228499348501096451800224, -4161618670315807469113001228499348501096449703071⟩, ⟨-4088732322665208046970651467837234485292975909753, -4088732322665208046970651467837234485292973812600⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0230StableWitnesses

end


