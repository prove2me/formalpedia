-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0075StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0075StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:58:37.176316+00:00
-- url     : https://prove2.me/theorems/22cbea24-f960-444e-a5da-26fcf9232b0c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0075StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0076StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0075StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0076StableWitnesses, GeneralCK.Certificates.E8TAxisProd0077StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0075StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0076StableWitnesses, GeneralCK.Certificates.E8TAxisProd0077StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0075StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0076StableWitnesses, GeneralCK.Certificates.E8TAxisProd0077StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0075StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0076StableWitnesses, GeneralCK/Certificates/E8TAxisProd0077StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0075StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0075StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨143784951906453523486401736308747511963801146731, 143784951906453523486401736308747511963801146732⟩
def centerCExp : DyadicInterval precision := ⟨1200455553997433241471093829650107437063632516222, 1200455553997433241471093829650107439262655771775⟩
def centerCLog : DyadicInterval precision := ⟨876312307913377450072465511517085678912945006351, 876312307913377450072465511517085681111968261904⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1200455553997433241471093829650107437613388330110, scale precision, 1200455553997433241471093829650107438712899957887, scale precision,
    0, 128, 0, 128, ⟨-287569903812907046972803472617495024596906773935, -287569903812907046972803472617495024596904676782⟩, ⟨-287569903812907046972803472617495023258299910142, -287569903812907046972803472617495023258297812989⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨285853513404820338505729601496375842220942873735, 285853513404820338505729601496375842220942873736⟩
def centerBExp : DyadicInterval precision := ⟨988354938989533303716587227603332341159821626460, 988354938989533303716587227603332343358844882013⟩
def centerBLog : DyadicInterval precision := ⟨754960676138402977279889709654085874765785518978, 754960676138402977279889709654085876964808774531⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨988354938989533303716587227603332341709577440348, scale precision, 988354938989533303716587227603332342809089068125, scale precision,
    0, 128, 0, 128, ⟨-571707026809640677011459202992751685254822504095, -571707026809640677011459202992751685254820406942⟩, ⟨-571707026809640677011459202992751683628951087999, -571707026809640677011459202992751683628948990846⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨139464632142328242790800863371446902113522637316, 148108147869986271169876541451996606643262190666⟩
def wholeCExp : DyadicInterval precision := ⟨1193374503935763818484320017448353804443791307183, 1207573867472606940117047865330000288341849127384⟩
def wholeCLog : DyadicInterval precision := ⟨872419399585973093481858653506423335782807107340, 880215278904111554895432601471468089266246739122⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1193374503935763818484320017448353804993547121071, scale precision, 1207573867472606940117047865330000287792093313496, scale precision,
    0, 128, 0, 128, ⟨-296216295739972542339753082903993213959800264825, -296216295739972542339753082903993213959798167672⟩, ⟨-278929264284656485581601726742893803561688249661, -278929264284656485581601726742893803561686152508⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨277271358307143331511699022410631785361523651158, 294457137294997558988966870615527000026378033130⟩
def wholeBExp : DyadicInterval precision := ⟨976786602031452594313788453393719744631000533473, 1000030902333961399782025547003040623603597575104⟩
def wholeBLog : DyadicInterval precision := ⟨748043051719392730062777160911762063782803454006, 761909615141175183101165194030151440509812698646⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨976786602031452594313788453393719745180756347361, scale precision, 1000030902333961399782025547003040623053841761216, scale precision,
    0, 128, 0, 128, ⟨-588914274589995117977933741231054000875320631227, -588914274589995117977933741231054000875318534074⟩, ⟨-554542716614286663023398044821263569919604157065, -554542716614286663023398044821263569919602059912⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0075StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0076StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0076StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨135786562981532744407176542973785707700032315693, 135786562981532744407176542973785707700032315694⟩
def centerCExp : DyadicInterval precision := ⟨1213667239671959788349268414738433180580208522853, 1213667239671959788349268414738433182779231778406⟩
def centerCLog : DyadicInterval precision := ⟨883548014710720481577488483032536808430808059162, 883548014710720481577488483032536810629831314715⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1213667239671959788349268414738433181129964336741, scale precision, 1213667239671959788349268414738433182229475964518, scale precision,
    0, 128, 0, 128, ⟨-271573125963065488814353085947571416062083237880, -271573125963065488814353085947571416062081140727⟩, ⟨-271573125963065488814353085947571414738048122048, -271573125963065488814353085947571414738046024895⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨269367851291656958061157820574856895714751460503, 269367851291656958061157820574856895714751460504⟩
def centerBExp : DyadicInterval precision := ⟨1010905536282544587880923401371442581054942470311, 1010905536282544587880923401371442583253965725864⟩
def centerBLog : DyadicInterval precision := ⟨768352061535131801711860538659714807189431380141, 768352061535131801711860538659714809388454635694⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1010905536282544587880923401371442581604698284199, scale precision, 1010905536282544587880923401371442582704209911976, scale precision,
    0, 128, 0, 128, ⟨-538735702583313916122315641149713792224305257431, -538735702583313916122315641149713792224303160278⟩, ⟨-538735702583313916122315641149713790634702681734, -538735702583313916122315641149713790634700584581⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨131471339378828304616901319120236275981063672875, 140104501423603957080255867083430975685001820322⟩
def wholeCExp : DyadicInterval precision := ⟨1206516939165977478034182301920685409615456633826, 1220855380056719261952743524936059028138872676122⟩
def wholeCLog : DyadicInterval precision := ⟨879636423651667828578324327983484522079416879258, 887469782128195457844251951048425796785795894303⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1206516939165977478034182301920685410165212447714, scale precision, 1220855380056719261952743524936059027589116862234, scale precision,
    0, 128, 0, 128, ⟨-280209002847207914160511734166861952035945627178, -280209002847207914160511734166861952035943530025⟩, ⟨-262942678757656609233802638240472551304008656925, -262942678757656609233802638240472551304006559772⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨260825123272224201955122488373057881563951191170, 277930776969409987152309133436217984235744235873⟩
def wholeBExp : DyadicInterval precision := ⟨999128896371743693173117868503035940483411553911, 1022792716389535190659037248359019656207330550438⟩
def wholeBLog : DyadicInterval precision := ⟨761373963158186988811949092195581925758639618565, 775362032339477282440355951971957161786691018380⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨999128896371743693173117868503035941033167367799, scale precision, 1022792716389535190659037248359019655657574736550, scale precision,
    0, 128, 0, 128, ⟨-555861553938819974304618266872435969275659057453, -555861553938819974304618266872435969275656960300⟩, ⟨-521650246544448403910244976746115762342339543675, -521650246544448403910244976746115762342337446522⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0076StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0077StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0077StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨143144725152330608981727936468764867144537797563, 143144725152330608981727936468764867144537797564⟩
def centerCExp : DyadicInterval precision := ⟨1201507760193115864138191597336788405895568313971, 1201507760193115864138191597336788408094591569524⟩
def centerCLog : DyadicInterval precision := ⟨876889889414464727246782031609189902647008630870, 876889889414464727246782031609189904846031886423⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1201507760193115864138191597336788406445324127859, scale precision, 1201507760193115864138191597336788407544835755636, scale precision,
    0, 128, 0, 128, ⟨-286289450304661217963455872937529734957793941045, -286289450304661217963455872937529734957791843892⟩, ⟨-286289450304661217963455872937529733620359346363, -286289450304661217963455872937529733620357249210⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨285192593881366198366266551507570054859771280736, 285192593881366198366266551507570054859771280737⟩
def centerBExp : DyadicInterval precision := ⟨989249250084191454782878915757453835081293639377, 989249250084191454782878915757453837280316894930⟩
def centerBLog : DyadicInterval precision := ⟨755494094557775419733629936915105549646895953847, 755494094557775419733629936915105551845919209400⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨989249250084191454782878915757453835631049453265, scale precision, 989249250084191454782878915757453836730561081042, scale precision,
    0, 128, 0, 128, ⟨-570385187762732396732533103015140110531744399752, -570385187762732396732533103015140110531742302599⟩, ⟨-570385187762732396732533103015140108907342820348, -570385187762732396732533103015140108907340723195⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨138824824073724312515584487072396406921145910541, 147467489505837704641503792021720686236046886405⟩
def wholeCExp : DyadicInterval precision := ⟨1194421209022043368884451180509721978191836988739, 1208631620422256427272457205985983281802592323300⟩
def wholeCLog : DyadicInterval precision := ⟨872995494151319611040382737657176576721236134766, 880794356350518998071035925612790700085003884694⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1194421209022043368884451180509721978741592802627, scale precision, 1208631620422256427272457205985983281252836509412, scale precision,
    0, 128, 0, 128, ⟨-294934979011675409283007584043441373144779646522, -294934979011675409283007584043441373144777549369⟩, ⟨-277649648147448625031168974144792813177517094681, -277649648147448625031168974144792813177514997528⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨276612062758662568906369624396592009937292335738, 293794542745046640067294646993992613811650700681⟩
def wholeBExp : DyadicInterval precision := ⟨977672686556378899154880479700583293524917980231, 1000933553987258952345939520956286575061748668116⟩
def wholeBLog : DyadicInterval precision := ⟨748574071273698567109675504566805884354344410173, 762445454105232810722635421847765875875382051583⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨977672686556378899154880479700583294074673794119, scale precision, 1000933553987258952345939520956286574511992854228, scale precision,
    0, 128, 0, 128, ⟨-587589085490093280134589293987985228445120460382, -587589085490093280134589293987985228445118363229⟩, ⟨-553224125517325137812739248793184019071866080044, -553224125517325137812739248793184019071863982891⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0077StableWitnesses

end


