-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0137StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0137StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:33:04.272462+00:00
-- url     : https://prove2.me/theorems/0e54e809-f112-4c15-8028-7df9701c40a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0137StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0138StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0137StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0138StableWitnesses, GeneralCK.Certificates.E8TAxisProd0139StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0137StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0138StableWitnesses, GeneralCK.Certificates.E8TAxisProd0139StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0137StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0138StableWitnesses, GeneralCK.Certificates.E8TAxisProd0139StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0137StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0138StableWitnesses, GeneralCK/Certificates/E8TAxisProd0139StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0137StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0137StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨504850921516716661624915223882637479158109109888, 504850921516716661624915223882637479158109109889⟩
def centerCExp : DyadicInterval precision := ⟨732419669519777336096906549012551212952080774438, 732419669519777336096906549012551215151104029991⟩
def centerCLog : DyadicInterval precision := ⟨593700063361072216177846913544609025012169831590, 593700063361072216177846913544609027211193087143⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨732419669519777336096906549012551213501836588326, scale precision, 732419669519777336096906549012551214601348216103, scale precision,
    0, 128, 0, 128, ⟨-1009701843033433323249830447765274959413225609892, -1009701843033433323249830447765274959413223512739⟩, ⟨-1009701843033433323249830447765274957219212926817, -1009701843033433323249830447765274957219210829664⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1142053459507959978107753732761516301048849222181, 1142053459507959978107753732761516301048849222182⟩
def centerBExp : DyadicInterval precision := ⟨306240374404804559768392145550737248170727830849, 306240374404804559768392145550737250369751086402⟩
def centerBLog : DyadicInterval precision := ⟨278034035214956440041061239253501923286583871369, 278034035214956440041061239253501925485607126922⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨306240374404804559768392145550737248720483644737, scale precision, 306240374404804559768392145550737249819995272514, scale precision,
    2, 128, 2, 128, ⟨-2284106919015919956215507465523032604721354272922, -2284106919015919956215507465523032604721352175769⟩, ⟨-2284106919015919956215507465523032599474044712960, -2284106919015919956215507465523032599474042615807⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨495543268424541307964823262387162562286101825385, 514197227172531651826757701096059998106464853082⟩
def wholeCExp : DyadicInterval precision := ⟨723111670810691735202705412487442330952709917959, 741808243667164317623916619935340828915976313086⟩
def wholeCLog : DyadicInterval precision := ⟨587486260323262292263961080864338398888039225255, 599941007606703218084900534397005016724939214171⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨723111670810691735202705412487442331502465731847, scale precision, 741808243667164317623916619935340828366220499198, scale precision,
    1, 128, 0, 128, ⟨-1028394454345063303653515402192119997324057921624, -1028394454345063303653515402192119997324055824471⟩, ⟨-991086536849082615929646524774325123489082438319, -991086536849082615929646524774325123489080341166⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1117201928718692108021617223385872370067790757793, 1167178859140035961024426919159297585805816112666⟩
def wholeBExp : DyadicInterval precision := ⟨295889874278348482568591433948209282372669806141, 316834180029148107033218414422959583562421207788⟩
def wholeBLog : DyadicInterval precision := ⟨269451485785731215577637819296464197860550354569, 286766449489789062861980362452480266327071442804⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨295889874278348482568591433948209282922425620029, scale precision, 316834180029148107033218414422959583012665393900, scale precision,
    2, 128, 2, 128, ⟨-2334357718280071922048853838318595174327065912791, -2334357718280071922048853838318595174327063815638⟩, ⟨-2234403857437384216043234446771744737599653448006, -2234403857437384216043234446771744737599651350853⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0137StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0138StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0138StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨486985262849539121663164700186722645658546838913, 486985262849539121663164700186722645658546838914⟩
def centerCExp : DyadicInterval precision := ⟨750546815434250144892991531416034696314810169684, 750546815434250144892991531416034698513833425237⟩
def centerCLog : DyadicInterval precision := ⟨605726021032668008594440549726162447197346418916, 605726021032668008594440549726162449396369674469⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨750546815434250144892991531416034696864565983572, scale precision, 750546815434250144892991531416034697964077611349, scale precision,
    0, 128, 0, 128, ⟨-973970525699078243326329400373445292387606259605, -973970525699078243326329400373445292387604162452⟩, ⟨-973970525699078243326329400373445290246583193202, -973970525699078243326329400373445290246581096049⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1093582501974210395444474579499781193419550296662, 1093582501974210395444474579499781193419550296663⟩
def centerBExp : DyadicInterval precision := ⟨327242236418810008965175935383411000832498033725, 327242236418810008965175935383411003031521289278⟩
def centerBLog : DyadicInterval precision := ⟨295295238269583640031370359685105865373253806859, 295295238269583640031370359685105867572277062412⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨327242236418810008965175935383411001382253847613, scale precision, 327242236418810008965175935383411002481765475390, scale precision,
    2, 128, 2, 128, ⟨-2187165003948420790888949158999562389294374625375, -2187165003948420790888949158999562389294372528222⟩, ⟨-2187165003948420790888949158999562384383828658430, -2187165003948420790888949158999562384383826561277⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨477749886812595267904089875359623307557272545269, 496257886122708299080717656232804391559802806574⟩
def wholeCExp : DyadicInterval precision := ⟨741083167255899678520967171438347783723339308077, 760092570798305895630605365076300359575036354050⟩
def wholeCLog : DyadicInterval precision := ⟨599459970066116025774948586559345270603711332384, 612019337710713729234559670735098355719559635437⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨741083167255899678520967171438347784273095121965, scale precision, 760092570798305895630605365076300359025280540162, scale precision,
    0, 128, 0, 128, ⟨-992515772245416598161435312465608784203788650508, -992515772245416598161435312465608784203786553355⟩, ⟨-955499773625190535808179750719246614057478812059, -955499773625190535808179750719246614057476714906⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1069266194161851377821362925880269549299729057280, 1118171343577782758717312908018417271239127174587⟩
def wholeBExp : DyadicInterval precision := ⟨316414146119398508367925400648354457238793486784, 338314679478191600369134409702645556518987995509⟩
def wholeBLog : DyadicInterval precision := ⟨286421209434474494023425203738245478530465880830, 304314145103950816978222069600431632786757795093⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨316414146119398508367925400648354457788549300672, scale precision, 338314679478191600369134409702645555969232181621, scale precision,
    2, 128, 2, 128, ⟨-2236342687155565517434625816036834545017550912769, -2236342687155565517434625816036834545017548815616⟩, ⟨-2138532388323702755642725851760539096224542936122, -2138532388323702755642725851760539096224540838969⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0138StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0139StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0139StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨469257354606100457519272734728868876863782922692, 469257354606100457519272734728868876863782922693⟩
def centerCExp : DyadicInterval precision := ⟨768977632202560260976882071481187639208516870971, 768977632202560260976882071481187641407540126524⟩
def centerCLog : DyadicInterval precision := ⟨617852821410026113046783399399537986357940232175, 617852821410026113046783399399537988556963487728⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨768977632202560260976882071481187639758272684859, scale precision, 768977632202560260976882071481187640857784312636, scale precision,
    0, 128, 0, 128, ⟨-938514709212200915038545469457737754772420461196, -938514709212200915038545469457737754772418364043⟩, ⟨-938514709212200915038545469457737752682713326727, -938514709212200915038545469457737752682711229574⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1046158965499335972807565906388841825036910978272, 1046158965499335972807565906388841825036910978273⟩
def centerBExp : DyadicInterval precision := ⟨349183538282043705259965036641266357584011001463, 349183538282043705259965036641266359783034257016⟩
def centerBLog : DyadicInterval precision := ⟨313113422963367925336023920765893147899257842157, 313113422963367925336023920765893150098281097710⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨349183538282043705259965036641266358133766815351, scale precision, 349183538282043705259965036641266359233278443128, scale precision,
    2, 128, 2, 128, ⟨-2092317930998671945615131812777683652374816419881, -2092317930998671945615131812777683652374814322728⟩, ⟨-2092317930998671945615131812777683647772829590357, -2092317930998671945615131812777683647772827493204⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨460091564435561259240709968794075934566944012036, 478458994542216572420101618630227318965760431276⟩
def wholeCExp : DyadicInterval precision := ⟨759355348100787594485829608227292426499445732655, 778683644276763750590717162547461277152115240125⟩
def wholeCLog : DyadicInterval precision := ⟨611534266680129103556842684329580873109540015318, 624198801817832807762057890746298067296041156341⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨759355348100787594485829608227292427049201546543, scale precision, 778683644276763750590717162547461276602359426237, scale precision,
    0, 128, 0, 128, ⟨-956917989084433144840203237260454638989615495559, -956917989084433144840203237260454638989613398406⟩, ⟨-920183128871122518481419937588151868102059230021, -920183128871122518481419937588151868102057132868⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1022372861277245739002886928894538520949876104748, 1070214655428945250809954185107274242530860726640⟩
def wholeBExp : DyadicInterval precision := ⟨337875856540075881664697066351840843245872564631, 360736547835041306824950537159995616908268039827⟩
def wholeBLog : DyadicInterval precision := ⟨303957765048045373044145779769888236137935737603, 322408856761182563500821520578483381885427902312⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨337875856540075881664697066351840843795628378519, scale precision, 360736547835041306824950537159995616358512225939, scale precision,
    2, 128, 2, 128, ⟨-2140429310857890501619908370214548487439723198200, -2140429310857890501619908370214548487439721101047⟩, ⟨-2044745722554491478005773857789077039672451846694, -2044745722554491478005773857789077039672449749541⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0139StableWitnesses

end


