-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0329StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0329StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:44:58.588095+00:00
-- url     : https://prove2.me/theorems/e2479dda-73ed-4e11-b427-b3299e1b74f9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0329StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0330StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0329StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0330StableWitnesses, GeneralCK.Certificates.E8TAxisProd0331StableWitnesses, GeneralCK.Certificates.E8TAxisProd0332StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0329StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0330StableWitnesses, GeneralCK.Certificates.E8TAxisProd0331StableWitnesses, GeneralCK.Certificates.E8TAxisProd0332StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0329StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0330StableWitnesses, GeneralCK.Certificates.E8TAxisProd0331StableWitnesses, GeneralCK.Certificates.E8TAxisProd0332StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0329StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0330StableWitnesses, GeneralCK/Certificates/E8TAxisProd0331StableWitnesses, GeneralCK/Certificates/E8TAxisProd0332StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0329StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0329StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨733440986312093234127888410179197994001522319513, 733440986312093234127888410179197994001522319514⟩
def centerDExp : DyadicInterval precision := ⟨535680729704461451649291949156588179014765393299, 535680729704461451649291949156588181213788648852⟩
def centerDLog : DyadicInterval precision := ⟨456387420244430310281539606035895557724605706337, 456387420244430310281539606035895559923628961890⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨535680729704461451649291949156588179564521207187, scale precision, 535680729704461451649291949156588180664032834964, scale precision,
    1, 128, 1, 128, ⟨-1466881972624186468255776820358395989502948479653, -1466881972624186468255776820358395989502946382500⟩, ⟨-1466881972624186468255776820358395986503142895557, -1466881972624186468255776820358395986503140798404⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨737253162836664068424639169110694263558496668276, 737253162836664068424639169110694263558496668277⟩
def centerCExp : DyadicInterval precision := ⟨532893470260276358850176571635400420637249007097, 532893470260276358850176571635400422836272262650⟩
def centerCLog : DyadicInterval precision := ⟨454346330009136764278902588338487139121276848833, 454346330009136764278902588338487141320300104386⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨532893470260276358850176571635400421187004820985, scale precision, 532893470260276358850176571635400422286516448762, scale precision,
    1, 128, 1, 128, ⟨-1474506325673328136849278338221388528624742306563, -1474506325673328136849278338221388528624740209410⟩, ⟨-1474506325673328136849278338221388525609246463697, -1474506325673328136849278338221388525609244366544⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1812915863847712156622872643421346888853774534644, 1812915863847712156622872643421346888853774534645⟩
def centerBExp : DyadicInterval precision := ⟨122281402032393390317363944604463923533584122030, 122281402032393390317363944604463925732607377583⟩
def centerBLog : DyadicInterval precision := ⟨117434415925763904506758405514324677477759215746, 117434415925763904506758405514324679676782471299⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨122281402032393390317363944604463924083339935918, scale precision, 122281402032393390317363944604463925182851563695, scale precision,
    3, 128, 3, 128, ⟨-3625831727695424313245745286842693784278206070251, -3625831727695424313245745286842693784278203973098⟩, ⟨-3625831727695424313245745286842693771136894165480, -3625831727695424313245745286842693771136892068327⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨727686670816724440524685346233204921246428500688, 739212305620516788391447838602016614455786978946⟩
def wholeDExp : DyadicInterval precision := ⟨531466696428681553786643034174516969558482716148, 539915612896337333160506278237532713275465316046⟩
def wholeDLog : DyadicInterval precision := ⟨453300409610535438784277685833236607008526820688, 459483149562382791203438629890379328233241384504⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨531466696428681553786643034174516970108238530036, scale precision, 539915612896337333160506278237532712725709502158, scale precision,
    1, 128, 1, 128, ⟨-1478424611241033576782895677204033230423370623258, -1478424611241033576782895677204033230423368526105⟩, ⟨-1455373341633448881049370692466409841004719898474, -1455373341633448881049370692466409841004717801321⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨731287388695801414191897623276264970291566354525, 743237227447511701214864328431153975408804381135⟩
def wholeCExp : DyadicInterval precision := ⟨528547463746913125994765537971093260735488779836, 537261764351401279199506585192988797250441056424⟩
def wholeCLog : DyadicInterval precision := ⟨451158082001934459666388436004574570179146072353, 457543934861743335128549013029760557621157892659⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨528547463746913125994765537971093261285244593724, scale precision, 537261764351401279199506585192988796700685242536, scale precision,
    1, 128, 1, 128, ⟨-1486474454895023402429728656862307952337755260858, -1486474454895023402429728656862307952337753163705⟩, ⟨-1462574777391602828383795246552529939087644825710, -1462574777391602828383795246552529939087642728557⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1795367025357589772002191998156372338068800431607, 1830520038672116921366937306175225584243177898110⟩
def wholeBExp : DyadicInterval precision := ⟨119370778197862041166482694354132719729714137873, 125253510537442359420902448349461169784822628305⟩
def wholeBLog : DyadicInterval precision := ⟨114746045731972209078600913379548174535760829323, 120174482414347035944019693751834603914886491733⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨119370778197862041166482694354132720279469951761, scale precision, 125253510537442359420902448349461169235066814417, scale precision,
    3, 128, 3, 128, ⟨-3661040077344233842733874612350451175217225439777, -3661040077344233842733874612350451175217223342624⟩, ⟨-3590734050715179544004383996312744669722859373373, -3590734050715179544004383996312744669722857276220⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0329StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0330StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0330StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271720183, 745000746231477256788872225997272556554271720184⟩
def centerDExp : DyadicInterval precision := ⟨527273459613343376350322664808293438125402667750, 527273459613343376350322664808293440324425923303⟩
def centerDLog : DyadicInterval precision := ⟨450222147616224759094825146719602335307459476714, 450222147616224759094825146719602337506482732267⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨527273459613343376350322664808293438675158481638, scale precision, 527273459613343376350322664808293439774670109415, scale precision,
    1, 128, 1, 128, ⟨-1490001492462954513577744451994545114632362931693, -1490001492462954513577744451994545114632360834540⟩, ⟨-1490001492462954513577744451994545111584726046197, -1490001492462954513577744451994545111584723949044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨748431578949766582000546962641522160863252470361, 748431578949766582000546962641522160863252470362⟩
def centerCExp : DyadicInterval precision := ⟨524803743420110816113562134906139745282733695217, 524803743420110816113562134906139747481756950770⟩
def centerCLog : DyadicInterval precision := ⟨448406086409492920675382599139879085125106227884, 448406086409492920675382599139879087324129483437⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨524803743420110816113562134906139745832489509105, scale precision, 524803743420110816113562134906139746932001136882, scale precision,
    1, 128, 1, 128, ⟨-1496863157899533164001093925283044323257495491956, -1496863157899533164001093925283044323257493394803⟩, ⟨-1496863157899533164001093925283044320195516486646, -1496863157899533164001093925283044320195514389493⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1846969133462966408111301772862766593354342665713, 1846969133462966408111301772862766593354342665714⟩
def centerBExp : DyadicInterval precision := ⟨116713775876262464095820602033056936389696661024, 116713775876262464095820602033056938588719916577⟩
def centerBLog : DyadicInterval precision := ⟨112287605593816246820922017387539290310698132890, 112287605593816246820922017387539292509721388443⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨116713775876262464095820602033056936939452474912, scale precision, 116713775876262464095820602033056938038964102689, scale precision,
    3, 128, 3, 128, ⟨-3693938266925932816222603545725533193592783960587, -3693938266925932816222603545725533193592781863434⟩, ⟨-3693938266925932816222603545725533179824588799425, -3693938266925932816222603545725533179824586702272⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786978945, 750806424999049798752938234956163650116084001298⟩
def wholeDExp : DyadicInterval precision := ⟨523100967242339682629524513379347095252573454615, 531466696428681553786643034174516971757505971701⟩
def wholeDLog : DyadicInterval precision := ⟨447152665109602019123525890115620509603294783509, 453300409610535438784277685833236609207550076241⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨523100967242339682629524513379347095802329268503, scale precision, 531466696428681553786643034174516971207750157813, scale precision,
    1, 128, 1, 128, ⟨-1501612849998099597505876469912327301768142166202, -1501612849998099597505876469912327301768140069049⟩, ⟨-1478424611241033576782895677204033227399779389680, -1478424611241033576782895677204033227399777292527⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨742431578345366751869389672720476995833122655484, 754450111391181169946783292707038783088639758434⟩
def wholeCExp : DyadicInterval precision := ⟨520499161256261253169269658260438626592552975709, 529130506008799572622474611617813275804531664421⟩
def wholeCLog : DyadicInterval precision := ⟨445235385327620924409651644573357755848393003902, 451586208332154248050465857004250033221439172824⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨520499161256261253169269658260438627142308789597, scale precision, 529130506008799572622474611617813275254775850533, scale precision,
    1, 128, 1, 128, ⟨-1508900222782362339893566585414077567720931510415, -1508900222782362339893566585414077567720929413262⟩, ⟨-1484863156690733503738779345440953990147775938719, -1484863156690733503738779345440953990147773841566⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1829314599131946497419882808047294253408844233645, 1864676445364227704420480937126220622707374834965⟩
def wholeBExp : DyadicInterval precision := ⟨113919596832567931978058761836681715587876502601, 119567853590568785229593829638848661478776935392⟩
def wholeBLog : DyadicInterval precision := ⟨109697771207304949602193661804549988943567312848, 114928228718259174016419064949877698985913626212⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨113919596832567931978058761836681716137632316489, scale precision, 119567853590568785229593829638848660929021121504, scale precision,
    3, 128, 3, 128, ⟨-3729352890728455408840961874252441252467698977364, -3729352890728455408840961874252441252467696880211⟩, ⟨-3658629198263892994839765616094588500097914944338, -3658629198263892994839765616094588500097912847185⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0330StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0331StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0331StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨733440986312093234127888410179197994001522319513, 733440986312093234127888410179197994001522319514⟩
def centerDExp : DyadicInterval precision := ⟨535680729704461451649291949156588179014765393299, 535680729704461451649291949156588181213788648852⟩
def centerDLog : DyadicInterval precision := ⟨456387420244430310281539606035895557724605706337, 456387420244430310281539606035895559923628961890⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨535680729704461451649291949156588179564521207187, scale precision, 535680729704461451649291949156588180664032834964, scale precision,
    1, 128, 1, 128, ⟨-1466881972624186468255776820358395989502948479653, -1466881972624186468255776820358395989502946382500⟩, ⟨-1466881972624186468255776820358395986503142895557, -1466881972624186468255776820358395986503140798404⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨736851530366918965430201270334456745797085054829, 736851530366918965430201270334456745797085054830⟩
def centerCExp : DyadicInterval precision := ⟨533186437633447761071817218188141946817128302075, 533186437633447761071817218188141949016151557628⟩
def centerCLog : DyadicInterval precision := ⟨454561002041154937627217218232264003616360211982, 454561002041154937627217218232264005815383467535⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨533186437633447761071817218188141947366884115963, scale precision, 533186437633447761071817218188141948466395743740, scale precision,
    1, 128, 1, 128, ⟨-1473703060733837930860402540668913493101090624712, -1473703060733837930860402540668913493101088527559⟩, ⟨-1473703060733837930860402540668913490087251691762, -1473703060733837930860402540668913490087249594609⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1812314982424177991123197662526435079107072978389, 1812314982424177991123197662526435079107072978390⟩
def centerBExp : DyadicInterval precision := ⟨122381992874702287318965050752071021166405825408, 122381992874702287318965050752071023365429080961⟩
def centerBLog : DyadicInterval precision := ⟨117527237359405703692475020746312340313709374296, 117527237359405703692475020746312342512732629849⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨122381992874702287318965050752071021716161639296, scale precision, 122381992874702287318965050752071022815673267073, scale precision,
    3, 128, 3, 128, ⟨-3624629964848355982246395325052870164779402262747, -3624629964848355982246395325052870164779400165594⟩, ⟨-3624629964848355982246395325052870151648891747972, -3624629964848355982246395325052870151648889650819⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨727686670816724440524685346233204921246428500688, 739212305620516788391447838602016614455786978946⟩
def wholeDExp : DyadicInterval precision := ⟨531466696428681553786643034174516969558482716148, 539915612896337333160506278237532713275465316046⟩
def wholeDLog : DyadicInterval precision := ⟨453300409610535438784277685833236607008526820688, 459483149562382791203438629890379328233241384504⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨531466696428681553786643034174516970108238530036, scale precision, 539915612896337333160506278237532712725709502158, scale precision,
    1, 128, 1, 128, ⟨-1478424611241033576782895677204033230423370623258, -1478424611241033576782895677204033230423368526105⟩, ⟨-1455373341633448881049370692466409841004719898474, -1455373341633448881049370692466409841004717801321⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨730886981166577453562276968076731180416584219417, 742834361291372729891888239281078093017880189846⟩
def wholeCExp : DyadicInterval precision := ⟨528838934636989681341346835359242052434771931721, 537556232175859704595533715533304933941186037142⟩
def wholeCLog : DyadicInterval precision := ⟨451372123952011486061135753011893102466625023268, 457759234735935835353343240651627840512310475313⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨528838934636989681341346835359242052984527745609, scale precision, 537556232175859704595533715533304933391430223254, scale precision,
    1, 128, 1, 128, ⟨-1485668722582745459783776478562156187555069046346, -1485668722582745459783776478562156187555066949193⟩, ⟨-1461773962333154907124553936153462359338499769085, -1461773962333154907124553936153462359338497671932⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1794768059235723271505897891786956967680013826406, 1829917287311471905349548649499246234872039055078⟩
def wholeBExp : DyadicInterval precision := ⟨119469280422197957283106737942538025932422406993, 125356217729007284566593932508241648072329178358⟩
def wholeBLog : DyadicInterval precision := ⟨114837107272358414470650904838073590551265638800, 120269079158532102036743117316932119776266188268⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨119469280422197957283106737942538026482178220881, scale precision, 125356217729007284566593932508241647522573364470, scale precision,
    3, 128, 3, 128, ⟨-3659834574622943810699097298998492476469398163678, -3659834574622943810699097298998492476469396066525⟩, ⟨-3589536118471446543011795783573913928950541906985, -3589536118471446543011795783573913928950539809832⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0331StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0332StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0332StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385356161447, 721949241039261777105100229686264310385356161448⟩
def centerDExp : DyadicInterval precision := ⟨544171400918647169539408046331758482200227109223, 544171400918647169539408046331758484399250364776⟩
def centerDLog : DyadicInterval precision := ⟨462587568506596564045749998967475930132416323351, 462587568506596564045749998967475932331439578904⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758482749982923111, scale precision, 544171400918647169539408046331758483849494550888, scale precision,
    1, 128, 1, 128, ⟨-1443898482078523554210200459372528622247213277149, -1443898482078523554210200459372528622247211179996⟩, ⟨-1443898482078523554210200459372528619294213465789, -1443898482078523554210200459372528619294211368636⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨725739047464315867516374726036205453071580912483, 725739047464315867516374726036205453071580912484⟩
def centerCExp : DyadicInterval precision := ⟨541356534743192125224459456175554358313953154697, 541356534743192125224459456175554360512976410250⟩
def centerCLog : DyadicInterval precision := ⟨460534980172042125658304244787391245004499445280, 460534980172042125658304244787391247203522700833⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨541356534743192125224459456175554358863708968585, scale precision, 541356534743192125224459456175554359963220596362, scale precision,
    1, 128, 1, 128, ⟨-1451478094928631735032749452072410907627340066512, -1451478094928631735032749452072410907627337969359⟩, ⟨-1451478094928631735032749452072410904658985680575, -1451478094928631735032749452072410904658983583422⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1778471923653248053496891502529504081182926322354, 1778471923653248053496891502529504081182926322355⟩
def centerBExp : DyadicInterval precision := ⟨128183132388681222892732011440615187216745957763, 128183132388681222892732011440615189415769213316⟩
def centerBLog : DyadicInterval precision := ⟨122870361107140722312803585027630124716783800544, 122870361107140722312803585027630126915807056097⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨128183132388681222892732011440615187766501771651, scale precision, 128183132388681222892732011440615188866013399428, scale precision,
    3, 128, 3, 128, ⟨-3556943847306496106993783005059008168633987473115, -3556943847306496106993783005059008168633985375962⟩, ⟨-3556943847306496106993783005059008156097719913450, -3556943847306496106993783005059008156097717816297⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨716228578308099727358082939138935890959899212494, 727686670816724440524685346233204921246428500689⟩
def wholeDExp : DyadicInterval precision := ⟨539915612896337333160506278237532711076442060493, 548448150163327086956497611001597703886791384129⟩
def wholeDLog : DyadicInterval precision := ⟨459483149562382791203438629890379326034218128951, 465700648921796470149242465934935277251827483709⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨539915612896337333160506278237532711626197874381, scale precision, 548448150163327086956497611001597703337035570241, scale precision,
    1, 128, 1, 128, ⟨-1455373341633448881049370692466409843980996201432, -1455373341633448881049370692466409843980994104279⟩, ⟨-1432457156616199454716165878277871780454813181077, -1432457156616199454716165878277871780454811083924⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨719808254405766980762212099586180611407586661965, 731687878298791682542639028106814433901145489908⟩
def wholeCExp : DyadicInterval precision := ⟨536967397524294968555572621087582187472662866632, 545768076641690884266447176830351104165699837924⟩
def wholeCLog : DyadicInterval precision := ⟨457328677126597882756141638592129152960138849543, 463750577525533406664036433744213516217890095216⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨536967397524294968555572621087582188022418680520, scale precision, 545768076641690884266447176830351103615944024036, scale precision,
    1, 128, 1, 128, ⟨-1463375756597583365085278056213628869298600790962, -1463375756597583365085278056213628869298598693809⟩, ⟨-1439616508811533961524424199172361221342994051749, -1439616508811533961524424199172361221342991954596⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1761035734573108415812231814899649169660312168995, 1795966057709101911334711647766516726045121792149⟩
def wholeBExp : DyadicInterval precision := ⟨125150876153492922831815558505283386650438844511, 131278446417159234245325950718373643346690446471⟩
def wholeBLog : DyadicInterval precision := ⟨120079946611671807462671293272760516491625623972, 125713319729117763271763039228836367759998094739⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨125150876153492922831815558505283387200194658399, scale precision, 131278446417159234245325950718373642796934632583, scale precision,
    3, 128, 3, 128, ⟨-3591932115418203822669423295533033458510247806837, -3591932115418203822669423295533033458510245709684⟩, ⟨-3522071469146216831624463629799298333200283136497, -3522071469146216831624463629799298333200281039344⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0332StableWitnesses

end


