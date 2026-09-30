-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0321StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0321StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:12:29.994717+00:00
-- url     : https://prove2.me/theorems/de43bdc8-26e4-41c4-86ba-6ea831f32da3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0321StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0322StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0321StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0322StableWitnesses, GeneralCK.Certificates.E8TAxisProd0323StableWitnesses, GeneralCK.Certificates.E8TAxisProd0324StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0321StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0322StableWitnesses, GeneralCK.Certificates.E8TAxisProd0323StableWitnesses, GeneralCK.Certificates.E8TAxisProd0324StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0321StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0322StableWitnesses, GeneralCK.Certificates.E8TAxisProd0323StableWitnesses, GeneralCK.Certificates.E8TAxisProd0324StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0321StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0322StableWitnesses, GeneralCK/Certificates/E8TAxisProd0323StableWitnesses, GeneralCK/Certificates/E8TAxisProd0324StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0321StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0321StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨738056675805332691003299679694934399135140564468, 738056675805332691003299679694934399135140564469⟩
def centerCExp : DyadicInterval precision := ⟨532307837677272658229436750358942513338559174794, 532307837677272658229436750358942515537582430347⟩
def centerCLog : DyadicInterval precision := ⟨453917112817611376904390458297104517347471580381, 453917112817611376904390458297104519546494835934⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨532307837677272658229436750358942513888314988682, scale precision, 532307837677272658229436750358942514987826616459, scale precision,
    1, 128, 1, 128, ⟨-1476113351610665382006599359389868799779688887804, -1476113351610665382006599359389868799779686790651⟩, ⟨-1476113351610665382006599359389868796760875467223, -1476113351610665382006599359389868796760873370070⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1814117820676313729352789958734748956908598816317, 1814117820676313729352789958734748956908598816318⟩
def centerBExp : DyadicInterval precision := ⟨122080435912310853450169100291965653283950423160, 122080435912310853450169100291965655482973678713⟩
def centerBLog : DyadicInterval precision := ⟨117248954317454970050541423402373133131784819980, 117248954317454970050541423402373135330808075533⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨122080435912310853450169100291965653833706237048, scale precision, 122080435912310853450169100291965654933217864825, scale precision,
    3, 128, 3, 128, ⟨-3628235641352627458705579917469497920398671102457, -3628235641352627458705579917469497920398669005304⟩, ⟨-3628235641352627458705579917469497907235726259971, -3628235641352627458705579917469497907235724162818⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨732088450015273885412168945467779610187390537763, 744043209547391812896925149715910618876663149158⟩
def wholeCExp : DyadicInterval precision := ⟨527964823342261549886606675883753607416375142650, 536673131676134175886659866352304691727646145206⟩
def wholeCLog : DyadicInterval precision := ⟨450730125433731886765940776201445941947625456800, 457113461540330669166646829324555654077246243127⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨527964823342261549886606675883753607966130956538, scale precision, 536673131676134175886659866352304691177890331318, scale precision,
    1, 128, 1, 128, ⟨-1488086419094783625793850299431821239275150367305, -1488086419094783625793850299431821239275148270152⟩, ⟨-1464176900030547770824337890935559218877652913218, -1464176900030547770824337890935559218877650816065⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1796565156237215979596483990466467059040684533886, 1831725730724981834600832200022148056449235356021⟩
def wholeBExp : DyadicInterval precision := ⟨119173986449980794064713985074084545010657879316, 125048314545172815726990485764531019294461118381⟩
def wholeBLog : DyadicInterval precision := ⟨114564102292532393209878160549286626695293917094, 119985471733263886206512940327500587492083664562⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨119173986449980794064713985074084545560413693204, scale precision, 125048314545172815726990485764531018744705304493, scale precision,
    3, 128, 3, 128, ⟨-3663451461449963669201664400044296119640455024458, -3663451461449963669201664400044296119640452927305⟩, ⟨-3593130312474431959192967980932934111656101410787, -3593130312474431959192967980932934111656099313634⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0321StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0322StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0322StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨749239712234780662806981473307830555095652417339, 749239712234780662806981473307830555095652417340⟩
def centerCExp : DyadicInterval precision := ⟨524223686665407013326805074616375827844727088660, 524223686665407013326805074616375830043750344213⟩
def centerCLog : DyadicInterval precision := ⟨447979224702831025638682078042740086992046245223, 447979224702831025638682078042740089191069500776⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨524223686665407013326805074616375828394482902548, scale precision, 524223686665407013326805074616375829493994530325, scale precision,
    1, 128, 1, 128, ⟨-1498479424469561325613962946615661111723989435272, -1498479424469561325613962946615661111723987338119⟩, ⟨-1498479424469561325613962946615661108658622331237, -1498479424469561325613962946615661108658620234084⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1848178223834490707861550233971959371052118144762, 1848178223834490707861550233971959371052118144763⟩
def centerBExp : DyadicInterval precision := ⟨116520822522197371279025946167185527474902590292, 116520822522197371279025946167185529673925845845⟩
def centerBLog : DyadicInterval precision := ⟨112108910796663641894088814500657988034146393100, 112108910796663641894088814500657990233169648653⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨116520822522197371279025946167185528024658404180, scale precision, 116520822522197371279025946167185529124170031957, scale precision,
    3, 128, 3, 128, ⟨-3696356447668981415723100467943918748999734681312, -3696356447668981415723100467943918748999732584159⟩, ⟨-3696356447668981415723100467943918735208739994896, -3696356447668981415723100467943918735208737897743⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨743237227447511701214864328431153975408804381134, 755260746152291163860170870995844609651218718820⟩
def wholeCExp : DyadicInterval precision := ⟨519922082504956804614508079898252108003713390684, 528547463746913125994765537971093262934512035389⟩
def wholeCLog : DyadicInterval precision := ⟨444809792993547236939148976338631925652358131547, 451158082001934459666388436004574572378169327906⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨519922082504956804614508079898252108553469204572, scale precision, 528547463746913125994765537971093262384756221501, scale precision,
    1, 128, 1, 128, ⟨-1510521492304582327720341741991689220847802780534, -1510521492304582327720341741991689220847800683381⟩, ⟨-1486474454895023402429728656862307949297464360834, -1486474454895023402429728656862307949297462263681⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1830520038672116921366937306175225584243177898109, 1865889096222728188412355876142391027903805484196⟩
def wholeBExp : DyadicInterval precision := ⟨113730708727298394244534889706248045416817590665, 119370778197862041166482694354132721928737393426⟩
def wholeBLog : DyadicInterval precision := ⟨109522531201747066994668216297727467728694138474, 114746045731972209078600913379548176734784084876⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨113730708727298394244534889706248045966573404553, scale precision, 119370778197862041166482694354132721378981579538, scale precision,
    3, 128, 3, 128, ⟨-3731778192445456376824711752284782062872274069295, -3731778192445456376824711752284782062872271972142⟩, ⟨-3661040077344233842733874612350451161755488249818, -3661040077344233842733874612350451161755486152665⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0322StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0323StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0323StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨737654877969631034537594522192142192077747018860, 737654877969631034537594522192142192077747018861⟩
def centerCExp : DyadicInterval precision := ⟨532600603614184533246476044062503654319650977469, 532600603614184533246476044062503656518674233022⟩
def centerCLog : DyadicInterval precision := ⟨454131700264574368361204714310637252403646953264, 454131700264574368361204714310637254602670208817⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨532600603614184533246476044062503654869406791357, scale precision, 532600603614184533246476044062503655968918419134, scale precision,
    1, 128, 1, 128, ⟨-1475309755939262069075189044384284385664072088800, -1475309755939262069075189044384284385664069991647⟩, ⟨-1475309755939262069075189044384284382646918083799, -1475309755939262069075189044384284382646915986646⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1813516809949433064885465930060512564897404661915, 1813516809949433064885465930060512564897404661916⟩
def centerBExp : DyadicInterval precision := ⟨122180883055739761590996758934825668615719624209, 122180883055739761590996758934825670814742879762⟩
def centerBLog : DyadicInterval precision := ⟨117341654917797004721097768526373763229427876890, 117341654917797004721097768526373765428451132443⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨122180883055739761590996758934825669165475438097, scale precision, 122180883055739761590996758934825670264987065874, scale precision,
    3, 128, 3, 128, ⟨-3627033619898866129770931860121025136370872044541, -3627033619898866129770931860121025136370869947388⟩, ⟨-3627033619898866129770931860121025123218748700275, -3627033619898866129770931860121025123218746603122⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨731687878298791682542639028106814433901145489907, 743640176853088305713584024449537137481511845037⟩
def wholeCExp : DyadicInterval precision := ⟨528256093321136938591583775534217479349174785172, 536967397524294968555572621087582189671686122185⟩
def wholeCLog : DyadicInterval precision := ⟨450944082492356533225239494812990818077592008691, 457328677126597882756141638592129155159162105096⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨528256093321136938591583775534217479898930599060, scale precision, 536967397524294968555572621087582189121930308297, scale precision,
    1, 128, 1, 128, ⟨-1487280353706176611427168048899074276484008655897, -1487280353706176611427168048899074276484006558744⟩, ⟨-1463375756597583365085278056213628866305983265821, -1463375756597583365085278056213628866305981168668⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1795966057709101911334711647766516726045121792148, 1831122853160934571055545818495106763469077934987⟩
def wholeBExp : DyadicInterval precision := ⟨119272346884735835250754085466297053053088986106, 125150876153492922831815558505283388849462100064⟩
def wholeBLog : DyadicInterval precision := ⟨114655044078304241023680946016243564215684983730, 120079946611671807462671293272760518690648879525⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨119272346884735835250754085466297053602844799994, scale precision, 125150876153492922831815558505283388299706286176, scale precision,
    3, 128, 3, 128, ⟨-3662245706321869142111091636990213533674580264918, -3662245706321869142111091636990213533674578167765⟩, ⟨-3591932115418203822669423295533033445670241458902, -3591932115418203822669423295533033445670239361749⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0323StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0324StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0324StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨726537837793173083693074137979154395585725924588, 726537837793173083693074137979154395585725924589⟩
def centerCExp : DyadicInterval precision := ⟨540765096331219150960831999553930074160209486142, 540765096331219150960831999553930076359232741695⟩
def centerCLog : DyadicInterval precision := ⟨460103339095118903969319405890724282093751164779, 460103339095118903969319405890724284292774420332⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨540765096331219150960831999553930074709965300030, scale precision, 540765096331219150960831999553930075809476927807, scale precision,
    1, 128, 1, 128, ⟨-1453075675586346167386148275958308792657253345270, -1453075675586346167386148275958308792657251248117⟩, ⟨-1453075675586346167386148275958308789685652450237, -1453075675586346167386148275958308789685650353084⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1779666273231019310261708602767380970039478973378, 1779666273231019310261708602767380970039478973379⟩
def centerBExp : DyadicInterval precision := ⟨127973799161047559237307122316010300238308640670, 127973799161047559237307122316010302437331896223⟩
def centerBLog : DyadicInterval precision := ⟨122677894647112219140346386901715155825807224263, 122677894647112219140346386901715158024830479816⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨127973799161047559237307122316010300788064454558, scale precision, 127973799161047559237307122316010301887576082335, scale precision,
    3, 128, 3, 128, ⟨-3559332546462038620523417205534761946357345879196, -3559332546462038620523417205534761946357343782043⟩, ⟨-3559332546462038620523417205534761933800572111480, -3559332546462038620523417205534761933800570014327⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨720604627137442571971635842887643880059900459958, 732489103884959677068193236220434180558274845111⟩
def wholeCExp : DyadicInterval precision := ⟨536378966788546601555137569569386272004923344358, 545173622203440533669542480593903943525913862092⟩
def wholeCLog : DyadicInterval precision := ⟨456898288112793945676359883212336099549073521485, 463317688611057747267494064599643735677635356139⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨536378966788546601555137569569386272554679158246, scale precision, 545173622203440533669542480593903942976158048204, scale precision,
    1, 128, 1, 128, ⟨-1464978207769919354136386472440868362614501016269, -1464978207769919354136386472440868362614498919116⟩, ⟨-1441209254274885143943271685775287758646016390087, -1441209254274885143943271685775287758646014292934⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1762226079877476289842927684052120418677636043985, 1797164320888887703000211489752848787788502778263⟩
def wholeBExp : DyadicInterval precision := ⟨124945825680480090273412424284015551409233301291, 131064776485844737456511339257400016077857375567⟩
def wholeBLog : DyadicInterval precision := ⟨119891057761852561835099961921823182970478079140, 125517247524620304996542505988065009963097464961⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨124945825680480090273412424284015551958989115179, scale precision, 131064776485844737456511339257400015528101561679, scale precision,
    3, 128, 3, 128, ⟨-3594328641777775406000422979505697582007545742793, -3594328641777775406000422979505697582007543645640⟩, ⟨-3524452159754952579685855368104240831224953124766, -3524452159754952579685855368104240831224951027613⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0324StableWitnesses

end


