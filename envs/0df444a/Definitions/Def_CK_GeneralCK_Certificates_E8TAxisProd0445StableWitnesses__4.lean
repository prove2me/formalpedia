-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0445StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:23:56.239796+00:00
-- url     : https://prove2.me/theorems/8e47a8a1-5c64-4f35-90ec-fea48611d360
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0445StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0446StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0445StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0446StableWitnesses, GeneralCK.Certificates.E8TAxisProd0447StableWitnesses, GeneralCK.Certificates.E8TAxisProd0448StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0445StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0446StableWitnesses, GeneralCK.Certificates.E8TAxisProd0447StableWitnesses, GeneralCK.Certificates.E8TAxisProd0448StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0445StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0446StableWitnesses, GeneralCK.Certificates.E8TAxisProd0447StableWitnesses, GeneralCK.Certificates.E8TAxisProd0448StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0445StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0446StableWitnesses, GeneralCK/Certificates/E8TAxisProd0447StableWitnesses, GeneralCK/Certificates/E8TAxisProd0448StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0445StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0445StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨734042414326775546425032761271467813013906666797, 734042414326775546425032761271467813013906666798⟩
def centerCExp : DyadicInterval precision := ⟨535240031114564080803365031417524252216082550380, 535240031114564080803365031417524254415105805933⟩
def centerCLog : DyadicInterval precision := ⟨456064889466380159798215392699396195465240077662, 456064889466380159798215392699396197664263333215⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨535240031114564080803365031417524252765838364268, scale precision, 535240031114564080803365031417524253865349992045, scale precision,
    1, 128, 1, 128, ⟨-1468084828653551092850065522542935627528952143591, -1468084828653551092850065522542935627528950046438⟩, ⟨-1468084828653551092850065522542935624526676620749, -1468084828653551092850065522542935624526674523596⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1808110627903270700325143133155988188836709042795, 1808110627903270700325143133155988188836709042796⟩
def centerBExp : DyadicInterval precision := ⟨123088143730302566286428670637494139380188919082, 123088143730302566286428670637494141579212174635⟩
def centerBLog : DyadicInterval precision := ⟨118178680824312027858515367868788792606524552143, 118178680824312027858515367868788794805547807696⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨123088143730302566286428670637494139929944732970, scale precision, 123088143730302566286428670637494141029456360747, scale precision,
    3, 128, 3, 128, ⟨-3616221255806541400650286266311976384201009832829, -3616221255806541400650286266311976384201007735676⟩, ⟨-3616221255806541400650286266311976371145828435493, -3616221255806541400650286266311976371145826338340⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨728086423187601485414030335955879143113100802116, 740016625879139692246839118143765550469418119117⟩
def wholeCExp : DyadicInterval precision := ⟨530882045336521385092588803484129145890374814309, 539620336426298673833260170654239264030675191884⟩
def wholeCLog : DyadicInterval precision := ⟨452871605062747921265505140167037979491413854840, 459267512927206948597737950345226370136669599495⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨530882045336521385092588803484129146440130628197, scale precision, 539620336426298673833260170654239263480919377996, scale precision,
    1, 128, 1, 128, ⟨-1480033251758279384493678236287531102452297817616, -1480033251758279384493678236287531102452295720463⟩, ⟨-1456172846375202970828060671911758284737250202554, -1456172846375202970828060671911758284737248105401⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1790577155268251264318358183860781884375991453422, 1825699799823815535191144023111417836702784920971⟩
def wholeBExp : DyadicInterval precision := ⟨120160784262046053534712171499709069064198490183, 126077209366697777120126321300719763195039224649⟩
def wholeBLog : DyadicInterval precision := ⟨115476216458801569614639981483303279538727928257, 120932964172539280471025078043449530788296569768⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨120160784262046053534712171499709069613954304071, scale precision, 126077209366697777120126321300719762645283410761, scale precision,
    3, 128, 3, 128, ⟨-3651399599647631070382288046222835680092186886444, -3651399599647631070382288046222835680092184789291⟩, ⟨-3581154310536502528636716367721563762379150783062, -3581154310536502528636716367721563762379148685909⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0445StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0446StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0446StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨722547143799236287942572850543624893283984436657, 722547143799236287942572850543624893283984436658⟩
def centerCExp : DyadicInterval precision := ⟨543726340161232027946975001961542913976381944369, 543726340161232027946975001961542916175405199922⟩
def centerCLog : DyadicInterval precision := ⟨462263223913802709414718891098995805394711725662, 462263223913802709414718891098995807593734981215⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨543726340161232027946975001961542914526137758257, scale precision, 543726340161232027946975001961542915625649386034, scale precision,
    1, 128, 1, 128, ⟨-1445094287598472575885145701087249788045678399087, -1445094287598472575885145701087249788045676301934⟩, ⟨-1445094287598472575885145701087249785090261444698, -1445094287598472575885145701087249785090259347545⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1773697238683273688499152152221351513105721100796, 1773697238683273688499152152221351513105721100797⟩
def centerBExp : DyadicInterval precision := ⟨129023415998545183374551538732991958278304690608, 129023415998545183374551538732991960477327946161⟩
def centerBLog : DyadicInterval precision := ⟨123642684927611092098111319178671050253482945720, 123642684927611092098111319178671052452506201273⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨129023415998545183374551538732991958828060504496, scale precision, 129023415998545183374551538732991959927572132273, scale precision,
    3, 128, 3, 128, ⟨-3547394477366547376998304304442703032438754904505, -3547394477366547376998304304442703032438752807352⟩, ⟨-3547394477366547376998304304442703019984131595829, -3547394477366547376998304304442703019984129498676⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨716625997303320235477651725761357209197888139370, 728486257313942527219704926193369205483883629524⟩
def wholeCExp : DyadicInterval precision := ⟨539325161102103299534207626345967361066615585261, 548149957608301623724888081959574620077267662556⟩
def wholeCLog : DyadicInterval precision := ⟨459051918353187739231753732362930817453728580737, 465483807067719270488136912617592971912358734286⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨539325161102103299534207626345967361616371399149, scale precision, 548149957608301623724888081959574619527511848668, scale precision,
    1, 128, 1, 128, ⟨-1456972514627885054439409852386738412457535668910, -1456972514627885054439409852386738412457533571757⟩, ⟨-1433251994606640470955303451522714416929994085016, -1433251994606640470955303451522714416929991987863⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1756277128622506345972574320203850945403883756702, 1791175656297438879993694687522273246484835596035⟩
def wholeBExp : DyadicInterval precision := ⟨125973991627547044524441153065708186183859771068, 132136113374318253076307810432189810453635935835⟩
def wholeBLog : DyadicInterval precision := ⟨120837940357370023186589993824604908754718175525, 126500085155101967253583616649889667723038864024⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨125973991627547044524441153065708186733615584956, scale precision, 132136113374318253076307810432189809903880121947, scale precision,
    3, 128, 3, 128, ⟨-3582351312594877759987389375044546499347727041879, -3582351312594877759987389375044546499347724944726⟩, ⟨-3512554257245012691945148640407701884727152130851, -3512554257245012691945148640407701884727150033698⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0446StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0447StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0447StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823374015368, 710524563403850356500890582610538039823374015369⟩
def centerDExp : DyadicInterval precision := ⟨552745918518612785766768712299414359359889019406, 552745918518612785766768712299414361558912274959⟩
def centerDLog : DyadicInterval precision := ⟨468822363559667384554973018042110607773397723001, 468822363559667384554973018042110609972420978554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414359909644833294, scale precision, 552745918518612785766768712299414361009156461071, scale precision,
    1, 128, 1, 128, ⟨-1421049126807700713001781165221076081100344655889, -1421049126807700713001781165221076081100342558736⟩, ⟨-1421049126807700713001781165221076078193153502733, -1421049126807700713001781165221076078193151405580⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨711118990542992569664521602278231630734582890235, 711118990542992569664521602278231630734582890236⟩
def centerCExp : DyadicInterval precision := ⟨552296471775827965112706377481891503175423597929, 552296471775827965112706377481891505374446853482⟩
def centerCLog : DyadicInterval precision := ⟨468496216734216149291688901905322817991046717999, 468496216734216149291688901905322820190069973552⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨552296471775827965112706377481891503725179411817, scale precision, 552296471775827965112706377481891504824691039594, scale precision,
    1, 128, 1, 128, ⟨-1422237981085985139329043204556463262923945309792, -1422237981085985139329043204556463262923943212639⟩, ⟨-1422237981085985139329043204556463260014388348304, -1422237981085985139329043204556463260014386251151⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1739509171672602433986987343945644628376283751069, 1739509171672602433986987343945644628376283751070⟩
def centerBExp : DyadicInterval precision := ⟨135203189819755972837831136525888569347808837589, 135203189819755972837831136525888571546832093142⟩
def centerBLog : DyadicInterval precision := ⟨129310152424296139170820024358048569272512244112, 129310152424296139170820024358048571471535499665⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨135203189819755972837831136525888569897564651477, scale precision, 135203189819755972837831136525888570997076279254, scale precision,
    3, 128, 3, 128, ⟨-3479018343345204867973974687891289262695246554107, -3479018343345204867973974687891289262695244456954⟩, ⟨-3479018343345204867973974687891289250809890547324, -3479018343345204867973974687891289250809888450171⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    1, 128, 1, 128, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨705232195447749529846185115854158530882609513902, 717023496903120910002674981283023727125938253401⟩
def wholeCExp : DyadicInterval precision := ⟨547851866751135760472412415515319334741294893838, 556763640442969877903307630244600434395199585453⟩
def wholeCLog : DyadicInterval precision := ⟨465267007006069053334345831556498270955613631599, 471734646474082036318131261500638381037654540036⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨547851866751135760472412415515319335291050707726, scale precision, 556763640442969877903307630244600433845443771565, scale precision,
    1, 128, 1, 128, ⟨-1434046993806241820005349962566047455718458342798, -1434046993806241820005349962566047455718456245645⟩, ⟨-1410464390895499059692370231708317060322113947018, -1410464390895499059692370231708317060322111849865⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1722207537783939284051018161965604178270685889102, 1756871710975547950726506190158551621521097047154⟩
def wholeBExp : DyadicInterval precision := ⟨132028643297012214213248332887012217006615797399, 138442527176722213024059573691808631450184643823⟩
def wholeBLog : DyadicInterval precision := ⟨126401522611513272205504715999844237425462927860, 132272190786316562849960840484993256145310430424⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨132028643297012214213248332887012217556371611287, scale precision, 138442527176722213024059573691808630900428829935, scale precision,
    3, 128, 3, 128, ⟨-3513743421951095901453012380317103249127761138764, -3513743421951095901453012380317103249127759041611⟩, ⟨-3444415075567878568102036323931208350737744140460, -3444415075567878568102036323931208350737742043307⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0447StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0448StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0448StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨699165997627898866254694872768746753397359927635, 699165997627898866254694872768746753397359927636⟩
def centerDExp : DyadicInterval precision := ⟨561404751706234480105216227684808901745528779369, 561404751706234480105216227684808903944552034922⟩
def centerDLog : DyadicInterval precision := ⟨475091591069212524269724099885343165971571379074, 475091591069212524269724099885343168170594634627⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨561404751706234480105216227684808902295284593257, scale precision, 561404751706234480105216227684808903394796221034, scale precision,
    1, 128, 1, 128, ⟨-1398331995255797732509389745537493508225896930926, -1398331995255797732509389745537493508225894833773⟩, ⟨-1398331995255797732509389745537493505363544876768, -1398331995255797732509389745537493505363542779615⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨705281590890329838910003699123827632327752752697, 705281590890329838910003699123827632327752752698⟩
def centerCExp : DyadicInterval precision := ⟨556726007016828547060414708394094301932369989991, 556726007016828547060414708394094304131393245544⟩
def centerCLog : DyadicInterval precision := ⟨471707394443675100159562937828326131543236330828, 471707394443675100159562937828326133742259586381⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨556726007016828547060414708394094302482125803879, scale precision, 556726007016828547060414708394094303581637431656, scale precision,
    1, 128, 1, 128, ⟨-1410563181780659677820007398247655266098710234065, -1410563181780659677820007398247655266098708136912⟩, ⟨-1410563181780659677820007398247655263212302873878, -1410563181780659677820007398247655263212300776725⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1713800995003714018498320327469534371070653370024, 1713800995003714018498320327469534371070653370025⟩
def centerBExp : DyadicInterval precision := ⟨140044363315892589297279694148419052836357134197, 140044363315892589297279694148419055035380389750⟩
def centerBLog : DyadicInterval precision := ⟨133734688694928425391084562011673084165481184621, 133734688694928425391084562011673086364504440174⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨140044363315892589297279694148419053386112948085, scale precision, 140044363315892589297279694148419054485624575862, scale precision,
    3, 128, 3, 128, ⟨-3427601990007428036996640654939068747878554209016, -3427601990007428036996640654939068747878552111863⟩, ⟨-3427601990007428036996640654939068736404061368231, -3427601990007428036996640654939068736404059271078⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821414414, 704837076587479092158941059188951191105662022839⟩
def wholeDExp : DyadicInterval precision := ⟨557064765387537285209117120927584102725232557331, 565765939962058116901418666290376204947661904598⟩
def wholeDLog : DyadicInterval precision := ⟨471952686082951260798866870121334518051885287659, 478239054014281969770673762969782323901449402529⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨557064765387537285209117120927584103274988371219, scale precision, 565765939962058116901418666290376204397906090710, scale precision,
    1, 128, 1, 128, ⟨-1409674153174958184317882118377902383653651143312, -1409674153174958184317882118377902383653649046159⟩, ⟨-1387022411658040514847764993209478983971500023954, -1387022411658040514847764993209478983971497926801⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨699412226729351037223251834141358780805047251836, 711168534265659926846046301936513378429429882319⟩
def wholeCExp : DyadicInterval precision := ⟨552259028238342516585564421278776739205392246456, 561215616234337660797995178659569173047914418446⟩
def wholeCLog : DyadicInterval precision := ⟨468469042063699554140296213609861686954219643695, 474954938811624802399157458689696647649153173291⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨552259028238342516585564421278776739755148060344, scale precision, 561215616234337660797995178659569172498158604558, scale precision,
    1, 128, 1, 128, ⟨-1422337068531319853692092603873026758313737928927, -1422337068531319853692092603873026758313735831774⟩, ⟨-1398824453458702074446503668282717560178437204036, -1398824453458702074446503668282717560178435106883⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1696592364383445283685959180461638427222092120206, 1731072480895751065327871566963525704787856849617⟩
def wholeBExp : DyadicInterval precision := ⟨136773188137675934815327620589792141817955583246, 143381441059296053248962342673329572131833857679⟩
def wholeBLog : DyadicInterval precision := ⟨130746502915639054692469181854095130221983223602, 136776793308230379246279946956164847568572313437⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨136773188137675934815327620589792142367711397134, scale precision, 143381441059296053248962342673329571582078043791, scale precision,
    3, 128, 3, 128, ⟨-3462144961791502130655743133927051415450177667551, -3462144961791502130655743133927051415450175570398⟩, ⟨-3393184728766890567371918360923276848840468265406, -3393184728766890567371918360923276848840466168253⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0448StableWitnesses

end


