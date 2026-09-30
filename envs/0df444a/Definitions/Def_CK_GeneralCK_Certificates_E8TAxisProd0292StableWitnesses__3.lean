-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0292StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0292StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:58:28.068631+00:00
-- url     : https://prove2.me/theorems/a2596a18-b58a-4f28-a6dd-75bb80a27b33
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0292StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0293StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0292StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0293StableWitnesses, GeneralCK.Certificates.E8TAxisProd0294StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0292StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0293StableWitnesses, GeneralCK.Certificates.E8TAxisProd0294StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0292StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0293StableWitnesses, GeneralCK.Certificates.E8TAxisProd0294StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0292StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0293StableWitnesses, GeneralCK/Certificates/E8TAxisProd0294StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0292StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0292StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨728136397981575104963875272539904249170421239680, 728136397981575104963875272539904249170421239681⟩
def centerCExp : DyadicInterval precision := ⟨539583433979744408289514900022501316393207967459, 539583433979744408289514900022501318592231223012⟩
def centerCLog : DyadicInterval precision := ⟨459240561305037091897784235335824250835650192589, 459240561305037091897784235335824253034673448142⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨539583433979744408289514900022501316942963781347, scale precision, 539583433979744408289514900022501318042475409124, scale precision,
    1, 128, 1, 128, ⟨-1456272795963150209927750545079808499829897808577, -1456272795963150209927750545079808499829895711424⟩, ⟨-1456272795963150209927750545079808496851789247296, -1456272795963150209927750545079808496851787150143⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1782055783421333531094744799875295483671145615889, 1782055783421333531094744799875295483671145615890⟩
def centerBExp : DyadicInterval precision := ⟨127556016150779824450586180506993358694206281814, 127556016150779824450586180506993360893229537367⟩
def centerBLog : DyadicInterval precision := ⟨122293698201904458321069646585574610236648979425, 122293698201904458321069646585574612435672234978⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨127556016150779824450586180506993359243962095702, scale precision, 127556016150779824450586180506993360343473723479, scale precision,
    3, 128, 3, 128, ⟨-3564111566842667062189489599750590973641242705250, -3564111566842667062189489599750590973641240608097⟩, ⟨-3564111566842667062189489599750590961043341855470, -3564111566842667062189489599750590961043339758317⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨722198344994417869219609110170833200809152022274, 734092541689480100535415985938889722535476714773⟩
def wholeCExp : DyadicInterval precision := ⟨535203316477681163998064756142718746967455486207, 543985931203311227643823781124117992803635345195⟩
def wholeCLog : DyadicInterval precision := ⟨456038016187733646968625481324462385725424888185, 462452413463253984708760357722707629291174333622⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨535203316477681163998064756142718747517211300095, scale precision, 543985931203311227643823781124117992253879531307, scale precision,
    1, 128, 1, 128, ⟨-1468185083378960201070831971877779446572195216723, -1468185083378960201070831971877779446572193119570⟩, ⟨-1444396689988835738439218220341666400141301781013, -1444396689988835738439218220341666400141299683860⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1764607600105616150080605020414501265452494244061, 1799561639670250482571270485047135300042224190393⟩
def wholeBExp : DyadicInterval precision := ⟨124536597017393794584460478524852125722271603761, 130638331056824412386060033823056435027568523753⟩
def wholeBLog : DyadicInterval precision := ⟨119514010599774977156535846834058501458607166320, 125125845227722155733946265151055995862293261706⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨124536597017393794584460478524852126272027417649, scale precision, 130638331056824412386060033823056434477812709865, scale precision,
    3, 128, 3, 128, ⟨-3599123279340500965142540970094270606536119391233, -3599123279340500965142540970094270606536117294080⟩, ⟨-3529215200211232300161210040829002524754658193441, -3529215200211232300161210040829002524754656096288⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0292StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0293StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0293StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨716675680344407676747437670590218710038014350711, 716675680344407676747437670590218710038014350712⟩
def centerCExp : DyadicInterval precision := ⟨548112690689958297074083696118477158732607276661, 548112690689958297074083696118477160931630532214⟩
def centerCLog : DyadicInterval precision := ⟨465456704774304209509662333622774831741700820189, 465456704774304209509662333622774833940724075742⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨548112690689958297074083696118477159282363090549, scale precision, 548112690689958297074083696118477160381874718326, scale precision,
    1, 128, 1, 128, ⟨-1433351360688815353494875341180437421541912652874, -1433351360688815353494875341180437421541910555721⟩, ⟨-1433351360688815353494875341180437418610146847128, -1433351360688815353494875341180437418610144749975⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1747811928632611860527852553430027575664998020387, 1747811928632611860527852553430027575664998020388⟩
def centerBExp : DyadicInterval precision := ⟨133675711440021382347438068467134266705245633950, 133675711440021382347438068467134268904268889503⟩
def centerBLog : DyadicInterval precision := ⟨127911346202546547993228768057240622865977035122, 127911346202546547993228768057240625065000290675⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨133675711440021382347438068467134267255001447838, scale precision, 133675711440021382347438068467134268354513075615, scale precision,
    3, 128, 3, 128, ⟨-3495623857265223721055705106860055157340580563898, -3495623857265223721055705106860055157340578466745⟩, ⟨-3495623857265223721055705106860055145319413614797, -3495623857265223721055705106860055145319411517644⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨710772219499800002539550232633061131065685412854, 722596977274384673613373174668084948310181321070⟩
def wholeCExp : DyadicInterval precision := ⟨543689262064988857606302969742362187437867251306, 552558621154368501616986397782311833873400096237⟩
def wholeCLog : DyadicInterval precision := ⟨462236199455743056572890960549513371724412520964, 468686457657077742530140922151493329240543147711⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨543689262064988857606302969742362187987623065194, scale precision, 552558621154368501616986397782311833323644282349, scale precision,
    1, 128, 1, 128, ⟨-1445193954548769347226746349336169898098172943518, -1445193954548769347226746349336169898098170846365⟩, ⟨-1421544438999600005079100465266122260677283581442, -1421544438999600005079100465266122260677281484289⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1730480979171308863079045827616715137963238279928, 1765203152691508352831245859955899508737045922867⟩
def wholeBExp : DyadicInterval precision := ⟨130531905858678251166493618444926377078696669308, 136883943166681602440876159476332482826945681740⟩
def wholeBLog : DyadicInterval precision := ⟨125028149168863384198381073365448124615255370198, 130847776517299761396889421162079515599887534026⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨130531905858678251166493618444926377628452483196, scale precision, 136883943166681602440876159476332482277189867852, scale precision,
    3, 128, 3, 128, ⟨-3530406305383016705662491719911799023629438722170, -3530406305383016705662491719911799023629436625017⟩, ⟨-3460961958342617726158091655233430270056767812363, -3460961958342617726158091655233430270056765715210⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0293StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0294StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0294StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨727736635393444038393719207565242720963944923840, 727736635393444038393719207565242720963944923841⟩
def centerCExp : DyadicInterval precision := ⟨539878697805529799133214523449570409287280928399, 539878697805529799133214523449570411486304183952⟩
def centerCLog : DyadicInterval precision := ⟨459456192683096047181784175530187905225486011150, 459456192683096047181784175530187907424509266703⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨539878697805529799133214523449570409837036742287, scale precision, 539878697805529799133214523449570410936548370064, scale precision,
    1, 128, 1, 128, ⟨-1455473270786888076787438415130485443416130801620, -1455473270786888076787438415130485443416128704467⟩, ⟨-1455473270786888076787438415130485440439650990892, -1455473270786888076787438415130485440439648893739⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1781458304626912455847038189098290290872769673452, 1781458304626912455847038189098290290872769673453⟩
def centerBExp : DyadicInterval precision := ⟨127660351551645330359711560386803505147820010010, 127660351551645330359711560386803507346843265563⟩
def centerBLog : DyadicInterval precision := ⟨122389655295126535644447548042966167361751753881, 122389655295126535644447548042966169560775009434⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨127660351551645330359711560386803505697575823898, scale precision, 127660351551645330359711560386803506797087451675, scale precision,
    3, 128, 3, 128, ⟨-3562916609253824911694076378196580588039342757487, -3562916609253824911694076378196580588039340660334⟩, ⟨-3562916609253824911694076378196580575451738033476, -3562916609253824911694076378196580575451735936323⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨721799793880790238599180403384320635387653893052, 733691558810144535508643671577973607618470891238⟩
def wholeCExp : DyadicInterval precision := ⟨535497077706014000362915783751168364483046962779, 544282701767069878325066184209694170952034378076⟩
def wholeCLog : DyadicInterval precision := ⟨456253020881404967805689861019607355922069208158, 462668669391859070938846506962361449490987161410⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨535497077706014000362915783751168365032802776667, scale precision, 544282701767069878325066184209694170402278564188, scale precision,
    1, 128, 1, 128, ⟨-1467383117620289071017287343155947216737360023936, -1467383117620289071017287343155947216737357926783⟩, ⟨-1443599587761580477198360806768641269299110859765, -1443599587761580477198360806768641269299108762612⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1764012116478371536855969007624414316243485743847, 1798962211054799313084703346404843068542030143122⟩
def wholeBExp : DyadicInterval precision := ⟨124638795227910776338896143190235848655945441612, 130744830687524242027442283757869983741586044540⟩
def wholeBLog : DyadicInterval precision := ⟨119608181116469210579996659459870329413254417285, 125223603077034334853974993226795972044084231542⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨124638795227910776338896143190235849205701255500, scale precision, 130744830687524242027442283757869983191830230652, scale precision,
    3, 128, 3, 128, ⟨-3597924422109598626169406692809686143530441217276, -3597924422109598626169406692809686143530439120123⟩, ⟨-3528024232956743073711938015248828626341651012624, -3528024232956743073711938015248828626341648915471⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0294StableWitnesses

end


