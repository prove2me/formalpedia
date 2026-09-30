-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0190StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0190StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:24:05.706508+00:00
-- url     : https://prove2.me/theorems/b8c44e17-7bfd-41da-a697-a7a8e72ea430
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0190StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0191StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0190StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0191StableWitnesses, GeneralCK.Certificates.E8TAxisProd0192StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0190StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0191StableWitnesses, GeneralCK.Certificates.E8TAxisProd0192StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0190StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0191StableWitnesses, GeneralCK.Certificates.E8TAxisProd0192StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0190StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0191StableWitnesses, GeneralCK/Certificates/E8TAxisProd0192StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0190StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0190StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705871997, 347578074592523924908318039364714024927705871998⟩
def centerDExp : DyadicInterval precision := ⟨908299859688922494739995341064431377288246704711, 908299859688922494739995341064431379487269960264⟩
def centerDLog : DyadicInterval precision := ⟨706404787120776184926021840452869055161422984619, 706404787120776184926021840452869057360446240172⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨908299859688922494739995341064431377838002518599, scale precision, 908299859688922494739995341064431378937514146376, scale precision,
    0, 128, 0, 128, ⟨-695156149185047849816636078729428050739998442960, -695156149185047849816636078729428050739996345807⟩, ⟨-695156149185047849816636078729428048970827142184, -695156149185047849816636078729428048970825045031⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨349263660896782262280251526995244170364612413276, 349263660896782262280251526995244170364612413277⟩
def centerCExp : DyadicInterval precision := ⟨906207144415209230296427843306651058886023961183, 906207144415209230296427843306651061085047216736⟩
def centerCLog : DyadicInterval precision := ⟨705113599632849654853580906211829501684946423492, 705113599632849654853580906211829503883969679045⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨906207144415209230296427843306651059435779775071, scale precision, 906207144415209230296427843306651060535291402848, scale precision,
    0, 128, 0, 128, ⟨-698527321793564524560503053990488341615854310009, -698527321793564524560503053990488341615852212856⟩, ⟨-698527321793564524560503053990488339842597440249, -698527321793564524560503053990488339842595343096⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨742733657755456941780777835616417680686296877252, 742733657755456941780777835616417680686296877253⟩
def centerBExp : DyadicInterval precision := ⟨528911818059097944294841239816970365125508949832, 528911818059097944294841239816970367324532205385⟩
def centerBLog : DyadicInterval precision := ⟨451425641069635609636093494147936927627624629031, 451425641069635609636093494147936929826647884584⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨528911818059097944294841239816970365675264763720, scale precision, 528911818059097944294841239816970366774776391497, scale precision,
    1, 128, 1, 128, ⟨-1485467315510913883561555671232835362891693062370, -1485467315510913883561555671232835362891690965217⟩, ⟨-1485467315510913883561555671232835359853496543795, -1485467315510913883561555671232835359853494446642⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773909588, 356015818146773315735630103594046256346147492781⟩
def wholeDExp : DyadicInterval precision := ⟨897872332234039104779267097055247454328309327909, 918817951079152880960489128094785338008821185250⟩
def wholeDLog : DyadicInterval precision := ⟨699959742628865241142888209739517589777680401458, 712877141250487397629906767735900639146197088161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨897872332234039104779267097055247454878065141797, scale precision, 918817951079152880960489128094785337459065371362, scale precision,
    0, 128, 0, 128, ⟨-712031636293546631471260207188092513587154905811, -712031636293546631471260207188092513587152808658⟩, ⟨-678329234677107700847743398667782514541089437367, -678329234677107700847743398667782514541087340214⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨340509163550737734786805570700132916350028968076, 358044558190719898392359023693497830097627184929⟩
def wholeCExp : DyadicInterval precision := ⟨895383079650601657819313742220858027019097543024, 917128924766610565047671978136442514717495490655⟩
def wholeCLog : DyadicInterval precision := ⟨698416974385628154897256113035766030285986852686, 711839721337752540520369736804890277504775145542⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨895383079650601657819313742220858027568853356912, scale precision, 917128924766610565047671978136442514167739676767, scale precision,
    0, 128, 0, 128, ⟨-716089116381439796784718047386995661092602085342, -716089116381439796784718047386995661092599988189⟩, ⟨-681018327101475469573611141400265831823989110109, -681018327101475469573611141400265831823987012956⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨722297995453501352472186853324671799545652829220, 763385715419221596005381651623863469753986400929⟩
def wholeBExp : DyadicInterval precision := ⟨514173264887947852703415841781641101390832360166, 543911754410846392617316740313260673730370230743⟩
def wholeBLog : DyadicInterval precision := ⟨440563291668490213331945155930551125283857388866, 462398356030908803359795823026737880545756222586⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨514173264887947852703415841781641101940588174054, scale precision, 543911754410846392617316740313260673180614416855, scale precision,
    1, 128, 1, 128, ⟨-1526771430838443192010763303247726941070616401104, -1526771430838443192010763303247726941070614303951⟩, ⟨-1444595990907002704944373706649343597614101966333, -1444595990907002704944373706649343597614099869180⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0190StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0191StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0191StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨330774838385704024446645164332729497941801346231, 330774838385704024446645164332729497941801346232⟩
def centerDExp : DyadicInterval precision := ⟨929427725267003858605636529731753968326593265085, 929427725267003858605636529731753970525616520638⟩
def centerDLog : DyadicInterval precision := ⟨719377002425149550154397054915826075326505911594, 719377002425149550154397054915826077525529167147⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨929427725267003858605636529731753968876349078973, scale precision, 929427725267003858605636529731753969975860706750, scale precision,
    0, 128, 0, 128, ⟨-661549676771408048893290328665458996748080881422, -661549676771408048893290328665458996748078784269⟩, ⟨-661549676771408048893290328665458995019126600658, -661549676771408048893290328665458995019124503505⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨332450929007255858832737068653628197487143760378, 332450929007255858832737068653628197487143760379⟩
def centerCExp : DyadicInterval precision := ⟨927298381193753131857339534910833218631775273415, 927298381193753131857339534910833220830798528968⟩
def centerCLog : DyadicInterval precision := ⟨718074819892529487010729337025025285124606728998, 718074819892529487010729337025025287323629984551⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨927298381193753131857339534910833219181531087303, scale precision, 927298381193753131857339534910833220281042715080, scale precision,
    0, 128, 0, 128, ⟨-664901858014511717665474137307256395840750798131, -664901858014511717665474137307256395840748700978⟩, ⟨-664901858014511717665474137307256394107826340534, -664901858014511717665474137307256394107824243381⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨702862672520444937412890224784031278630497834487, 702862672520444937412890224784031278630497834488⟩
def centerBExp : DyadicInterval precision := ⟨558571925025681024356898890478455319289142097775, 558571925025681024356898890478455321488165353328⟩
def centerBLog : DyadicInterval precision := ⟨473043506953427368145099411052005752643000895846, 473043506953427368145099411052005754842024151399⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨558571925025681024356898890478455319838897911663, scale precision, 558571925025681024356898890478455320938409539440, scale precision,
    1, 128, 1, 128, ⟨-1405725345040889874825780449568062558699431028573, -1405725345040889874825780449568062558699428931420⟩, ⟨-1405725345040889874825780449568062555822562406530, -1405725345040889874825780449568062555822560309377⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 339164617338553850423871699333891257707773909589⟩
def wholeDExp : DyadicInterval precision := ⟨918817951079152880960489128094785335809797929697, 940130328208408204655831711119657711878645153902⟩
def wholeDLog : DyadicInterval precision := ⟨712877141250487397629906767735900636947173832608, 725904575743015811666185701912516251881166002297⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨918817951079152880960489128094785336359553743585, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-678329234677107700847743398667782516290008298142, -678329234677107700847743398667782516290006200989⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨323745279710826766446985521470106618369709766890, 341181664743207029901761625605753194818793566139⟩
def wholeCExp : DyadicInterval precision := ⟨916285290296825158783368498693788598941704995641, 938411625610146292314081985138210584633840883331⟩
def wholeCLog : DyadicInterval precision := ⟨711321275186003626837213087546784675085785460207, 724858293078083165410598662537004366869231215761⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨916285290296825158783368498693788599491460809529, scale precision, 938411625610146292314081985138210584084085069443, scale precision,
    0, 128, 0, 128, ⟨-682363329486414059803523251211506390514464663146, -682363329486414059803523251211506390514462565993⟩, ⟨-647490559421653532893971042940213235883219529213, -647490559421653532893971042940213235883217432060⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨682835956741538807505496934441851184518523283903, 723095381825490724288119292239514973318635896595⟩
def wholeBExp : DyadicInterval precision := ⟨543318568242366388450850122152057331600224720484, 574091655821216878552110089211839166246414848729⟩
def wholeBLog : DyadicInterval precision := ⟨461965990912139238006126035442713466679111057356, 484228953634616374141842731273179492967179431451⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨543318568242366388450850122152057332149980534372, scale precision, 574091655821216878552110089211839165696659034841, scale precision,
    1, 128, 1, 128, ⟨-1446190763650981448576238584479029948116090369997, -1446190763650981448576238584479029948116088272844⟩, ⟨-1365671913483077615010993868883702367637499279487, -1365671913483077615010993868883702367637497182334⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0191StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0192StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0192StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨381480886315733598228818968652248949197699359262, 381480886315733598228818968652248949197699359263⟩
def centerDExp : DyadicInterval precision := ⟨867122341474961541277039570779760212192757729340, 867122341474961541277039570779760214391780984893⟩
def centerDLog : DyadicInterval precision := ⟨680786608648623470121619561851525432077092876199, 680786608648623470121619561851525434276116131752⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨867122341474961541277039570779760212742513543228, scale precision, 867122341474961541277039570779760213842025171005, scale precision,
    0, 128, 0, 128, ⟨-762961772631467196457637937304497899321992225512, -762961772631467196457637937304497899321990128359⟩, ⟨-762961772631467196457637937304497897468807308690, -762961772631467196457637937304497897468805211537⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨382504384572763969889234619601422084370115959514, 382504384572763969889234619601422084370115959515⟩
def centerCExp : DyadicInterval precision := ⟨865908689772774920062892187001742574564524914206, 865908689772774920062892187001742576763548169759⟩
def centerCLog : DyadicInterval precision := ⟨680024692445464781763770535914774158800720003146, 680024692445464781763770535914774160999743258699⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨865908689772774920062892187001742575114280728094, scale precision, 865908689772774920062892187001742576213792355871, scale precision,
    0, 128, 0, 128, ⟨-765008769145527939778469239202844169668124131674, -765008769145527939778469239202844169668122034521⟩, ⟨-765008769145527939778469239202844167812341803537, -765008769145527939778469239202844167812339706384⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨824169445381042335862458807073655917183717986360, 824169445381042335862458807073655917183717986361⟩
def centerBExp : DyadicInterval precision := ⟨473134862008812799968096038460868121791864547623, 473134862008812799968096038460868123990887803176⟩
def centerBLog : DyadicInterval precision := ⟨409885481624720367681055066110788750670253175713, 409885481624720367681055066110788752869276431266⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨473134862008812799968096038460868122341620361511, scale precision, 473134862008812799968096038460868123441131989288, scale precision,
    1, 128, 1, 128, ⟨-1648338890762084671724917614147311836065618843536, -1648338890762084671724917614147311836065616746383⟩, ⟨-1648338890762084671724917614147311832669255199061, -1648338890762084671724917614147311832669253101908⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨372966609392870424646531471060848444542040850580, 390021907983024779256146395473341757167804190698⟩
def wholeDExp : DyadicInterval precision := ⟨857046406820575460675375243512252169980002923132, 877284626339432933560204346302551152435952374342⟩
def wholeDLog : DyadicInterval precision := ⟨674448983099953378325059509857368474307670227252, 687150831490084437187371430673459277974101520863⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨857046406820575460675375243512252170529758737020, scale precision, 877284626339432933560204346302551151886196560454, scale precision,
    0, 128, 0, 128, ⟨-780043815966049558512292790946683515273095446757, -780043815966049558512292790946683515273093349604⟩, ⟨-745933218785740849293062942121696888168223747987, -745933218785740849293062942121696888168221650834⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨373646781925249351030950326683961254976679459701, 391390994830230264090034133324584929749196342429⟩
def wholeCExp : DyadicInterval precision := ⟨855442204069468392391412930235862394581513556601, 876468442115516198200232507263586161552531696456⟩
def wholeCLog : DyadicInterval precision := ⟨673437420530613622463329923875635176971565091256, 686640711011610567336990065024320226897240716090⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨855442204069468392391412930235862395131269370489, scale precision, 876468442115516198200232507263586161002775882568, scale precision,
    0, 128, 0, 128, ⟨-782781989660460528180068266649169860437637808962, -782781989660460528180068266649169860437635711809⟩, ⟨-747293563850498702061900653367922509036648100762, -747293563850498702061900653367922509036646003609⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨802865233561216913142342731263416338063221001901, 845709337934757964588152352207057543087871465215⟩
def wholeBExp : DyadicInterval precision := ⟨459392095176499336902797022465146369192015980987, 487131610930505629454859937688780158229176043405⟩
def wholeBLog : DyadicInterval precision := ⟨399466597538172117851805770482198019101779944168, 420421118540265489243162511406115270658610952681⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨459392095176499336902797022465146369741771794875, scale precision, 487131610930505629454859937688780157679420229517, scale precision,
    1, 128, 1, 128, ⟨-1691418675869515929176304704414115087924727103807, -1691418675869515929176304704414115087924725006654⟩, ⟨-1605730467122433826284685462526832674477055075698, -1605730467122433826284685462526832674477052978545⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0192StableWitnesses

end


