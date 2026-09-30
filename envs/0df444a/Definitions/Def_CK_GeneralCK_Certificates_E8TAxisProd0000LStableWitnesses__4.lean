-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LStableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0000LStableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:32:50.701283+00:00
-- url     : https://prove2.me/theorems/6f6d888b-a534-4a4e-b7b3-57a9b720c5b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0000LStableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0023LStableWitnesses, GeneralCK/Certificates/E8TAxisProd0024LStableWitnesses, GeneralCK/Certificates/E8TAxisProd0028LStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨22953787393551632719727143497985289631556801416, 22953787393551632719727143497985289631556801417⟩
def centerDExp : DyadicInterval precision := ⟨1416307579080234976617203231554007855493109330315, 1416307579080234976617203231554007857692132585868⟩
def centerDLog : DyadicInterval precision := ⟨990262196212108070669138906538977259922532503432, 990262196212108070669138906538977262121555758985⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1416307579080234976617203231554007856042865144203, scale precision, 1416307579080234976617203231554007857142376771980, scale precision,
    0, 128, 0, 128, ⟨-45907574787103265439454286995970579830413050428, -45907574787103265439454286995970579830410953275⟩, ⟨-45907574787103265439454286995970578695816252391, -45907574787103265439454286995970578695814155238⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨26753952616998906953143333910970666895507355234, 26753952616998906953143333910970666895507355235⟩
def centerCExp : DyadicInterval precision := ⟨1408961391830249812414692104779201205994941538031, 1408961391830249812414692104779201208193964793584⟩
def centerCLog : DyadicInterval precision := ⟨986526649223242389614411570668033815807664199946, 986526649223242389614411570668033818006687455499⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1408961391830249812414692104779201206544697351919, scale precision, 1408961391830249812414692104779201207644208979696, scale precision,
    0, 128, 0, 128, ⟨-53507905233997813906286667821941334361271996575, -53507905233997813906286667821941334361269899422⟩, ⟨-53507905233997813906286667821941333220759521515, -53507905233997813906286667821941333220757424362⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨49724376405738921362341935939808058827278463596, 49724376405738921362341935939808058827278463597⟩
def centerBExp : DyadicInterval precision := ⟨1365360952751993252517509967629037027202278830327, 1365360952751993252517509967629037029401302085880⟩
def centerBLog : DyadicInterval precision := ⟨964157080983777303704197953080412960833580905834, 964157080983777303704197953080412963032604161387⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1365360952751993252517509967629037027752034644215, scale precision, 1365360952751993252517509967629037028851546271992, scale precision,
    0, 128, 0, 128, ⟨-99448752811477842724683871879616118243024359337, -99448752811477842724683871879616118243022262184⟩, ⟨-99448752811477842724683871879616117066091592202, -99448752811477842724683871879616117066089495049⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989432986973, 23745456717760790936231587082098894243338759236⟩
def wholeDExp : DyadicInterval precision := ⟨1414774032904110256356769903186423881438634712406, 1417842757137037989742285799922994929667109837448⟩
def wholeDLog : DyadicInterval precision := ⟨989483173884649444583154341512750139258805608841, 991041631832012714857158240438297380855618410517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1414774032904110256356769903186423881988390526294, scale precision, 1417842757137037989742285799922994929117354023560, scale precision,
    0, 128, 0, 128, ⟨-47490913435521581872463174164197789054591889912, -47490913435521581872463174164197789054589792759⟩, ⟨-44324267483763059541032859816138423412182869373, -44324267483763059541032859816138423412180772220⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨24695481355850246866248295865805301976344615011, 28812547370402185580586103553553495740636253294⟩
def wholeCExp : DyadicInterval precision := ⟨1404997798737333350196092251917829438352842279626, 1412935927708083132512800521363519722924860511439⟩
def wholeCLog : DyadicInterval precision := ⟨984507183782496558074853044541072122246545207630, 988548891914689170103698086859276757451192383982⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1404997798737333350196092251917829438902598093514, scale precision, 1412935927708083132512800521363519722375104697551, scale precision,
    0, 128, 0, 128, ⟨-57625094740804371161172207107106992053138523815, -57625094740804371161172207107106992053136426662⟩, ⟨-49390962711700493732496591731610603384038150521, -49390962711700493732496591731610603384036053368⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨46871591652396955948239255283142047275791395945, 52577601371879322502513854285499030441883455173⟩
def wholeBExp : DyadicInterval precision := ⟨1360040279301955759027850686834924112987074957563, 1370701615716012189539119176421333098610924879644⟩
def wholeBLog : DyadicInterval precision := ⟨961403675044213210016109363187450489822866094140, 966915624602095365704810787008635854487439275214⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1360040279301955759027850686834924113536830771451, scale precision, 1370701615716012189539119176421333098061169065756, scale precision,
    0, 128, 0, 128, ⟨-105155202743758645005027708570998061474536507734, -105155202743758645005027708570998061474534410581⟩, ⟨-93743183304793911896478510566284093965410297723, -93743183304793911896478510566284093965408200570⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0000LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨30000258078203469979793125548293523128589031944, 30000258078203469979793125548293523128589031945⟩
def centerCExp : DyadicInterval precision := ⟨1402716069448503871625639627514803058156352973220, 1402716069448503871625639627514803060355376228773⟩
def centerCLog : DyadicInterval precision := ⟨983343367392797031655131223867114583290938123565, 983343367392797031655131223867114585489961379118⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1402716069448503871625639627514803058706108787108, scale precision, 1402716069448503871625639627514803059805620414885, scale precision,
    0, 128, 0, 128, ⟨-60000516156406939959586251096587046829974305755, -60000516156406939959586251096587046829972208602⟩, ⟨-60000516156406939959586251096587045684383919176, -60000516156406939959586251096587045684381822023⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨56541191515484745831666298834050522873763429555, 56541191515484745831666298834050522873763429556⟩
def centerBExp : DyadicInterval precision := ⟨1352683394996923325966594229879893106817370718457, 1352683394996923325966594229879893109016393974010⟩
def centerBLog : DyadicInterval precision := ⟨957587981110745282442808669418236076265123399202, 957587981110745282442808669418236078464146654755⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1352683394996923325966594229879893107367126532345, scale precision, 1352683394996923325966594229879893108466638160122, scale precision,
    0, 128, 0, 128, ⟨-113082383030969491663332597668101046341509489116, -113082383030969491663332597668101046341507391963⟩, ⟨-113082383030969491663332597668101045153546326262, -113082383030969491663332597668101045153544229109⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨28495832066569625071725925768742554179975452124, 31504758042925872545671731216196284729899073540⟩
def wholeCExp : DyadicInterval precision := ⟨1399831070570501640493024625187727560374204840927, 1405606871950498835032546928453693495128825057280⟩
def wholeCLog : DyadicInterval precision := ⟨981870520020801992942599944432199780880590508092, 984817690364086630685032594349947518367968360197⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1399831070570501640493024625187727560923960654815, scale precision, 1405606871950498835032546928453693494579069243392, scale precision,
    0, 128, 0, 128, ⟨-63009516085851745091343462432392570033774898168, -63009516085851745091343462432392570033772801015⟩, ⟨-56991664133139250143451851537485107788334782930, -56991664133139250143451851537485107788332685777⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 59236980323012821373995552116184975561081649329⟩
def wholeBExp : DyadicInterval precision := ⟨1347702448352258315839178145014715609212891416307, 1357681920934804568838490939788917163911062976792⟩
def wholeBLog : DyadicInterval precision := ⟨954998914827886117763014829058236090679685739835, 960181582307675404146178190201383839808765855727⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1347702448352258315839178145014715609762647230195, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-118473960646025642747991104232369951718341213361, -118473960646025642747991104232369951718339116208⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0023LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨29366806747521364469519614331072697578537260361, 29366806747521364469519614331072697578537260362⟩
def centerCExp : DyadicInterval precision := ⟨1403932541014675339099439498285772630745508980264, 1403932541014675339099439498285772632944532235817⟩
def centerCLog : DyadicInterval precision := ⟨983963954907740132417277576840144886534809063830, 983963954907740132417277576840144888733832319383⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1403932541014675339099439498285772631295264794152, scale precision, 1403932541014675339099439498285772632394776421929, scale precision,
    0, 128, 0, 128, ⟨-58733613495042728939039228662145395729374450234, -58733613495042728939039228662145395729372353081⟩, ⟨-58733613495042728939039228662145394584776688365, -58733613495042728939039228662145394584774591212⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨55906953955441934614833995922022843761568683825, 55906953955441934614833995922022843761568683826⟩
def centerBExp : DyadicInterval precision := ⟨1353857933578876353992516595434652697394001293428, 1353857933578876353992516595434652699593024548981⟩
def centerBLog : DyadicInterval precision := ⟨958197831536143147344228658020216315302294402435, 958197831536143147344228658020216317501317657988⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1353857933578876353992516595434652697943757107316, scale precision, 1353857933578876353992516595434652699043268735093, scale precision,
    0, 128, 0, 128, ⟨-111813907910883869229667991844045688116604689315, -111813907910883869229667991844045688116602592162⟩, ⟨-111813907910883869229667991844045686929672143141, -111813907910883869229667991844045686929670045988⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨27862410764083842283213187030105662664219775911, 30871275121883886504471543380315675920526649137⟩
def wholeCExp : DyadicInterval precision := ⟨1401045100758393964311190852361738770284570851988, 1406825792685543838526339659362356366856670352668⟩
def wholeCLog : DyadicInterval precision := ⟨982490486653824970692824039413070255941518701095, 985438900223535865014739601324176538763086637898⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1401045100758393964311190852361738770834326665876, scale precision, 1406825792685543838526339659362356366306914538780, scale precision,
    0, 128, 0, 128, ⟨-61742550243767773008943086760631352414532689336, -61742550243767773008943086760631352414530592183⟩, ⟨-55724821528167684566426374060211324757318698662, -55724821528167684566426374060211324757316601509⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨53211713690413505970693577539315862056912531907, 58602635770181898821662589353151101542136562993⟩
def wholeBExp : DyadicInterval precision := ⟨1348872859460053731599279250908956038245338563934, 1358860610121550734019776036940863164366791355906⟩
def wholeBLog : DyadicInterval precision := ⟨955607699899585814401544643147774223090176566354, 960792502499039239104543795401092342082376600922⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1348872859460053731599279250908956038795094377822, scale precision, 1358860610121550734019776036940863163817035542018, scale precision,
    0, 128, 0, 128, ⟨-117205271540363797643325178706302203679933740618, -117205271540363797643325178706302203679931643465⟩, ⟨-106423427380827011941387155078631723522544699019, -106423427380827011941387155078631723522542601866⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0024LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨28733368250682422168576000032531891306167954754, 28733368250682422168576000032531891306167954755⟩
def centerCExp : DyadicInterval precision := ⟨1405150042858365334461169775082597944841000813908, 1405150042858365334461169775082597947040024069461⟩
def centerCLog : DyadicInterval precision := ⟨984584804283928516732402967116276041963514513531, 984584804283928516732402967116276044162537769084⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1405150042858365334461169775082597945390756627796, scale precision, 1405150042858365334461169775082597946490268255573, scale precision,
    0, 128, 0, 128, ⟨-57466736501364844337152000065063783184139966748, -57466736501364844337152000065063783184137869595⟩, ⟨-57466736501364844337152000065063782040533949421, -57466736501364844337152000065063782040531852268⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨55272740841022808192576745041062645791328064693, 55272740841022808192576745041062645791328064694⟩
def centerBExp : DyadicInterval precision := ⟨1355033446686202890835232612109240876317935548863, 1355033446686202890835232612109240878516958804416⟩
def centerBLog : DyadicInterval precision := ⟨958807933273222914244853948612332595557861696736, 958807933273222914244853948612332597756884952289⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1355033446686202890835232612109240876867691362751, scale precision, 1355033446686202890835232612109240877967202990528, scale precision,
    0, 128, 0, 128, ⟨-110545481682045616385153490082125292175608609602, -110545481682045616385153490082125292175606512449⟩, ⟨-110545481682045616385153490082125290989705746325, -110545481682045616385153490082125290989703649172⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨27229001637740082023660026865057311811959644989, 30237805692459661685740618735843772034829551822⟩
def wholeCExp : DyadicInterval precision := ⟨1402260157947636484963162216733466194370526655908, 1408045746988392385501324593993414679995757765003⟩
def wholeCLog : DyadicInterval precision := ⟨983110714532861567518714518882903788349475794336, 986060372561514944316941668173754766862795251004⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1402260157947636484963162216733466194920282469796, scale precision, 1408045746988392385501324593993414679446001951115, scale precision,
    0, 128, 0, 128, ⟨-60475611384919323371481237471687544642641576228, -60475611384919323371481237471687544642639479075⟩, ⟨-54458003275480164047320053730114623053293266354, -54458003275480164047320053730114623053291169201⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨52577601371879322502513854285499030441883455172, 57968316843561369459396042560216062604255734919⟩
def wholeBExp : DyadicInterval precision := ⟨1350044239666637883354013223985990278530419113026, 1360040279301955759027850686834924115186098213116⟩
def wholeBLog : DyadicInterval precision := ⟨956216735247228220778188764646695069534995848076, 961403675044213210016109363187450492021889349693⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1350044239666637883354013223985990279080174926914, scale precision, 1360040279301955759027850686834924114636342399228, scale precision,
    0, 128, 0, 128, ⟨-115936633687122738918792085120432125803655254128, -115936633687122738918792085120432125803653156975⟩, ⟨-105155202743758645005027708570998060292999410108, -105155202743758645005027708570998060292997312955⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0028LStableWitnesses

end


