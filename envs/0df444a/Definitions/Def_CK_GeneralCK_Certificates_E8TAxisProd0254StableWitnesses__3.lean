-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0254StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0254StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:03:55.11403+00:00
-- url     : https://prove2.me/theorems/24311045-6eb9-464f-82c6-6a4ec1cd02ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0254StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0255StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0254StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0255StableWitnesses, GeneralCK.Certificates.E8TAxisProd0256StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0254StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0255StableWitnesses, GeneralCK.Certificates.E8TAxisProd0256StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0254StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0255StableWitnesses, GeneralCK.Certificates.E8TAxisProd0256StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0254StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0255StableWitnesses, GeneralCK/Certificates/E8TAxisProd0256StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0254StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0254StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029348165, 864539270161105163740168296694370154034029348166⟩
def centerDExp : DyadicInterval precision := ⟨447705727508954974656542730347776284626226541037, 447705727508954974656542730347776286825249796590⟩
def centerDLog : DyadicInterval precision := ⟨390547930354595539952804600044570644160315185441, 390547930354595539952804600044570646359338440994⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨447705727508954974656542730347776285175982354925, scale precision, 447705727508954974656542730347776286275493982702, scale precision,
    1, 128, 1, 128, ⟨-1729078540322210327480336593388740309862696205336, -1729078540322210327480336593388740309862694108183⟩, ⟨-1729078540322210327480336593388740306273423284479, -1729078540322210327480336593388740306273421187326⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨868187467173751992471297993761205624547079597443, 868187467173751992471297993761205624547079597444⟩
def centerCExp : DyadicInterval precision := ⟨445476173540605023808902515754053534490280953934, 445476173540605023808902515754053536689304209487⟩
def centerCLog : DyadicInterval precision := ⟨388840205495359962813171749605002270967046709253, 388840205495359962813171749605002273166069964806⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨445476173540605023808902515754053535040036767822, scale precision, 445476173540605023808902515754053536139548395599, scale precision,
    1, 128, 1, 128, ⟨-1736374934347503984942595987522411250897778640706, -1736374934347503984942595987522411250897776543553⟩, ⟨-1736374934347503984942595987522411247290541846224, -1736374934347503984942595987522411247290539749071⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2203131368793057409381337232897591382076241343980, 2203131368793057409381337232897591382076241343981⟩
def centerBExp : DyadicInterval precision := ⟨71688647122122857685481489477492426074507252345, 71688647122122857685481489477492428273530507898⟩
def centerBLog : DyadicInterval precision := ⟨69985893944213292039486242118026945789440479554, 69985893944213292039486242118026947988463735107⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71688647122122857685481489477492426624263066233, scale precision, 71688647122122857685481489477492427723774694010, scale precision,
    4, 128, 4, 128, ⟨-4406262737586114818762674465795182775360241929577, -4406262737586114818762674465795182775360239832424⟩, ⟨-4406262737586114818762674465795182752944725543517, -4406262737586114818762674465795182752944723446364⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 870712988176454679833831807012927217752922944019⟩
def wholeDExp : DyadicInterval precision := ⟨443939237141351316813290285207320724478560656031, 451492192509468156215846209344698069605083336703⟩
def wholeDLog : DyadicInterval precision := ⟨387661827478115861734404726101104695617766958964, 393443605556601543377574216062392477640846281111⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725028316469919, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1741425976352909359667663614025854437315709536964, -1741425976352909359667663614025854437315707439811⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨861807572949673468660518328224844520744745706286, 874588186260648773346854413637122018667374633123⟩
def wholeCExp : DyadicInterval precision := ⟨441591242524962125809089712112610743009197672673, 449382475880140624509440467073035851256772417776⟩
def wholeCLog : DyadicInterval precision := ⟨385859769976505728721241860644683743051198353331, 391830920911933999407673320463696040714174560152⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨441591242524962125809089712112610743558953486561, scale precision, 449382475880140624509440467073035850707016603888, scale precision,
    1, 128, 1, 128, ⟨-1749176372521297546693708827274244039154236175856, -1749176372521297546693708827274244039154234078703⟩, ⟨-1723615145899346937321036656449689039701552198112, -1723615145899346937321036656449689039701550100959⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2184669309228439526573711343006089816796651285984, 2221622609040950356192009939625428230446663911099⟩
def wholeBExp : DyadicInterval precision := ⟨69897365324512522267441137724532175122948289701, 73522898653205352289959644070637236993190778655⟩
def wholeBLog : DyadicInterval precision := ⟨68277370332723297249157721280231308186241678484, 71733334780141387016435126963703620705571174561⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨69897365324512522267441137724532175672704103589, scale precision, 73522898653205352289959644070637236443434964767, scale precision,
    4, 128, 4, 128, ⟨-4443245218081900712384019879250856472388311813255, -4443245218081900712384019879250856472388309716102⟩, ⟨-4369338618456879053147422686012179622665156922735, -4369338618456879053147422686012179622665154825582⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0254StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0255StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0255StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133789484, 852249911794452062012049136358764955095133789485⟩
def centerDExp : DyadicInterval precision := ⟨455298659801689467951201474539649436055069582612, 455298659801689467951201474539649438254092838165⟩
def centerDLog : DyadicInterval precision := ⟨396348806111750593903736846609666706637987139797, 396348806111750593903736846609666708837010395350⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649436604825396500, scale precision, 455298659801689467951201474539649437704337024277, scale precision,
    1, 128, 1, 128, ⟨-1704499823588904124024098272717529911954976264684, -1704499823588904124024098272717529911954974167531⟩, ⟨-1704499823588904124024098272717529908425560990410, -1704499823588904124024098272717529908425558893257⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨855875257039306516750649986172085809067710375679, 855875257039306516750649986172085809067710375680⟩
def centerCExp : DyadicInterval precision := ⟨453045460626734306175798483878596417666924953774, 453045460626734306175798483878596419865948209327⟩
def centerCLog : DyadicInterval precision := ⟨394629800068450422281538453411446964861894757200, 394629800068450422281538453411446967060918012753⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨453045460626734306175798483878596418216680767662, scale precision, 453045460626734306175798483878596419316192395439, scale precision,
    1, 128, 1, 128, ⟨-1711750514078613033501299972344171619908906123162, -1711750514078613033501299972344171619908904026009⟩, ⟨-1711750514078613033501299972344171616361937476710, -1711750514078613033501299972344171616361935379557⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2166867103203941085474100972296809250865164340740, 2166867103203941085474100972296809250865164340741⟩
def centerBExp : DyadicInterval precision := ⟨75336024341140457577394441299435936672368069171, 75336024341140457577394441299435938871391324724⟩
def centerBLog : DyadicInterval precision := ⟨73458598674692166126028333147290260256302865556, 73458598674692166126028333147290262455326121109⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75336024341140457577394441299435937222123883059, scale precision, 75336024341140457577394441299435938321635510836, scale precision,
    4, 128, 4, 128, ⟨-4333734206407882170948201944593618512395466749924, -4333734206407882170948201944593618512395464652771⟩, ⟨-4333734206407882170948201944593618491065192710192, -4333734206407882170948201944593618491065190613039⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771969770, 858384943750592238779991986336301839154815993317⟩
def wholeDExp : DyadicInterval precision := ⟨451492192509468156215846209344698067406060081150, 459125158042315647897421247370792079661750447941⟩
def wholeDLog : DyadicInterval precision := ⟨393443605556601543377574216062392475441823025558, 399263485746125009998379766489542017105011910291⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨451492192509468156215846209344698067955815895038, scale precision, 459125158042315647897421247370792079111994634053, scale precision,
    1, 128, 1, 128, ⟨-1716769887501184477559983972672603680089218674697, -1716769887501184477559983972672603680089216577544⟩, ⟨-1692268151626862819173455653290755287573544997795, -1692268151626862819173455653290755287573542900642⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨849535308550269335127518736936914542954195773108, 862235822613332734442002484759373418279860428952⟩
def wholeCExp : DyadicInterval precision := ⟨449119196648549881059977620731960640956244134315, 456993154976262153579828161561724319357018168113⟩
def wholeCLog : DyadicInterval precision := ⟨391629543164700278112090303032403185425246903824, 397640236145411121068347138321692515485013749910⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨449119196648549881059977620731960641505999948203, scale precision, 456993154976262153579828161561724318807262354225, scale precision,
    1, 128, 1, 128, ⟨-1724471645226665468884004969518746838348710282228, -1724471645226665468884004969518746838348708185075⟩, ⟨-1699070617100538670255037473873829084150228356705, -1699070617100538670255037473873829084150226259552⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2148465443011358342897619745438093480966248919969, 2185299997858007781513684444410996213977655824581⟩
def wholeBExp : DyadicInterval precision := ⟨73459470668620058807616494005055840094691857664, 77257213108321294368199001276717770130090946066⟩
def wholeBLog : DyadicInterval precision := ⟨71672943550938824621250011126147638676202444810, 75284469450002712924610561751099272626256866609⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73459470668620058807616494005055840644447671552, scale precision, 77257213108321294368199001276717769580335132178, scale precision,
    4, 128, 4, 128, ⟨-4370599995716015563027368888821992438892895215241, -4370599995716015563027368888821992438892893118088⟩, ⟨-4296930886022716685795239490876186951532576476048, -4296930886022716685795239490876186951532574378895⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0255StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0256StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0256StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808718837, 840037336037815392922282998599371946229808718838⟩
def centerDExp : DyadicInterval precision := ⟨462971716911096059979186904937436744746229273838, 462971716911096059979186904937436746945252529391⟩
def centerDLog : DyadicInterval precision := ⟨402187598898660414610829051743418455419293862475, 402187598898660414610829051743418457618317118028⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745295985087726, scale precision, 462971716911096059979186904937436746395496715503, scale precision,
    1, 128, 1, 128, ⟨-1680074672075630785844565997198743894195078759054, -1680074672075630785844565997198743894195076661901⟩, ⟨-1680074672075630785844565997198743890724158213450, -1680074672075630785844565997198743890724156116297⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨844913203376789313510511418311850372625725892347, 844913203376789313510511418311850372625725892348⟩
def centerCExp : DyadicInterval precision := ⟨459892863997781123379801432673434727425278020426, 459892863997781123379801432673434729624301275979⟩
def centerCLog : DyadicInterval precision := ⟨399847555140429255800262523835246290099146418153, 399847555140429255800262523835246292298169673706⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨459892863997781123379801432673434727975033834314, scale precision, 459892863997781123379801432673434729074545462091, scale precision,
    1, 128, 1, 128, ⟨-1689826406753578627021022836623700746998531522743, -1689826406753578627021022836623700746998529425590⟩, ⟨-1689826406753578627021022836623700743504374143801, -1689826406753578627021022836623700743504372046648⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2132606193836235069215919146921213839663038214742, 2132606193836235069215919146921213839663038214743⟩
def centerBExp : DyadicInterval precision := ⟨78952228122644369235712461171610604537139637451, 78952228122644369235712461171610606736162893004⟩
def centerBLog : DyadicInterval precision := ⟨76893495975624785466662709658361204755721185235, 76893495975624785466662709658361206954744440788⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨78952228122644369235712461171610605086895451339, scale precision, 78952228122644369235712461171610606186407079116, scale precision,
    4, 128, 4, 128, ⟨-4265212387672470138431838293842427689502725322401, -4265212387672470138431838293842427689502723225248⟩, ⟨-4265212387672470138431838293842427669149429633719, -4265212387672470138431838293842427669149427536566⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871334898, 846134075813431409586727826645377644661771969771⟩
def wholeDExp : DyadicInterval precision := ⟨459125158042315647897421247370792077462727192388, 466838367135635595432846250236128804162502981146⟩
def wholeDLog : DyadicInterval precision := ⟨399263485746125009998379766489542014905988654738, 405121100734994108525530084726425877554191840093⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078012483006276, scale precision, 466838367135635595432846250236128803612747167258, scale precision,
    1, 128, 1, 128, ⟨-1692268151626862819173455653290755291073544978437, -1692268151626862819173455653290755291073542881284⟩, ⟨-1667919182890941556768167636068781992468657623715, -1667919182890941556768167636068781992468655526562⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨838608684733141678699255504151558673118099039611, 851238148224410957186621235667228583458897172910⟩
def wholeCExp : DyadicInterval precision := ⟨455929481736318270254142181283128819882679561574, 463877733175818555576760837722347698540365029791⟩
def wholeCLog : DyadicInterval precision := ⟨396829709426426598151300715516752587192216148140, 402875492370674838486182557565795319132105906450⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨455929481736318270254142181283128820432435375462, scale precision, 463877733175818555576760837722347697990609215903, scale precision,
    1, 128, 1, 128, ⟨-1702476296448821914373242471334457168680061390162, -1702476296448821914373242471334457168680059293009⟩, ⟨-1677217369466283357398511008303117344504128444800, -1677217369466283357398511008303117344504126347647⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2114265616623986542815076664703363534760788967967, 2150980026509145184506690252160800632897242284898⟩
def wholeBExp : DyadicInterval precision := ⟨76991820527235262831579080159734392792823686769, 80958868272004706273830445183742190735891018368⟩
def wholeBLog : DyadicInterval precision := ⟨75032379823352000834320002435445158302981900842, 78796051755644624878188154591487660741488669888⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨76991820527235262831579080159734393342579500657, scale precision, 80958868272004706273830445183742190186135204480, scale precision,
    4, 128, 4, 128, ⟨-4301960053018290369013380504321601276230256803260, -4301960053018290369013380504321601276230254706107⟩, ⟨-4228531233247973085630153329406727059597168734216, -4228531233247973085630153329406727059597166637063⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0256StableWitnesses

end


