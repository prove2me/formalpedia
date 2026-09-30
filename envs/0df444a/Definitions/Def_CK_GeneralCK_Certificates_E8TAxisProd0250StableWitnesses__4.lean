-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0250StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0250StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:02:47.840183+00:00
-- url     : https://prove2.me/theorems/74491f64-aac3-42cd-9212-6b115ee57489
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0250StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0251StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0250StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0251StableWitnesses, GeneralCK.Certificates.E8TAxisProd0252StableWitnesses, GeneralCK.Certificates.E8TAxisProd0253StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0250StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0251StableWitnesses, GeneralCK.Certificates.E8TAxisProd0252StableWitnesses, GeneralCK.Certificates.E8TAxisProd0253StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0250StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0251StableWitnesses, GeneralCK.Certificates.E8TAxisProd0252StableWitnesses, GeneralCK.Certificates.E8TAxisProd0253StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0250StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0251StableWitnesses, GeneralCK/Certificates/E8TAxisProd0252StableWitnesses, GeneralCK/Certificates/E8TAxisProd0253StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0250StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0250StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303356852, 889351442612263296687940979624415955523303356853⟩
def centerDExp : DyadicInterval precision := ⟨432759351678313928226043309926168445711221586154, 432759351678313928226043309926168447910244841707⟩
def centerDLog : DyadicInterval precision := ⟨379061432685197727184727484874290046165241739981, 379061432685197727184727484874290048364264995534⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446260977400042, scale precision, 432759351678313928226043309926168447360489027819, scale precision,
    1, 128, 1, 128, ⟨-1778702885224526593375881959248831912903226270963, -1778702885224526593375881959248831912903224173810⟩, ⟨-1778702885224526593375881959248831909189989253603, -1778702885224526593375881959248831909189987156450⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨893046018040782233721732459736325134195282197569, 893046018040782233721732459736325134195282197570⟩
def centerCExp : DyadicInterval precision := ⟨430576901770189226519690689688973811125250806794, 430576901770189226519690689688973813324274062347⟩
def centerCLog : DyadicInterval precision := ⟨377376610474364216696209328552409040679159465200, 377376610474364216696209328552409042878182720753⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨430576901770189226519690689688973811675006620682, scale precision, 430576901770189226519690689688973812774518248459, scale precision,
    1, 128, 1, 128, ⟨-1786092036081564467443464919472650270256594528941, -1786092036081564467443464919472650270256592431788⟩, ⟨-1786092036081564467443464919472650266524536358486, -1786092036081564467443464919472650266524534261333⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2275990641109448552795944099803773901056830134389, 2275990641109448552795944099803773901056830134390⟩
def centerBExp : DyadicInterval precision := ⟨64885729963508664258328331584823137141828859438, 64885729963508664258328331584823139340852114991⟩
def centerBLog : DyadicInterval precision := ⟨63486636803220555867099013564665525857156148576, 63486636803220555867099013564665528056179404129⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨64885729963508664258328331584823137691584673326, scale precision, 64885729963508664258328331584823138791096301103, scale precision,
    4, 128, 4, 128, ⟨-4551981282218897105591888199607547814496492219966, -4551981282218897105591888199607547814496490122813⟩, ⟨-4551981282218897105591888199607547789730830414756, -4551981282218897105591888199607547789730828317603⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 895603670620266646532188138393358736598408063638⟩
def wholeDExp : DyadicInterval precision := ⟨429072502312048699316189665111836193246265566837, 436466074505762269046786189274013978256547303798⟩
def wholeDLog : DyadicInterval precision := ⟨376214102269711135965559641860188009991436493933, 381918529993447746751868483809797876669420495502⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836193796021380725, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1791207341240533293064376276786717475069388868982, -1791207341240533293064376276786717475069386771829⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨886585047464279175601806592379370389555017033916, 899528210835903146169830462245263344204199023925⟩
def wholeCExp : DyadicInterval precision := ⟨426774320008511696372858309893774228517004348827, 434400748833354390208063835142766254640905149005⟩
def wholeCLog : DyadicInterval precision := ⟨374436419891522530780813199414713878447279939102, 380327290930404234323537283718330229399432666485⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨426774320008511696372858309893774229066760162715, scale precision, 434400748833354390208063835142766254091149335117, scale precision,
    1, 128, 1, 128, ⟨-1799056421671806292339660924490526690291054599488, -1799056421671806292339660924490526690291052502335⟩, ⟨-1773170094928558351203613184758740777260431900281, -1773170094928558351203613184758740777260429803128⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2257419612576293155721708466288320538842938650183, 2294586991976204353239957390600877754296614987374⟩
def wholeBExp : DyadicInterval precision := ⟨63255333175119429063028342118721824135501257904, 66555843620712577240901895515832004609585633739⟩
def wholeBLog : DyadicInterval precision := ⟨61924712791299042589820542376593227860670828413, 65084880810921778694385333622794010292179595482⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨63255333175119429063028342118721824685257071792, scale precision, 66555843620712577240901895515832004059829819851, scale precision,
    4, 128, 4, 128, ⟨-4589173983952408706479914781201755521295227547573, -4589173983952408706479914781201755521295225450420⟩, ⟨-4514839225152586311443416932576641065613775008032, -4514839225152586311443416932576641065613772910879⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0250StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0251StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0251StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103956064712, 876906193579724784222253173988686333103956064713⟩
def centerDExp : DyadicInterval precision := ⟨440192694720248252032582341812381160071591754974, 440192694720248252032582341812381162270615010527⟩
def centerDLog : DyadicInterval precision := ⟨384785344583078380142629370287541215891742295997, 384785344583078380142629370287541218090765551550⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨440192694720248252032582341812381160621347568862, scale precision, 440192694720248252032582341812381161720859196639, scale precision,
    1, 128, 1, 128, ⟨-1753812387159449568444506347977372668033179775489, -1753812387159449568444506347977372668033177678336⟩, ⟨-1753812387159449568444506347977372664382646580517, -1753812387159449568444506347977372664382644483364⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨880577469555873053778656908938965968543607052925, 880577469555873053778656908938965968543607052926⟩
def centerCExp : DyadicInterval precision := ⟨437986722360710935574566820054665617124737926399, 437986722360710935574566820054665619323761181952⟩
def centerCLog : DyadicInterval precision := ⟨383089013288969541127784959549373620675882355371, 383089013288969541127784959549373622874905610924⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨437986722360710935574566820054665617674493740287, scale precision, 437986722360710935574566820054665618774005368064, scale precision,
    1, 128, 1, 128, ⟨-1761154939111746107557313817877931938921674924803, -1761154939111746107557313817877931938921672827650⟩, ⟨-1761154939111746107557313817877931935252755384048, -1761154939111746107557313817877931935252753286895⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2239508420437104764284119736608677703687168065021, 2239508420437104764284119736608677703687168065022⟩
def centerBExp : DyadicInterval precision := ⟨68207328761407506747633934610097760025147334654, 68207328761407506747633934610097762224170590207⟩
def centerBLog : DyadicInterval precision := ⟨66663581155531875814581825487215598962721593403, 66663581155531875814581825487215601161744848956⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨68207328761407506747633934610097760574903148542, scale precision, 68207328761407506747633934610097761674414776319, scale precision,
    4, 128, 4, 128, ⟨-4479016840874209528568239473217355419154142028336, -4479016840874209528568239473217355419154139931183⟩, ⟨-4479016840874209528568239473217355395594532328892, -4479016840874209528568239473217355395594530231739⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922944018, 883118980747789020882084464779538700246874405267⟩
def wholeDExp : DyadicInterval precision := ⟨436466074505762269046786189274013976057524048245, 443939237141351316813290285207320726677583911584⟩
def wholeDLog : DyadicInterval precision := ⟨381918529993447746751868483809797874470397239949, 387661827478115861734404726101104697816790214517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013976607279862133, scale precision, 443939237141351316813290285207320726127828097696, scale precision,
    1, 128, 1, 128, ⟨-1766237961495578041764168929559077402334600887543, -1766237961495578041764168929559077402334598790390⟩, ⟨-1741425976352909359667663614025854433695984336263, -1741425976352909359667663614025854433695982239110⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨874157230747478651127939648387624030242740227483, 887018735049816900191077495365469056175113535617⟩
def wholeCExp : DyadicInterval precision := ⟨434143016219362010869024635375220972842952937453, 441851744877633692763545673461665836644728150682⟩
def wholeCLog : DyadicInterval precision := ⟨380128598083406369020701180328906594212166395641, 386059812004865249943512807625478915790236266593⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨434143016219362010869024635375220973392708751341, scale precision, 441851744877633692763545673461665836094972336794, scale precision,
    1, 128, 1, 128, ⟨-1774037470099633800382154990730938114200929368276, -1774037470099633800382154990730938114200927271123⟩, ⟨-1748314461494957302255879296775248058667068356047, -1748314461494957302255879296775248058667066258894⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2220989959146203942278856072072081120998919885509, 2258054091262509235013941793937008873212629311584⟩
def wholeBExp : DyadicInterval precision := ⟨66498081198861217224540281200084955586465623501, 69957905398170965726667630033981374456483478197⟩
def wholeBLog : DyadicInterval precision := ⟨65029633236277992481662786342700939523412121104, 68335146044840857138755599865071699364771357263⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66498081198861217224540281200084956136221437389, scale precision, 69957905398170965726667630033981373906727664309, scale precision,
    4, 128, 4, 128, ⟨-4516108182525018470027883587874017758507849238906, -4516108182525018470027883587874017758507847141753⟩, ⟨-4441979918292407884557712144144162230512805389255, -4441979918292407884557712144144162230512803292102⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0251StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0252StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0252StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨868617113497772692368686748854564557162355644130, 868617113497772692368686748854564557162355644131⟩
def centerCExp : DyadicInterval precision := ⟨445214331965657657362702094119717760560385153407, 445214331965657657362702094119717762759408408960⟩
def centerCLog : DyadicInterval precision := ⟨388639517179429506035483654145622592099728453893, 388639517179429506035483654145622594298751709446⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨445214331965657657362702094119717761110140967295, scale precision, 445214331965657657362702094119717762209652595072, scale precision,
    1, 128, 1, 128, ⟨-1737234226995545384737373497709129116129391486725, -1737234226995545384737373497709129116129389389572⟩, ⟨-1737234226995545384737373497709129112520033186947, -1737234226995545384737373497709129112520031089794⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2203763072011470146489582452753053373482105882297, 2203763072011470146489582452753053373482105882298⟩
def centerBExp : DyadicInterval precision := ⟨71626702092848344755875937588385772357503071902, 71626702092848344755875937588385774556526327455⟩
def centerBLog : DyadicInterval precision := ⟨69926844137049373960575473989474229791945256931, 69926844137049373960575473989474231990968512484⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71626702092848344755875937588385772907258885790, scale precision, 71626702092848344755875937588385774006770513567, scale precision,
    4, 128, 4, 128, ⟨-4407526144022940292979164905506106758181663828695, -4407526144022940292979164905506106758181661731542⟩, ⟨-4407526144022940292979164905506106735746761797643, -4407526144022940292979164905506106735746759700490⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨862235822613332734442002484759373418279860428951, 875019236366843678144084161940470670675231405862⟩
def wholeCExp : DyadicInterval precision := ⟨441330836627887409297469961440319841421973682722, 449119196648549881059977620731960643155267389868⟩
def wholeCLog : DyadicInterval precision := ⟨385659774648085658925371223910079293491529005464, 391629543164700278112090303032403187624270159377⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨441330836627887409297469961440319841971729496610, scale precision, 449119196648549881059977620731960642605511575980, scale precision,
    1, 128, 1, 128, ⟨-1750038472733687356288168323880941343171023303345, -1750038472733687356288168323880941343171021206192⟩, ⟨-1724471645226665468884004969518746834770733530729, -1724471645226665468884004969518746834770731433576⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2185299997858007781513684444410996213977655824580, 2222255291856429851874220686980443631899353089466⟩
def wholeBExp : DyadicInterval precision := ⟨69836874494747442705286338675083159253880156170, 73459470668620058807616494005055842293715113217⟩
def wholeBLog : DyadicInterval precision := ⟨68219639334661164280174563685157613791278447262, 71672943550938824621250011126147640875225700363⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨69836874494747442705286338675083159803635970058, scale precision, 73459470668620058807616494005055841743959299329, scale precision,
    4, 128, 4, 128, ⟨-4444510583712859703748441373960887275303646816282, -4444510583712859703748441373960887275303644719129⟩, ⟨-4370599995716015563027368888821992417017730180232, -4370599995716015563027368888821992417017728083079⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0252StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0253StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0253StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨856302210448687089229127087332001370695025939878, 856302210448687089229127087332001370695025939879⟩
def centerCExp : DyadicInterval precision := ⟨452780838538154598547195114684921255680274459284, 452780838538154598547195114684921257879297714837⟩
def centerCLog : DyadicInterval precision := ⟨394427782397571217242755176975606392164838593931, 394427782397571217242755176975606394363861849484⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨452780838538154598547195114684921256230030273172, scale precision, 452780838538154598547195114684921257329541900949, scale precision,
    1, 128, 1, 128, ⟨-1712604420897374178458254174664002743164573742253, -1712604420897374178458254174664002743164571645100⟩, ⟨-1712604420897374178458254174664002739615532114412, -1712604420897374178458254174664002739615530017259⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2167496778030749535375849116874054591809577372416, 2167496778030749535375849116874054591809577372417⟩
def centerBExp : DyadicInterval precision := ⟨75271136605338473771393125206681978006309588583, 75271136605338473771393125206681980205332844136⟩
def centerBLog : DyadicInterval precision := ⟨73396890443204713548625200829746793788885802052, 73396890443204713548625200829746795987909057605⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75271136605338473771393125206681978556065402471, scale precision, 75271136605338473771393125206681979655577030248, scale precision,
    4, 128, 4, 128, ⟨-4334993556061499070751698233748109194293486730414, -4334993556061499070751698233748109194293484633261⟩, ⟨-4334993556061499070751698233748109172944824856396, -4334993556061499070751698233748109172944822759243⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨849960879361055916238778446333942431649780212695, 862664165944678037906770610371578220863353369137⟩
def wholeCExp : DyadicInterval precision := ⟨448856014129685698715715233182597969841110838451, 456727091192909713204266828372060282065009330876⟩
def wholeCLog : DyadicInterval precision := ⟨391428211655344317075084778943367367187901134898, 397437535766550800592075976754544798673564485356⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨448856014129685698715715233182597970390866652339, scale precision, 456727091192909713204266828372060281515253516988, scale precision,
    1, 128, 1, 128, ⟨-1725328331889356075813541220743156443516745119174, -1725328331889356075813541220743156443516743022021⟩, ⟨-1699921758722111832477556892667884861540373027250, -1699921758722111832477556892667884861540370930097⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2149094032349808565141438601629983347811363735400, 2185930721759970506683951043565355111437476297358⟩
def wholeBExp : DyadicInterval precision := ⟨73396093860432837040928756228195810171549399362, 77190785294164538614904811028948302194541747471⟩
def wholeBLog : DyadicInterval precision := ⟨71612598555419744477175956947252754791517785487, 75221375447495358638583620322878407343952598468⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73396093860432837040928756228195810721305213250, scale precision, 77190785294164538614904811028948301644785933583, scale precision,
    4, 128, 4, 128, ⟨-4371861443519941013367902087130710233821980656167, -4371861443519941013367902087130710233821978559014⟩, ⟨-4298188064699617130282877203259966685213856280696, -4298188064699617130282877203259966685213854183543⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0253StableWitnesses

end


