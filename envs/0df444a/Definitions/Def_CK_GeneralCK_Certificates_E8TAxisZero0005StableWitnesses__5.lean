-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0005StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0005StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:35:24.525931+00:00
-- url     : https://prove2.me/theorems/b1e6df0c-7e45-4cae-bcd7-49f93d6d2288
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0005StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0006StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0005StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0006StableWitnesses, GeneralCK.Certificates.E8TAxisZero0007StableWitnesses, GeneralCK.Certificates.E8TAxisZero0008StableWitnesses, GeneralCK.Certificates.E8TAxisZero0009StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0005StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0006StableWitnesses, GeneralCK.Certificates.E8TAxisZero0007StableWitnesses, GeneralCK.Certificates.E8TAxisZero0008StableWitnesses, GeneralCK.Certificates.E8TAxisZero0009StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0005StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0006StableWitnesses, GeneralCK.Certificates.E8TAxisZero0007StableWitnesses, GeneralCK.Certificates.E8TAxisZero0008StableWitnesses, GeneralCK.Certificates.E8TAxisZero0009StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0005StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0006StableWitnesses, GeneralCK/Certificates/E8TAxisZero0007StableWitnesses, GeneralCK/Certificates/E8TAxisZero0008StableWitnesses, GeneralCK/Certificates/E8TAxisZero0009StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0005StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨24220466060029118896113524058399908749108492980, 24220466060029118896113524058399908749108492981⟩
def centerCExp : DyadicInterval precision := ⟨1413854687358199078213875037703050622297290468702, 1413854687358199078213875037703050624496313724255⟩
def centerCLog : DyadicInterval precision := ⟨989015958654867489723299125598598771253233385874, 989015958654867489723299125598598773452256641427⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1413854687358199078213875037703050622847046282590, scale precision, 1413854687358199078213875037703050623946557910367, scale precision,
    0, 128, 0, 128, ⟨-48440932120058237792227048116799818066500637632, -48440932120058237792227048116799818066498540479⟩, ⟨-48440932120058237792227048116799816929935431441, -48440932120058237792227048116799816929933334288⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨47188546783399559438734684046034277281554052952, 47188546783399559438734684046034277281554052953⟩
def centerBExp : DyadicInterval precision := ⟨1370107217880869781974877110045552700062516438850, 1370107217880869781974877110045552702261539694403⟩
def centerBLog : DyadicInterval precision := ⟨966608865339651213022540113418688110423791416365, 966608865339651213022540113418688112622814671918⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1370107217880869781974877110045552700612272252738, scale precision, 1370107217880869781974877110045552701711783880515, scale precision,
    0, 128, 0, 128, ⟨-94377093566799118877469368092068555149536998700, -94377093566799118877469368092068555149534901547⟩, ⟨-94377093566799118877469368092068553976681310263, -94377093566799118877469368092068553976679213110⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989432986973, 26278910172762769820712328120209532577634289712⟩
def wholeCExp : DyadicInterval precision := ⟨1409877619422784131283828294378918307862547641302, 1417842757137037989742285799922994929667109837448⟩
def wholeCLog : DyadicInterval precision := ⟨986993073785723638762592089261738282950696548032, 991041631832012714857158240438297380855618410517⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1409877619422784131283828294378918308412303455190, scale precision, 1417842757137037989742285799922994929117354023560, scale precision,
    0, 128, 0, 128, ⟨-52557820345525539641424656240419065725155276982, -52557820345525539641424656240419065725153179829⟩, ⟨-44324267483763059541032859816138423412182869373, -44324267483763059541032859816138423412180772220⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 50041379200560764912647798132580101207504646538⟩
def wholeBExp : DyadicInterval precision := ⟨1364768781850218961742407903668732584768475455358, 1375465749469112915336031076552653134255992540413⟩
def wholeBLog : DyadicInterval precision := ⟨963850893691077814713601955824195277127821752601, 969371994805781330198871946178310256493558400824⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1364768781850218961742407903668732585318231269246, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-100082758401121529825295596265160203003732059804, -100082758401121529825295596265160203003729962651⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0005StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0006StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨21370495222089901813019887143702178164829792486, 21370495222089901813019887143702178164829792487⟩
def centerDExp : DyadicInterval precision := ⟨1419379569827633630618157326958425743127605926610, 1419379569827633630618157326958425745326629182163⟩
def centerDLog : DyadicInterval precision := ⟨991821481258824824738644685212964217149601286016, 991821481258824824738644685212964219348624541569⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1419379569827633630618157326958425743677361740498, scale precision, 1419379569827633630618157326958425744776873368275, scale precision,
    0, 128, 0, 128, ⟨-42740990444179803626039774287404356895731217634, -42740990444179803626039774287404356895729120481⟩, ⟨-42740990444179803626039774287404355763590049465, -42740990444179803626039774287404355763587952312⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨22637124082456445254227729657395697674875674669, 22637124082456445254227729657395697674875674670⟩
def centerCExp : DyadicInterval precision := ⟨1416921454323240139594433243688361662242981673120, 1416921454323240139594433243688361664442004928673⟩
def centerCLog : DyadicInterval precision := ⟨990573920836186620650833277746320784780310117698, 990573920836186620650833277746320786979333373251⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1416921454323240139594433243688361662792737487008, scale precision, 1416921454323240139594433243688361663892249114785, scale precision,
    0, 128, 0, 128, ⟨-45274248164912890508455459314791395916805017295, -45274248164912890508455459314791395916802920142⟩, ⟨-45274248164912890508455459314791394782699778535, -45274248164912890508455459314791394782697681382⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨44019221828644720306073496201742716112992228277, 44019221828644720306073496201742716112992228278⟩
def centerBExp : DyadicInterval precision := ⟨1376062387546952102332932362773385023678422884603, 1376062387546952102332932362773385025877446140156⟩
def centerBLog : DyadicInterval precision := ⟨969679328563446229227733723859229679757920562489, 969679328563446229227733723859229681956943818042⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1376062387546952102332932362773385024228178698491, scale precision, 1376062387546952102332932362773385025327690326268, scale precision,
    0, 128, 0, 128, ⟨-88038443657289440612146992403485432809875472187, -88038443657289440612146992403485432809873375034⟩, ⟨-88038443657289440612146992403485431642095538078, -88038443657289440612146992403485431642093440925⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932455778, 22162133741881529770516429908069211989432986974⟩
def wholeDExp : DyadicInterval precision := ⟨1417842757137037989742285799922994927468086581895, 1420918019911383254566844357126927031797158658050⟩
def wholeDLog : DyadicInterval precision := ⟨991041631832012714857158240438297378656595154964, 992601745007901601457433275450218203485852649055⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1417842757137037989742285799922994928017842395783, scale precision, 1420918019911383254566844357126927031247402844162, scale precision,
    0, 128, 0, 128, ⟨-44324267483763059541032859816138424545551175676, -44324267483763059541032859816138424545549078523⟩, ⟨-41157742587080362175549384121068020958408269492, -41157742587080362175549384121068020958406172339⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932455778, 24695481355850246866248295865805301976344615012⟩
def wholeCExp : DyadicInterval precision := ⟨1412935927708083132512800521363519720725837255886, 1420918019911383254566844357126927031797158658050⟩
def wholeCLog : DyadicInterval precision := ⟨988548891914689170103698086859276755252169128429, 992601745007901601457433275450218203485852649055⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1412935927708083132512800521363519721275593069774, scale precision, 1420918019911383254566844357126927031247402844162, scale precision,
    0, 128, 0, 128, ⟨-49390962711700493732496591731610604521342406679, -49390962711700493732496591731610604521340309526⟩, ⟨-41157742587080362175549384121068020958408269492, -41157742587080362175549384121068020958406172339⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨41167241659773099362357909881550147015249154044, 46871591652396955948239255283142047275791395946⟩
def wholeBExp : DyadicInterval precision := ⟨1370701615716012189539119176421333096411901624091, 1381443388570658598756805128725695648682979353028⟩
def wholeBLog : DyadicInterval precision := ⟨966915624602095365704810787008635852288416019661, 972448215678536315612740583202668588885486229541⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1370701615716012189539119176421333096961657437979, scale precision, 1381443388570658598756805128725695648133223539140, scale precision,
    0, 128, 0, 128, ⟨-93743183304793911896478510566284095137757383212, -93743183304793911896478510566284095137755286059⟩, ⟨-82334483319546198724715819763100293448883758966, -82334483319546198724715819763100293448881661813⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0006StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0007StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643299660144, 19787261415618956269193137821462137643299660145⟩
def centerDExp : DyadicInterval precision := ⟨1422458110153910514512537297173309437352704550462, 1422458110153910514512537297173309439551727806015⟩
def centerDLog : DyadicInterval precision := ⟨993382423595496802456179790205135829228690482622, 993382423595496802456179790205135831427713738175⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1422458110153910514512537297173309437902460364350, scale precision, 1422458110153910514512537297173309439001971992127, scale precision,
    0, 128, 0, 128, ⟨-39574522831237912538386275642924275851445840514, -39574522831237912538386275642924275851443743361⟩, ⟨-39574522831237912538386275642924274721754897217, -39574522831237912538386275642924274721752800064⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨21053843929995845187789694472046872430432246941, 21053843929995845187789694472046872430432246942⟩
def centerCExp : DyadicInterval precision := ⟨1419994753219220517666583706272429596750295095776, 1419994753219220517666583706272429598949318351329⟩
def centerCLog : DyadicInterval precision := ⟨992133537010893656493896321340013157096725839029, 992133537010893656493896321340013159295749094582⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1419994753219220517666583706272429597300050909664, scale precision, 1419994753219220517666583706272429598399562537441, scale precision,
    0, 128, 0, 128, ⟨-42107687859991690375579388944093745426690888159, -42107687859991690375579388944093745426688791006⟩, ⟨-42107687859991690375579388944093744295040196762, -42107687859991690375579388944093744295038099609⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨40850377929490787525132265847486563880844462280, 40850377929490787525132265847486563880844462281⟩
def centerBExp : DyadicInterval precision := ⟨1382042531548774472754394678349177424965897883659, 1382042531548774472754394678349177427164921139212⟩
def centerBLog : DyadicInterval precision := ⟨972756190746019273686271467148684857525744169409, 972756190746019273686271467148684859724767424962⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1382042531548774472754394678349177425515653697547, scale precision, 1382042531548774472754394678349177426615165325324, scale precision,
    0, 128, 0, 128, ⟨-81700755858981575050264531694973128343053428885, -81700755858981575050264531694973128343051331732⟩, ⟨-81700755858981575050264531694973127180326517392, -81700755858981575050264531694973127180324420239⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156033732657, 20578871293540181087774692060534010761932455779⟩
def wholeDExp : DyadicInterval precision := ⟨1420918019911383254566844357126927029598135402497, 1423999843327116683343282796578766321720660974834⟩
def wholeDLog : DyadicInterval precision := ⟨992601745007901601457433275450218201286829393502, 994163517538761546318115582447098114172952119197⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1420918019911383254566844357126927030147891216385, scale precision, 1423999843327116683343282796578766321170905160946, scale precision,
    0, 128, 0, 128, ⟨-41157742587080362175549384121068022089323650775, -41157742587080362175549384121068022089321553622⟩, ⟨-37991330095470232437237785869777167747834587957, -37991330095470232437237785869777167747832490804⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156033732657, 23112119987288769110966614346048366509737452060⟩
def wholeCExp : DyadicInterval precision := ⟨1416000739382545652019056606267271856467349476465, 1423999843327116683343282796578766321720660974834⟩
def wholeCLog : DyadicInterval precision := ⟨990106358699667674089767031322997499909707645129, 994163517538761546318115582447098114172952119197⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1416000739382545652019056606267271857017105290353, scale precision, 1423999843327116683343282796578766321170905160946, scale precision,
    0, 128, 0, 128, ⟨-46224239974577538221933228692096733586897282207, -46224239974577538221933228692096733586895185054⟩, ⟨-37991330095470232437237785869777167747834587957, -37991330095470232437237785869777167747832490804⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨37998801077005824018584868335497446470094208874, 43702316363191017940573234188486312291623637587⟩
def wholeBExp : DyadicInterval precision := ⟨1376659275366914708624851436993480763400185401428, 1387446151770136419623988677444135732926778635443⟩
def wholeBLog : DyadicInterval precision := ⟨969986726310514225814593545165102078801997762132, 975530863852771772001888955504779365508547212326⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1376659275366914708624851436993480763949941215316, scale precision, 1387446151770136419623988677444135732377022821555, scale precision,
    0, 128, 0, 128, ⟨-87404632726382035881146468376972625166885129536, -87404632726382035881146468376972625166883032383⟩, ⟨-75997602154011648037169736670994892361090219046, -75997602154011648037169736670994892361088121893⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0007StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0008StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨60981562246941182391851692343549914653715634261, 60981562246941182391851692343549914653715634262⟩
def centerDExp : DyadicInterval precision := ⟨1344488804354560387653913977701155507615899604953, 1344488804354560387653913977701155509814922860506⟩
def centerDLog : DyadicInterval precision := ⟨953326044385255946846825783453523246727646501740, 953326044385255946846825783453523248926669757293⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1344488804354560387653913977701155508165655418841, scale precision, 1344488804354560387653913977701155509265167046618, scale precision,
    0, 128, 0, 128, ⟨-121963124493882364783703384687099829905034185949, -121963124493882364783703384687099829905032088796⟩, ⟨-121963124493882364783703384687099828709830448249, -121963124493882364783703384687099828709828351096⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨61616005372896281097397239346326085284456382970, 61616005372896281097397239346326085284456382971⟩
def centerCExp : DyadicInterval precision := ⟨1343322016067629531180816907420006148193793600580, 1343322016067629531180816907420006150392816856133⟩
def centerCLog : DyadicInterval precision := ⟨952718195688988064491056549379153725141552392487, 952718195688988064491056549379153727340575648040⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1343322016067629531180816907420006148743549414468, scale precision, 1343322016067629531180816907420006149843061042245, scale precision,
    0, 128, 0, 128, ⟨-123232010745792562194794478692652171167034750912, -123232010745792562194794478692652171167032653759⟩, ⟨-123232010745792562194794478692652169970792878123, -123232010745792562194794478692652169970790780970⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨122848688962441263613203278400959891368589806121, 122848688962441263613203278400959891368589806122⟩
def centerBExp : DyadicInterval precision := ⟨1235346451068630015043686617380955604720345471969, 1235346451068630015043686617380955606919368727522⟩
def centerBLog : DyadicInterval precision := ⟨895344096204919741620693735092813397380350450680, 895344096204919741620693735092813399579373706233⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1235346451068630015043686617380955605270101285857, scale precision, 1235346451068630015043686617380955606369612913634, scale precision,
    0, 128, 0, 128, ⟨-245697377924882527226406556801919783387580410166, -245697377924882527226406556801919783387578313013⟩, ⟨-245697377924882527226406556801919782086780911474, -245697377924882527226406556801919782086778814321⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 63360863746962342702697993485127651995684952634⟩
def wholeDExp : DyadicInterval precision := ⟨1340118310385255731396483422015350658626993302998, 1348872859460053731599279250908956040444361819487⟩
def wholeDLog : DyadicInterval precision := ⟨951047895604627342379828868169897140353010055619, 955607699899585814401544643147774225289199821907⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1340118310385255731396483422015350659176749116886, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-126721727493924685405395986970255304590921766561, -126721727493924685405395986970255304590919669408⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 64629982951322598580719314150188454126481843139⟩
def wholeCExp : DyadicInterval precision := ⟨1337792902321001359725941128831362487348157711088, 1348872859460053731599279250908956040444361819487⟩
def wholeCLog : DyadicInterval precision := ⟨949834312395558470178147735810135993135986371821, 955607699899585814401544643147774225289199821907⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1337792902321001359725941128831362487897913524976, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-129259965902645197161438628300376908853557712090, -129259965902645197161438628300376908853555614937⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨117424693269005932071068146852707840826728800012, 128276576533857721025787388172632631798945739447⟩
def wholeBExp : DyadicInterval precision := ⟨1226204510955732588180712779922086012362307247027, 1244549920391411357530365430786644964073675738546⟩
def wholeBLog : DyadicInterval precision := ⟨890381392629473614381711917360076507391241130920, 900323236805503350434862310641063753455001590011⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1226204510955732588180712779922086012912063060915, scale precision, 1244549920391411357530365430786644963523919924658, scale precision,
    0, 128, 0, 128, ⟨-256553153067715442051574776345265264253141317498, -256553153067715442051574776345265264253139220345⟩, ⟨-234849386538011864142136293705415681007868617244, -234849386538011864142136293705415681007866520091⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0008StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0009StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨56224069662401947129176131245290424868351320698, 56224069662401947129176131245290424868351320699⟩
def centerDExp : DyadicInterval precision := ⟨1353270542552318619031293173544076935377002222510, 1353270542552318619031293173544076937576025478063⟩
def centerDLog : DyadicInterval precision := ⟨957892874924759606731049484620710570189124178339, 957892874924759606731049484620710572388147433892⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1353270542552318619031293173544076935926758036398, scale precision, 1353270542552318619031293173544076937026269664175, scale precision,
    0, 128, 0, 128, ⟨-112448139324803894258352262490580850330427558828, -112448139324803894258352262490580850330425461675⟩, ⟨-112448139324803894258352262490580849142979821120, -112448139324803894258352262490580849142977723967⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨56858319549409132114990700219771222531259906343, 56858319549409132114990700219771222531259906344⟩
def centerCExp : DyadicInterval precision := ⟨1352096490752689766398775694159672818074703130828, 1352096490752689766398775694159672820273726386381⟩
def centerCLog : DyadicInterval precision := ⟨957283150063576542250474812779312626076317126780, 957283150063576542250474812779312628275340382333⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1352096490752689766398775694159672818624458944716, scale precision, 1352096490752689766398775694159672819723970572493, scale precision,
    0, 128, 0, 128, ⟨-113716639098818264229981400439542445656760272152, -113716639098818264229981400439542445656758174999⟩, ⟨-113716639098818264229981400439542444468281450373, -113716639098818264229981400439542444468279353220⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨113279450314663153109211311785784474832424031926, 113279450314663153109211311785784474832424031927⟩
def centerBExp : DyadicInterval precision := ⟨1251629791774422009414544727917975059984365070649, 1251629791774422009414544727917975062183388326202⟩
def centerBLog : DyadicInterval precision := ⟨904141985694558194114408873063655307134269851086, 904141985694558194114408873063655309333293106639⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1251629791774422009414544727917975060534120884537, scale precision, 1251629791774422009414544727917975061633632512314, scale precision,
    0, 128, 0, 128, ⟨-226558900629326306218422623571568950306787349606, -226558900629326306218422623571568950306785252453⟩, ⟨-226558900629326306218422623571568949022910875252, -226558900629326306218422623571568949022908778099⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 58602635770181898821662589353151101542136562993⟩
def wholeDExp : DyadicInterval precision := ⟨1348872859460053731599279250908956038245338563934, 1357681920934804568838490939788917163911062976792⟩
def wholeDLog : DyadicInterval precision := ⟨955607699899585814401544643147774223090176566354, 960181582307675404146178190201383839808765855727⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1348872859460053731599279250908956038795094377822, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-117205271540363797643325178706302203679933740618, -117205271540363797643325178706302203679931643465⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 59871350779906312655059654590921689440155693628⟩
def wholeCExp : DyadicInterval precision := ⟨1346533005072431926854353225933980979301452895279, 1357681920934804568838490939788917163911062976792⟩
def wholeCLog : DyadicInterval precision := ⟨954390379789352380913007499717796928803157872992, 960181582307675404146178190201383839808765855727⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1346533005072431926854353225933980979851208709167, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-119742701559812625310119309181843379477007072429, -119742701559812625310119309181843379477004975276⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨107861900919962465695529931627750650712789068841, 118700586572171500710721487428242681162025303744⟩
def wholeBExp : DyadicInterval precision := ⟨1242378828106247998826148587803258948216931403842, 1260943450380055698574689747389208595926401624304⟩
def wholeBLog : DyadicInterval precision := ⟨899150188757459813599771432452226603054633248206, 909150448212166715607613698024710841333474523618⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1242378828106247998826148587803258948766687217730, scale precision, 1260943450380055698574689747389208595376645810416, scale precision,
    0, 128, 0, 128, ⟨-237401173144343001421442974856485362970769874335, -237401173144343001421442974856485362970767777182⟩, ⟨-215723801839924931391059863255501300788382473046, -215723801839924931391059863255501300788380375893⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0009StableWitnesses

end


