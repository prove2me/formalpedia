-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0152StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0152StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:26:49.540999+00:00
-- url     : https://prove2.me/theorems/a69eaa1d-1883-484a-aeae-d418bcbb9c1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0152StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0153StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0152StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0153StableWitnesses, GeneralCK.Certificates.E8TAxisProd0154StableWitnesses, GeneralCK.Certificates.E8TAxisProd0155StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0152StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0153StableWitnesses, GeneralCK.Certificates.E8TAxisProd0154StableWitnesses, GeneralCK.Certificates.E8TAxisProd0155StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0152StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0153StableWitnesses, GeneralCK.Certificates.E8TAxisProd0154StableWitnesses, GeneralCK.Certificates.E8TAxisProd0155StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0152StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0153StableWitnesses, GeneralCK/Certificates/E8TAxisProd0154StableWitnesses, GeneralCK/Certificates/E8TAxisProd0155StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0152StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0152StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨386602250249661028027369900336867183330838872291, 386602250249661028027369900336867183330838872292⟩
def centerCExp : DyadicInterval precision := ⟨861066482581620896971668148914828234382999341876, 861066482581620896971668148914828236582022597429⟩
def centerCLog : DyadicInterval precision := ⟨676980851973153073123885595525357301396363950862, 676980851973153073123885595525357303595387206415⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨861066482581620896971668148914828234932755155764, scale precision, 861066482581620896971668148914828236032266783541, scale precision,
    0, 128, 0, 128, ⟨-773204500499322056054739800673734367594787953001, -773204500499322056054739800673734367594785855848⟩, ⟨-773204500499322056054739800673734365728569633316, -773204500499322056054739800673734365728567536163⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨829216279520712393900938101046269556215249538228, 829216279520712393900938101046269556215249538229⟩
def centerBExp : DyadicInterval precision := ⟨469878476335662986723043107625858126172159333351, 469878476335662986723043107625858128371182588904⟩
def centerBLog : DyadicInterval precision := ⟨407423405231871294786240340961808659532979155499, 407423405231871294786240340961808661732002411052⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨469878476335662986723043107625858126721915147239, scale precision, 469878476335662986723043107625858127821426775016, scale precision,
    1, 128, 1, 128, ⟨-1658432559041424787801876202092539114140450809295, -1658432559041424787801876202092539114140448712142⟩, ⟨-1658432559041424787801876202092539110720549440771, -1658432559041424787801876202092539110720547343618⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨377731346157135098373979726371647444980012146880, 395502484258857815319500638290738212734295774002⟩
def wholeCExp : DyadicInterval precision := ⟨850642666916892482973072885744241869265832757134, 871583049021038093838557160181216577129161250328⟩
def wholeCLog : DyadicInterval precision := ⟨670406787412489536570811442140947324780582840560, 683583580248640024900874896368972880223378480143⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨850642666916892482973072885744241869815588571022, scale precision, 871583049021038093838557160181216576579405436440, scale precision,
    0, 128, 0, 128, ⟨-791004968517715630639001276581476426413136120409, -791004968517715630639001276581476426413134023256⟩, ⟨-755462692314270196747959452743294889038175126191, -755462692314270196747959452743294889038173029038⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨807857035289196051982800404807096288274968053078, 850812299164621819991992738866602209561071217501⟩
def wholeBExp : DyadicInterval precision := ⟨456195254582860327490604387826336281420003573666, 483815326071864986220832064228306289520946503392⟩
def wholeBLog : DyadicInterval precision := ⟨397032272391672577033875445336028269937362044282, 417931740577476337238539891928287493899520091273⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨456195254582860327490604387826336281969759387554, scale precision, 483815326071864986220832064228306288971190689504, scale precision,
    1, 128, 1, 128, ⟨-1701624598329243639983985477733204420883382808316, -1701624598329243639983985477733204420883380711163⟩, ⟨-1615714070578392103965600809614192574889243541213, -1615714070578392103965600809614192574889241444060⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0152StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0153StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0153StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183100243, 364478458648618710654128585069611790600183100244⟩
def centerDExp : DyadicInterval precision := ⟨887534276475298848733503786031227102092850438854, 887534276475298848733503786031227104291873694407⟩
def centerDLog : DyadicInterval precision := ⟨693541818075819702070900853962455106453799173953, 693541818075819702070900853962455108652822429506⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨887534276475298848733503786031227102642606252742, scale precision, 887534276475298848733503786031227103742117880519, scale precision,
    0, 128, 0, 128, ⟨-728956917297237421308257170139223582105649493848, -728956917297237421308257170139223582105647396695⟩, ⟨-728956917297237421308257170139223580295085004280, -728956917297237421308257170139223580295082907127⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨369568248505220937206034456409214942181457487652, 369568248505220937206034456409214942181457487653⟩
def centerCExp : DyadicInterval precision := ⟨881373944872612397569700762679825660316755451731, 881373944872612397569700762679825662515778707284⟩
def centerCLog : DyadicInterval precision := ⟨689704004892402114795599868554869435844467149230, 689704004892402114795599868554869438043490404783⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨881373944872612397569700762679825660866511265619, scale precision, 881373944872612397569700762679825661966022893396, scale precision,
    0, 128, 0, 128, ⟨-739136497010441874412068912818429885274525706473, -739136497010441874412068912818429885274523609320⟩, ⟨-739136497010441874412068912818429883451306341289, -739136497010441874412068912818429883451304244136⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨787554052826543110067927518777471603701303638456, 787554052826543110067927518777471603701303638457⟩
def centerBExp : DyadicInterval precision := ⟨497445998441326431016783164741866880198155367936, 497445998441326431016783164741866882397178623489⟩
def centerBLog : DyadicInterval precision := ⟨428136648784000992750612541222540034593503840636, 428136648784000992750612541222540036792527096189⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨497445998441326431016783164741866880747911181824, scale precision, 497445998441326431016783164741866881847422809601, scale precision,
    1, 128, 1, 128, ⟨-1575108105653086220135855037554943209017796757295, -1575108105653086220135855037554943209017794660142⟩, ⟨-1575108105653086220135855037554943205787419893684, -1575108105653086220135855037554943205787417796531⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 372966609392870424646531471060848444542040850581⟩
def wholeDExp : DyadicInterval precision := ⟨877284626339432933560204346302551150236929118789, 897872332234039104779267097055247456527332583462⟩
def wholeDLog : DyadicInterval precision := ⟨687150831490084437187371430673459275775078265310, 699959742628865241142888209739517591976703657011⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨877284626339432933560204346302551150786684932677, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-745933218785740849293062942121696889999941751488, -745933218785740849293062942121696889999939654335⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨360751790294758116634357805075516741583889296051, 378412697989057406245291916457002576216556282367⟩
def wholeCExp : DyadicInterval precision := ⟨870770764008120892198273236264355023781578632507, 892072066991257785754281552593305038452213888819⟩
def wholeCLog : DyadicInterval precision := ⟨683074656337333880270727106606651153462071304568, 696362375538974423103809126688934701762297486366⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨870770764008120892198273236264355024331334446395, scale precision, 892072066991257785754281552593305037902458074931, scale precision,
    0, 128, 0, 128, ⟨-756825395978114812490583832914005153355823763144, -756825395978114812490583832914005153355821665991⟩, ⟨-721503580589516233268715610151033482267102383918, -721503580589516233268715610151033482267100286765⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨766645226495309387918731185011730320819877664149, 808690249678272356060172778580176390873837343219⟩
def wholeBExp : DyadicInterval precision := ⟨483263986073075030390070547349518200728682002829, 511884904521197338754882311587328659230786221130⟩
def wholeBLog : DyadicInterval precision := ⟨417517464377230252333537421247436150777368586076, 438869500450241106105566329066449655664580817868⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨483263986073075030390070547349518201278437816717, scale precision, 511884904521197338754882311587328658681030407242, scale precision,
    1, 128, 1, 128, ⟨-1617380499356544712120345557160352783410263979297, -1617380499356544712120345557160352783410261882144⟩, ⟨-1533290452990618775837462370023460640070128097091, -1533290452990618775837462370023460640070125999938⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0153StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0154StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0154StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨385918840621167887743200173772399928336826829717, 385918840621167887743200173772399928336826829718⟩
def centerCExp : DyadicInterval precision := ⟨861872142137203081603315082443366646447423349709, 861872142137203081603315082443366648646446605262⟩
def centerCLog : DyadicInterval precision := ⟨677487734235961580643602162341500539823141538104, 677487734235961580643602162341500542022164793657⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨861872142137203081603315082443366646997179163597, scale precision, 861872142137203081603315082443366648096690791374, scale precision,
    0, 128, 0, 128, ⟨-771837681242335775486400347544799857605891617464, -771837681242335775486400347544799857605889520311⟩, ⟨-771837681242335775486400347544799855741417798557, -771837681242335775486400347544799855741415701404⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨828374231748295023329309883077257840952410920568, 828374231748295023329309883077257840952410920569⟩
def centerBExp : DyadicInterval precision := ⟨470420231695129958342463031596070243343166806664, 470420231695129958342463031596070245542190062217⟩
def centerBLog : DyadicInterval precision := ⟨407833301405471456473854129954459985240555765576, 407833301405471456473854129954459987439579021129⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨470420231695129958342463031596070243892922620552, scale precision, 470420231695129958342463031596070244992434248329, scale precision,
    1, 128, 1, 128, ⟨-1656748463496590046658619766154515683612804324173, -1656748463496590046658619766154515683612802227020⟩, ⟨-1656748463496590046658619766154515680196841455250, -1656748463496590046658619766154515680196839358097⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨377050163746239715183294877933211736903658442448, 394816793649930260865803568113874655646762532968⟩
def wholeCExp : DyadicInterval precision := ⟨851441231098437619362828790676466224092099075779, 872395889500669802048748927324068164122748526374⟩
def wholeCLog : DyadicInterval precision := ⟨670911471033301839823247132083422618021338789722, 684092674841084336192144363030727301008266496339⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨851441231098437619362828790676466224641854889667, scale precision, 872395889500669802048748927324068163572992712486, scale precision,
    0, 128, 0, 128, ⟨-789633587299860521731607136227749312237183753800, -789633587299860521731607136227749312237181656647⟩, ⟨-754100327492479430366589755866423472886326636058, -754100327492479430366589755866423472886324538905⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨807024177793826630419499886978758524921452957856, 849960879361055916238778446333942431649780212696⟩
def wholeBExp : DyadicInterval precision := ⟨456727091192909713204266828372060279865986075323, 484367058514719616402032561299605968698353360338⟩
def wholeBLog : DyadicInterval precision := ⟨397437535766550800592075976754544796474541229803, 418346194137196836450847119605287024299403955757⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨456727091192909713204266828372060280415741889211, scale precision, 484367058514719616402032561299605968148597546450, scale precision,
    1, 128, 1, 128, ⟨-1699921758722111832477556892667884865058749920688, -1699921758722111832477556892667884865058747823535⟩, ⟨-1614048355587653260838999773957517048184105012328, -1614048355587653260838999773957517048184102915175⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0154StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0155StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0155StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183100243, 364478458648618710654128585069611790600183100244⟩
def centerDExp : DyadicInterval precision := ⟨887534276475298848733503786031227102092850438854, 887534276475298848733503786031227104291873694407⟩
def centerDLog : DyadicInterval precision := ⟨693541818075819702070900853962455106453799173953, 693541818075819702070900853962455108652822429506⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨887534276475298848733503786031227102642606252742, scale precision, 887534276475298848733503786031227103742117880519, scale precision,
    0, 128, 0, 128, ⟨-728956917297237421308257170139223582105649493848, -728956917297237421308257170139223582105647396695⟩, ⟨-728956917297237421308257170139223580295085004280, -728956917297237421308257170139223580295082907127⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨368889074472186204716870798597736126589315670390, 368889074472186204716870798597736126589315670391⟩
def centerCExp : DyadicInterval precision := ⟨882193491763052121530915309815483939631135056862, 882193491763052121530915309815483941830158312415⟩
def centerCLog : DyadicInterval precision := ⟨690215154390933743735042557289068074964815552537, 690215154390933743735042557289068077163838808090⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨882193491763052121530915309815483940180890870750, scale precision, 882193491763052121530915309815483941280402498527, scale precision,
    0, 128, 0, 128, ⟨-737778148944372409433741597195472254089395197779, -737778148944372409433741597195472254089393100626⟩, ⟨-737778148944372409433741597195472252267869580934, -737778148944372409433741597195472252267867483781⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨786729847750390501358425749330299331038393140711, 786729847750390501358425749330299331038393140712⟩
def centerBExp : DyadicInterval precision := ⟨498007378338742268521669675036963225810181847854, 498007378338742268521669675036963228009205103407⟩
def centerBLog : DyadicInterval precision := ⟨428555414496031672302179247207445666266048678711, 428555414496031672302179247207445668465071934264⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨498007378338742268521669675036963226359937661742, scale precision, 498007378338742268521669675036963227459449289519, scale precision,
    1, 128, 1, 128, ⟨-1573459695500781002716851498660598663690155037142, -1573459695500781002716851498660598663690152939989⟩, ⟨-1573459695500781002716851498660598660463419622858, -1573459695500781002716851498660598660463417525705⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 372966609392870424646531471060848444542040850581⟩
def wholeDExp : DyadicInterval precision := ⟨877284626339432933560204346302551150236929118789, 897872332234039104779267097055247456527332583462⟩
def wholeDLog : DyadicInterval precision := ⟨687150831490084437187371430673459275775078265310, 699959742628865241142888209739517591976703657011⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨877284626339432933560204346302551150786684932677, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-745933218785740849293062942121696889999941751488, -745933218785740849293062942121696889999939654335⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨360074740751160892894090487962528567327495184603, 377731346157135098373979726371647444980012146881⟩
def wholeCExp : DyadicInterval precision := ⟨871583049021038093838557160181216574930137994775, 892898965645121959397532364804649249910439614843⟩
def wholeCLog : DyadicInterval precision := ⟨683583580248640024900874896368972878024355224590, 696875765659682097297052894707441002618043576303⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨871583049021038093838557160181216575479893808663, scale precision, 892898965645121959397532364804649249360683800955, scale precision,
    0, 128, 0, 128, ⟨-755462692314270196747959452743294890881875558486, -755462692314270196747959452743294890881873461333⟩, ⟨-720149481502321785788180975925057133755148263021, -720149481502321785788180975925057133755146165868⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨765829836543995576408455012925101753097866819757, 807857035289196051982800404807096288274968053079⟩
def wholeBExp : DyadicInterval precision := ⟨483815326071864986220832064228306287321923247839, 512456397221692565833276317058782593017330679115⟩
def wholeBLog : DyadicInterval precision := ⟨417931740577476337238539891928287491700496835720, 439292690018400355333875668480905795630937550209⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨483815326071864986220832064228306287871679061727, scale precision, 512456397221692565833276317058782592467574865227, scale precision,
    1, 128, 1, 128, ⟨-1615714070578392103965600809614192578210630768251, -1615714070578392103965600809614192578210628671098⟩, ⟨-1531659673087991152816910025850203504627856861829, -1531659673087991152816910025850203504627854764676⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0155StableWitnesses

end


