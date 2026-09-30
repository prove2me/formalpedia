-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0208StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0208StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:37:36.896366+00:00
-- url     : https://prove2.me/theorems/bd3f43d7-7014-42e7-ada2-5974225a6b6f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0208StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0209StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0208StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0209StableWitnesses, GeneralCK.Certificates.E8TAxisProd0210StableWitnesses, GeneralCK.Certificates.E8TAxisProd0211StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0208StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0209StableWitnesses, GeneralCK.Certificates.E8TAxisProd0210StableWitnesses, GeneralCK.Certificates.E8TAxisProd0211StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0208StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0209StableWitnesses, GeneralCK.Certificates.E8TAxisProd0210StableWitnesses, GeneralCK.Certificates.E8TAxisProd0211StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0208StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0209StableWitnesses, GeneralCK/Certificates/E8TAxisProd0210StableWitnesses, GeneralCK/Certificates/E8TAxisProd0211StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0208StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0208StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨896093812048976529173221490585129440333246652877, 896093812048976529173221490585129440333246652878⟩
def centerCExp : DyadicInterval precision := ⟨428784804112268249138033380271057257611774098962, 428784804112268249138033380271057259810797354515⟩
def centerCLog : DyadicInterval precision := ⟨375991681272252917294838357236015794122113195729, 375991681272252917294838357236015796321136451282⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨428784804112268249138033380271057258161529912850, scale precision, 428784804112268249138033380271057259261041540627, scale precision,
    1, 128, 1, 128, ⟨-1792187624097953058346442981170258882540322471431, -1792187624097953058346442981170258882540320374278⟩, ⟨-1792187624097953058346442981170258878792666237233, -1792187624097953058346442981170258878792664140080⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2280438780215732404614236095429987882107037113385, 2280438780215732404614236095429987882107037113386⟩
def centerBExp : DyadicInterval precision := ⟨64491964953193781538052581628115019449241771725, 64491964953193781538052581628115021648265027278⟩
def centerBLog : DyadicInterval precision := ⟨63109561846832888042346405406921586322410469062, 63109561846832888042346405406921588521433724615⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨64491964953193781538052581628115019998997585613, scale precision, 64491964953193781538052581628115021098509213390, scale precision,
    4, 128, 4, 128, ⟨-4560877560431464809228472190859975776672511341194, -4560877560431464809228472190859975776672509244041⟩, ⟨-4560877560431464809228472190859975751755639209499, -4560877560431464809228472190859975751755637112346⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨889622866940560267078565450060948161603839887112, 902586025993768359559526192209853986759641231130⟩
def wholeCExp : DyadicInterval precision := ⟨424992220849241514166045089804490836817317801897, 432598640801811646550421823182324848683551973606⟩
def wholeCLog : DyadicInterval precision := ⟨373056446457404052940795575140011001235257283204, 378937432257190463719391371232510241540935954088⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨424992220849241514166045089804490837367073615785, scale precision, 432598640801811646550421823182324848133796159718, scale precision,
    1, 128, 1, 128, ⟨-1805172051987536719119052384419707975409833461432, -1805172051987536719119052384419707975409831364279⟩, ⟨-1779245733881120534157130900121896321350372578280, -1779245733881120534157130900121896321350370481127⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2261861606037031545745500091786984997827912753705, 2299041052750102708121433314085385833525277148695⟩
def wholeBExp : DyadicInterval precision := ⟨62870952898152845968524666226794740219242942823, 66152499715317387072175205649539330869290688571⟩
def wholeBLog : DyadicInterval precision := ⟨61556232281743537694827355444115687778287697740, 64699053969086271720122973528557657333472589535⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨62870952898152845968524666226794740768998756711, scale precision, 66152499715317387072175205649539330319534874683, scale precision,
    4, 128, 4, 128, ⟨-4598082105500205416242866628170771679830209305269, -4598082105500205416242866628170771679830207208116⟩, ⟨-4523723212074063091491000183573969983510117390229, -4523723212074063091491000183573969983510115293076⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0208StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0209StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0209StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨883606027810012872796891821241516445502670367453, 883606027810012872796891821241516445502670367454⟩
def centerCExp : DyadicInterval precision := ⟨436175265809702025669795722568979925821573278137, 436175265809702025669795722568979928020596533690⟩
def centerCLog : DyadicInterval precision := ⟨381694579951024565976626859703523313560489488206, 381694579951024565976626859703523315759512743759⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨436175265809702025669795722568979926371329092025, scale precision, 436175265809702025669795722568979927470840719802, scale precision,
    1, 128, 1, 128, ⟨-1767212055620025745593783642483032892847420152230, -1767212055620025745593783642483032892847418055077⟩, ⟨-1767212055620025745593783642483032889163263414737, -1767212055620025745593783642483032889163261317584⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2243944260823841440125536988619402755463647774364, 2243944260823841440125536988619402755463647774365⟩
def centerBExp : DyadicInterval precision := ⟨67794547313419182870346581419654945716563296320, 67794547313419182870346581419654947915586551873⟩
def centerBLog : DyadicInterval precision := ⟨66269151766871877864429551798414533703305976751, 66269151766871877864429551798414535902329232304⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨67794547313419182870346581419654946266319110208, scale precision, 67794547313419182870346581419654947365830737985, scale precision,
    4, 128, 4, 128, ⟨-4487888521647682880251073977238805522778825281686, -4487888521647682880251073977238805522778823184533⟩, ⟨-4487888521647682880251073977238805499075767912906, -4487888521647682880251073977238805499075765815753⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨877175906901376237874711954063779399070020429472, 890057223604360727013968663923346048536464240889⟩
def wholeCExp : DyadicInterval precision := ⟨432341581535709021958392827323830479470887545635, 440030253675745449649467359245008248100306493735⟩
def wholeCLog : DyadicInterval precision := ⟨378739069985327430872574564061929840586548491675, 384660499076273856588931597425083716132820220211⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨432341581535709021958392827323830480020643359523, scale precision, 440030253675745449649467359245008247550550679847, scale precision,
    1, 128, 1, 128, ⟨-1780114447208721454027937327846692098931342082938, -1780114447208721454027937327846692098931339985785⟩, ⟨-1754351813802752475749423908127558796314101496791, -1754351813802752475749423908127558796314099399638⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2225419198344443823956498495796517003980774376233, 2262496298585247613475304611163991009425418188100⟩
def wholeBExp : DyadicInterval precision := ⟨66095068003761016001290898885138716894260246329, 69535157837558284074553879699704818793397650752⟩
def wholeBLog : DyadicInterval precision := ⟨64644108208613898104298685627019959362258883154, 67931654129900893015752327369386811360992862267⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66095068003761016001290898885138717444016060217, scale precision, 69535157837558284074553879699704818243641836864, scale precision,
    4, 128, 4, 128, ⟨-4524992597170495226950609222327982031007100310894, -4524992597170495226950609222327982031007098213741⟩, ⟨-4450838396688887647912996991593033996406689682560, -4450838396688887647912996991593033996406687585407⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0209StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0210StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0210StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨895658124772575823646769652234235613658761210983, 895658124772575823646769652234235613658761210984⟩
def centerCExp : DyadicInterval precision := ⟨429040529841723516612920149509273017892374808214, 429040529841723516612920149509273020091398063767⟩
def centerCLog : DyadicInterval precision := ⟨376189385855859145431054313023528737719283413590, 376189385855859145431054313023528739918306669143⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨429040529841723516612920149509273018442130622102, scale precision, 429040529841723516612920149509273019541642249879, scale precision,
    1, 128, 1, 128, ⟨-1791316249545151647293539304468471229190234709330, -1791316249545151647293539304468471229190232612177⟩, ⟨-1791316249545151647293539304468471225444812231754, -1791316249545151647293539304468471225444810134601⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2279803243473092718709542626208941394930165743324, 2279803243473092718709542626208941394930165743325⟩
def centerBExp : DyadicInterval precision := ⟨64548078255749931605311701267068161603434572025, 64548078255749931605311701267068163802457827578⟩
def centerBLog : DyadicInterval precision := ⟨63163302685366144501888699574856781397033958764, 63163302685366144501888699574856783596057214317⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨64548078255749931605311701267068162153190385913, scale precision, 64548078255749931605311701267068163252702013690, scale precision,
    4, 128, 4, 128, ⟨-4559606486946185437419085252417882802307938162576, -4559606486946185437419085252417882802307936065423⟩, ⟨-4559606486946185437419085252417882777412726907897, -4559606486946185437419085252417882777412724810744⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨889188605951130351749647091089586658568328333782, 902148905794955578792513600477775557702074971439⟩
def wholeCExp : DyadicInterval precision := ⟨425246518556635144039726924839706188301875195797, 432855796236656493485137146144871724757144017507⟩
def wholeCLog : DyadicInterval precision := ⟨373253442311315541391189573349794650484012030449, 379135841804426944490360837677073937026251291229⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨425246518556635144039726924839706188851631009685, scale precision, 432855796236656493485137146144871724207388203619, scale precision,
    1, 128, 1, 128, ⟨-1804297811589911157585027200955551117293570391892, -1804297811589911157585027200955551117293568294739⟩, ⟨-1778377211902260703499294182179173315280452880455, -1778377211902260703499294182179173315280450783302⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2261226943925830193632120433265442518555594234644, 2298404673296085140024593959919412400785099151859⟩
def wholeBExp : DyadicInterval precision := ⟨62925728353908903186999031791341686647936990687, 66209978573012859734334989613692278441068889569⟩
def wholeBLog : DyadicInterval precision := ⟨61608747644797353721615072396095945554078486029, 64754042766785952094515283043041247544113476210⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨62925728353908903186999031791341687197692804575, scale precision, 66209978573012859734334989613692277891313075681, scale precision,
    4, 128, 4, 128, ⟨-4596809346592170280049187919838824814338728905281, -4596809346592170280049187919838824814338726808128⟩, ⟨-4522453887851660387264240866530885024976024404586, -4522453887851660387264240866530885024976022307433⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0210StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0211StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0211StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨883173091136431819050333806052124777584860035603, 883173091136431819050333806052124777584860035604⟩
def centerCExp : DyadicInterval precision := ⟨436433756410544946825558187930340396760038148131, 436433756410544946825558187930340398959061403684⟩
def centerCLog : DyadicInterval precision := ⟨381893643715920133111977718562129382349475897433, 381893643715920133111977718562129384548499152986⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨436433756410544946825558187930340397309793962019, scale precision, 436433756410544946825558187930340398409305589796, scale precision,
    1, 128, 1, 128, ⟨-1766346182272863638100667612104249557010708463977, -1766346182272863638100667612104249557010706366824⟩, ⟨-1766346182272863638100667612104249553328733775592, -1766346182272863638100667612104249553328731678439⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2243310474445991562937303596304065392975122403484, 2243310474445991562937303596304065392975122403485⟩
def centerBExp : DyadicInterval precision := ⟨67853371604551508631003355406199365181936513366, 67853371604551508631003355406199367380959768919⟩
def centerBLog : DyadicInterval precision := ⟨66325367263425248453251078629684949808844200296, 66325367263425248453251078629684952007867455849⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨67853371604551508631003355406199365731692327254, scale precision, 67853371604551508631003355406199366831203955031, scale precision,
    4, 128, 4, 128, ⟨-4486620948891983125874607192608130797791500064876, -4486620948891983125874607192608130797791497967723⟩, ⟨-4486620948891983125874607192608130774108991646198, -4486620948891983125874607192608130774108989549045⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨876744383355288652573481314946293264353499645229, 889622866940560267078565450060948161603839887113⟩
def wholeCExp : DyadicInterval precision := ⟨432598640801811646550421823182324846484528718053, 440290177423607948156722745983572317329430107133⟩
def wholeCLog : DyadicInterval precision := ⟨378937432257190463719391371232510239341912698535, 384860260660121273067726584432245083823796370509⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨432598640801811646550421823182324847034284531941, scale precision, 440290177423607948156722745983572316779674293245, scale precision,
    1, 128, 1, 128, ⟨-1779245733881120534157130900121896325064989067324, -1779245733881120534157130900121896325064986970171⟩, ⟨-1753488766710577305146962629892586526882137865765, -1753488766710577305146962629892586526882135768612⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2224786351525314029832842569631773499938251714634, 2261861606037031545745500091786984997827912753706⟩
def wholeBExp : DyadicInterval precision := ⟨66152499715317387072175205649539328670267433018, 69595402947850876215036433225102207420128763654⟩
def wholeBLog : DyadicInterval precision := ⟨64699053969086271720122973528557655134449333982, 67989161954233009775553585338304573998947759305⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66152499715317387072175205649539329220023246906, scale precision, 69595402947850876215036433225102206870372949766, scale precision,
    4, 128, 4, 128, ⟨-4523723212074063091491000183573970007801535721748, -4523723212074063091491000183573970007801533624595⟩, ⟨-4449572703050628059665685139263546988331646799069, -4449572703050628059665685139263546988331644701916⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0211StableWitnesses

end


