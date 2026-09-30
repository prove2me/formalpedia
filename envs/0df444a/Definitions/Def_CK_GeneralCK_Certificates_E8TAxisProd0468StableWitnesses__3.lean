-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0468StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0468StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:16:33.209181+00:00
-- url     : https://prove2.me/theorems/03f4f1e3-8923-43c0-a3bd-16cc1de1ff67
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0468StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0469StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0468StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0469StableWitnesses, GeneralCK.Certificates.E8TAxisProd0470StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0468StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0469StableWitnesses, GeneralCK.Certificates.E8TAxisProd0470StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0468StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0469StableWitnesses, GeneralCK.Certificates.E8TAxisProd0470StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0468StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0469StableWitnesses, GeneralCK/Certificates/E8TAxisProd0470StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0468StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0468StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨632348540951967311680475479396950834210417986731, 632348540951967311680475479396950834210417986732⟩
def centerDExp : DyadicInterval precision := ⟨615157815904934041673261697075548683721928749060, 615157815904934041673261697075548685920952004613⟩
def centerDLog : DyadicInterval precision := ⟨513419890646572039308129704473371304747530047246, 513419890646572039308129704473371306946553302799⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684271684562948, scale precision, 615157815904934041673261697075548685371196190725, scale precision,
    1, 128, 1, 128, ⟨-1264697081903934623360950958793901669726955551880, -1264697081903934623360950958793901669726953454727⟩, ⟨-1264697081903934623360950958793901667114718492198, -1264697081903934623360950958793901667114716395045⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨638262035702813814353993596228693397953865345650, 638262035702813814353993596228693397953865345651⟩
def centerCExp : DyadicInterval precision := ⟨610199828674026369371121662531355487208906081386, 610199828674026369371121662531355489407929336939⟩
def centerCLog : DyadicInterval precision := ⟨509926409704541577238933778378899568836151431933, 509926409704541577238933778378899571035174687486⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨610199828674026369371121662531355487758661895274, scale precision, 610199828674026369371121662531355488858173523051, scale precision,
    1, 128, 1, 128, ⟨-1276524071405627628707987192457386797224462725981, -1276524071405627628707987192457386797224460628828⟩, ⟨-1276524071405627628707987192457386794591000753774, -1276524071405627628707987192457386794590998656621⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1515172134200258065189559407530125984729765498935, 1515172134200258065189559407530125984729765498936⟩
def centerBExp : DyadicInterval precision := ⟨183786363761661735930952960407179320957729106132, 183786363761661735930952960407179323156752361685⟩
def centerBLog : DyadicInterval precision := ⟨173116359188538219297049551017890702908314621770, 173116359188538219297049551017890705107337877323⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨183786363761661735930952960407179321507484920020, scale precision, 183786363761661735930952960407179322606996547797, scale precision,
    2, 128, 2, 128, ⟨-3030344268400516130379118815060251973831287413305, -3030344268400516130379118815060251973831285316152⟩, ⟨-3030344268400516130379118815060251965087776679590, -3030344268400516130379118815060251965087774582437⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408842647972, 637832247480472324939326434952621888088060941845⟩
def wholeDExp : DyadicInterval precision := ⟨610558820864912509175272747825498143969983465431, 619778890111929048152500802482413364610095309026⟩
def wholeDLog : DyadicInterval precision := ⟨510179642243321146984571771117295505605924827098, 516668475441837355502384214637433235544606836387⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498144519739279319, scale precision, 619778890111929048152500802482413364060339495138, scale precision,
    1, 128, 1, 128, ⟨-1275664494960944649878652869905243777492079715909, -1275664494960944649878652869905243777492077618756⟩, ⟨-1253759292121867631798962652155400921521306240344, -1253759292121867631798962652155400921521304143191⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨632586654082386112450412133695484089759159199205, 643953420834745641452672802241764577235941032281⟩
def wholeCExp : DyadicInterval precision := ⟨605465802963376776924971461867485546149304392861, 614957401088405087699137369838788728974748740617⟩
def wholeCLog : DyadicInterval precision := ⟨506582924394923643538958786868765081130687592946, 513278836841669367717574300249483877451042829659⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨605465802963376776924971461867485546699060206749, scale precision, 614957401088405087699137369838788728424992926729, scale precision,
    1, 128, 1, 128, ⟨-1287906841669491282905345604483529155798909376549, -1287906841669491282905345604483529155798907279396⟩, ⟨-1265173308164772224900824267390968178211775252695, -1265173308164772224900824267390968178211773155542⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1498798612743471147236477134000746644511277838493, 1531622718624734991807995553060516857443651820427⟩
def wholeBExp : DyadicInterval precision := ⟨179695207373922274782779572367692429798226271963, 187950842494332430779050251580904750294915091583⟩
def wholeBLog : DyadicInterval precision := ⟨169477678270568731895752919048661809916471591358, 176810972322998651792047309904725327606810442398⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨179695207373922274782779572367692430347982085851, scale precision, 187950842494332430779050251580904749745159277695, scale precision,
    3, 128, 2, 128, ⟨-3063245437249469983615991106121033719358592676857, -3063245437249469983615991106121033719358590579704⟩, ⟨-2997597225486942294472954268001493284747667549934, -2997597225486942294472954268001493284747665452781⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0468StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0469StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0469StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨621425438279266372444929921138880061854681288003, 621425438279266372444929921138880061854681288004⟩
def centerDExp : DyadicInterval precision := ⟨624422127721977427615890341813457419000892162445, 624422127721977427615890341813457421199915417998⟩
def centerDLog : DyadicInterval precision := ⟨519925384247664018477884675236132695692606507204, 519925384247664018477884675236132697891629762757⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨624422127721977427615890341813457419550647976333, scale precision, 624422127721977427615890341813457420650159604110, scale precision,
    1, 128, 1, 128, ⟨-1242850876558532744889859842277760124996103774330, -1242850876558532744889859842277760124996101677177⟩, ⟨-1242850876558532744889859842277760122422623474837, -1242850876558532744889859842277760122422621377684⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨627307115179953991283528024064700046038077023944, 627307115179953991283528024064700046038077023945⟩
def centerCExp : DyadicInterval precision := ⟨619416442538484021370017780483910460201672662699, 619416442538484021370017780483910462400695918252⟩
def centerCLog : DyadicInterval precision := ⟨516413937985385919527976722526694160227014953832, 516413937985385919527976722526694162426038209385⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨619416442538484021370017780483910460751428476587, scale precision, 619416442538484021370017780483910461850940104364, scale precision,
    1, 128, 1, 128, ⟨-1254614230359907982567056048129400093373293769177, -1254614230359907982567056048129400093373291672024⟩, ⟨-1254614230359907982567056048129400090779016423753, -1254614230359907982567056048129400090779014326600⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1483059003522856922763036807434599411456484154948, 1483059003522856922763036807434599411456484154949⟩
def centerBExp : DyadicInterval precision := ⟨192043019696238998461724142585177278843855141936, 192043019696238998461724142585177281042878397489⟩
def centerBLog : DyadicInterval precision := ⟨180432366162026734369487992062256963258931204927, 180432366162026734369487992062256965457954460480⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨192043019696238998461724142585177279393610955824, scale precision, 192043019696238998461724142585177280493122583601, scale precision,
    2, 128, 2, 128, ⟨-2966118007045713845526073614869198827096766423325, -2966118007045713845526073614869198827096764326172⟩, ⟨-2966118007045713845526073614869198818729172293623, -2966118007045713845526073614869198818729170196470⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879788980549, 626879646060933815899481326077700461408842647973⟩
def wholeDExp : DyadicInterval precision := ⟨619778890111929048152500802482413362411072053473, 629087614762237432177832619094338713110027667137⟩
def wholeDLog : DyadicInterval precision := ⟨516668475441837355502384214637433233345583580834, 523190605620864448684409715253755541203210012554⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨619778890111929048152500802482413362960827867361, scale precision, 629087614762237432177832619094338712560271853249, scale precision,
    1, 128, 1, 128, ⟨-1253759292121867631798962652155400924114066448699, -1253759292121867631798962652155400924114064351546⟩, ⟨-1231971585870689408193430922761488484482381679326, -1231971585870689408193430922761488484482379582173⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨621662274035242301718893572501174643647458594027, 632967693355213703396633370831003409958672336575⟩
def wholeCExp : DyadicInterval precision := ⟨614636824178406847520978180274332687622115007930, 624219785800907859695879263770915378089138958529⟩
def wholeCLog : DyadicInterval precision := ⟨513053183534412058176688768231267987563834835948, 519783606586412607142268410211409487754237772381⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨614636824178406847520978180274332688171870821818, scale precision, 624219785800907859695879263770915377539383144641, scale precision,
    1, 128, 1, 128, ⟨-1265935386710427406793266741662006821224571371937, -1265935386710427406793266741662006821224569274784⟩, ⟨-1243324548070484603437787145002349286007760987845, -1243324548070484603437787145002349286007758890692⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1466839977240481527013300992531075887191516369233, 1499357107615000298325434845275701205695370142272⟩
def wholeBExp : DyadicInterval precision := ⟨187807251168349206166702629534087487162010906729, 196353071538172995624826348123512807583988302170⟩
def wholeBLog : DyadicInterval precision := ⟨176683737318867307572247752104837152830370599735, 184236891491105114564864854703015354402318219290⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨187807251168349206166702629534087487711766720617, scale precision, 196353071538172995624826348123512807034232488282, scale precision,
    2, 128, 2, 128, ⟨-2998714215230000596650869690551402415668898950205, -2998714215230000596650869690551402415668896853052⟩, ⟨-2933679954480963054026601985062151770291073239467, -2933679954480963054026601985062151770291071142314⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0469StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0470StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0470StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨632348540951967311680475479396950834210417986731, 632348540951967311680475479396950834210417986732⟩
def centerDExp : DyadicInterval precision := ⟨615157815904934041673261697075548683721928749060, 615157815904934041673261697075548685920952004613⟩
def centerDLog : DyadicInterval precision := ⟨513419890646572039308129704473371304747530047246, 513419890646572039308129704473371306946553302799⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684271684562948, scale precision, 615157815904934041673261697075548685371196190725, scale precision,
    1, 128, 1, 128, ⟨-1264697081903934623360950958793901669726955551880, -1264697081903934623360950958793901669726953454727⟩, ⟨-1264697081903934623360950958793901667114718492198, -1264697081903934623360950958793901667114716395045⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨637879997208799531306517231422903422230879290706, 637879997208799531306517231422903422230879290707⟩
def centerCExp : DyadicInterval precision := ⟨610518926191394337456078262550340333057624955515, 610518926191394337456078262550340335256648211068⟩
def centerCLog : DyadicInterval precision := ⟨510151502769037790620516601343852836391781080670, 510151502769037790620516601343852838590804336223⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨610518926191394337456078262550340333607380769403, scale precision, 610518926191394337456078262550340334706892397180, scale precision,
    1, 128, 1, 128, ⟨-1275759994417599062613034462845806845777802405506, -1275759994417599062613034462845806845777800308353⟩, ⟨-1275759994417599062613034462845806843145716854473, -1275759994417599062613034462845806843145714757320⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1514611077389523314662541618778187192213654342844, 1514611077389523314662541618778187192213654342845⟩
def centerBExp : DyadicInterval precision := ⟨183927525678054794834457293928526694184542546105, 183927525678054794834457293928526696383565801658⟩
def centerBLog : DyadicInterval precision := ⟨173241747279811690468761493295161233410375807060, 173241747279811690468761493295161235609399062613⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨183927525678054794834457293928526694734298359993, scale precision, 183927525678054794834457293928526695833809987770, scale precision,
    2, 128, 2, 128, ⟨-3029222154779046629325083237556374388795709837341, -3029222154779046629325083237556374388795707740188⟩, ⟨-3029222154779046629325083237556374380058909631192, -3029222154779046629325083237556374380058907534039⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408842647972, 637832247480472324939326434952621888088060941845⟩
def wholeDExp : DyadicInterval precision := ⟨610558820864912509175272747825498143969983465431, 619778890111929048152500802482413364610095309026⟩
def wholeDLog : DyadicInterval precision := ⟨510179642243321146984571771117295505605924827098, 516668475441837355502384214637433235544606836387⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498144519739279319, scale precision, 619778890111929048152500802482413364060339495138, scale precision,
    1, 128, 1, 128, ⟨-1275664494960944649878652869905243777492079715909, -1275664494960944649878652869905243777492077618756⟩, ⟨-1253759292121867631798962652155400921521306240344, -1253759292121867631798962652155400921521304143191⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨632205686514054014973477281022546712202048803961, 643570302158419402762879584302270293330774637332⟩
def wholeCExp : DyadicInterval precision := ⟨605783320329306778067622524559805831717693208923, 615278084828305768807811408752816925481732832671⟩
def wholeCLog : DyadicInterval precision := ⟨506807415841710827876377431725930570823300484251, 513504530493722425503735242902309430684727481128⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨605783320329306778067622524559805832267449022811, scale precision, 615278084828305768807811408752816924931977018783, scale precision,
    1, 128, 1, 128, ⟨-1287140604316838805525759168604540587987881034513, -1287140604316838805525759168604540587987878937360⟩, ⟨-1264411373028108029946954562045093423098235434742, -1264411373028108029946954562045093423098233337589⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1498240209165424724988809637242899970684243967136, 1531059044732848403809149521898466992152956339307⟩
def wholeBExp : DyadicInterval precision := ⟨179833871019339745830008048921670439986930644336, 188094520106729574409737325373892969791358509473⟩
def wholeBLog : DyadicInterval precision := ⟨169601154369591997507405827222391079311448403704, 176938272698947761433232776198593086544148081026⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨179833871019339745830008048921670440536686458224, scale precision, 188094520106729574409737325373892969241602695585, scale precision,
    3, 128, 2, 128, ⟨-3062118089465696807618299043796933988773754059918, -3062118089465696807618299043796933988773751962765⟩, ⟨-2996480418330849449977619274485799937096865217980, -2996480418330849449977619274485799937096863120827⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0470StableWitnesses

end


