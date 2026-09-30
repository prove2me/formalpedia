-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0471StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:23:35.736896+00:00
-- url     : https://prove2.me/theorems/dab0e402-218e-4c1a-8ad3-7517a6a5fe07
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0471StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0472StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0471StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0472StableWitnesses, GeneralCK.Certificates.E8TAxisProd0473StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0471StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0472StableWitnesses, GeneralCK.Certificates.E8TAxisProd0473StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0471StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0472StableWitnesses, GeneralCK.Certificates.E8TAxisProd0473StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0471StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0472StableWitnesses, GeneralCK/Certificates/E8TAxisProd0473StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0471StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0471StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨626927138186391955070253028259319758527712060839, 626927138186391955070253028259319758527712060840⟩
def centerCExp : DyadicInterval precision := ⟨619738611456628435274276368095743364686373156155, 619738611456628435274276368095743366885396411708⟩
def centerCLog : DyadicInterval precision := ⟨516640190984491544400093836846259741260716494074, 516640190984491544400093836846259743459739749627⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨619738611456628435274276368095743365236128970043, scale precision, 619738611456628435274276368095743366335640597820, scale precision,
    1, 128, 1, 128, ⟨-1253854276372783910140506056518639518351889530031, -1253854276372783910140506056518639518351887432878⟩, ⟨-1253854276372783910140506056518639515758960810480, -1253854276372783910140506056518639515758958713327⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1482503195716967650320233346050338610476558445679, 1482503195716967650320233346050338610476558445680⟩
def centerBExp : DyadicInterval precision := ⟨192189142847568526624347625588002784818848324955, 192189142847568526624347625588002787017871580508⟩
def centerBLog : DyadicInterval precision := ⟨180561512833991198088128340867839795749348734896, 180561512833991198088128340867839797948371990449⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨192189142847568526624347625588002785368604138843, scale precision, 192189142847568526624347625588002786468115766620, scale precision,
    2, 128, 2, 128, ⟨-2965006391433935300640466692100677225133734025869, -2965006391433935300640466692100677225133731928716⟩, ⟨-2965006391433935300640466692100677216772501854003, -2965006391433935300640466692100677216772499756850⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨621283350039900454734590019789528943723343819777, 632586654082386112450412133695484089759159199206⟩
def wholeCExp : DyadicInterval precision := ⟨614957401088405087699137369838788726775725485064, 624543553062544341732808990290069165405422357065⟩
def wholeCLog : DyadicInterval precision := ⟨513278836841669367717574300249483875252019574106, 520010458386995974251610051426834524705408407552⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨614957401088405087699137369838788727325481298952, scale precision, 624543553062544341732808990290069164855666543177, scale precision,
    1, 128, 1, 128, ⟨-1265173308164772224900824267390968180824863641283, -1265173308164772224900824267390968180824861544130⟩, ⟨-1242566700079800909469180039579057886160198709666, -1242566700079800909469180039579057886160196612513⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1466286890351474529083091817859121200152972898411, 1498798612743471147236477134000746644511277838494⟩
def wholeBExp : DyadicInterval precision := ⟨187950842494332430779050251580904748095891836030, 196501742487967651388485619595300737713078289900⟩
def wholeBLog : DyadicInterval precision := ⟨176810972322998651792047309904725325407787186845, 184367948267892572120640564161991137613920908757⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨187950842494332430779050251580904748645647649918, scale precision, 196501742487967651388485619595300737163322476012, scale precision,
    2, 128, 2, 128, ⟨-2997597225486942294472954268001493293297445901201, -2997597225486942294472954268001493293297443804048⟩, ⟨-2932573780702949058166183635718242396217082227930, -2932573780702949058166183635718242396217080130777⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0471StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0472StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0472StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨654373479606638252589496685135113086385905445322, 654373479606638252589496685135113086385905445323⟩
def centerDExp : DyadicInterval precision := ⟨596893494903452163994038347155718252372053594473, 596893494903452163994038347155718254571076850026⟩
def centerDLog : DyadicInterval precision := ⟨500509053273440340443871498920685505225663393173, 500509053273440340443871498920685507424686648726⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨596893494903452163994038347155718252921809408361, scale precision, 596893494903452163994038347155718254021321036138, scale precision,
    1, 128, 1, 128, ⟨-1308746959213276505178993370270226174117896339520, -1308746959213276505178993370270226174117894242367⟩, ⟨-1308746959213276505178993370270226171425727538920, -1308746959213276505178993370270226171425725441767⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨659579761859087400149892520836293489417575912147, 659579761859087400149892520836293489417575912148⟩
def centerCExp : DyadicInterval precision := ⟨592656001031131836196676112984964860246257768465, 592656001031131836196676112984964862445281024018⟩
def centerCLog : DyadicInterval precision := ⟨497497246850645038264895654818957379568620133024, 497497246850645038264895654818957381767643388577⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨592656001031131836196676112984964860796013582353, scale precision, 592656001031131836196676112984964861895525210130, scale precision,
    1, 128, 1, 128, ⟨-1319159523718174800299785041672586980190861784505, -1319159523718174800299785041672586980190859687352⟩, ⟨-1319159523718174800299785041672586977479443961240, -1319159523718174800299785041672586977479441864087⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1579141278073079290453961094684530475612443622430, 1579141278073079290453961094684530475612443622431⟩
def centerBExp : DyadicInterval precision := ⟨168381979797490220852577044944856051756296976327, 168381979797490220852577044944856053955320231880⟩
def centerBLog : DyadicInterval precision := ⟨159368256172511997226669804967252147944310447909, 159368256172511997226669804967252150143333703462⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨168381979797490220852577044944856052306052790215, scale precision, 168381979797490220852577044944856053405564417992, scale precision,
    3, 128, 3, 128, ⟨-3158282556146158580907922189369060955996592623651, -3158282556146158580907922189369060955996590526498⟩, ⟨-3158282556146158580907922189369060946453183963216, -3158282556146158580907922189369060946453181866063⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458569907208, 659917674403335303398947154306570012946022027568⟩
def wholeDExp : DyadicInterval precision := ⟨592382009410612930615839145836493981094734824913, 601426740197304508434017275821189107729148063965⟩
def wholeDLog : DyadicInterval precision := ⟨497302293015079090720897450218278677548754229682, 503724208829984298099852655433700222030834719032⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨592382009410612930615839145836493981644490638801, scale precision, 601426740197304508434017275821189107179392250077, scale precision,
    1, 128, 1, 128, ⟨-1319835348806670606797894308613140027248381064907, -1319835348806670606797894308613140027248378967754⟩, ⟨-1297689185454824353294856041553732547581202554253, -1297689185454824353294856041553732547581200457100⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨653843969421245541837132973581687857387168975506, 665332069838523774458374403334431477573278680817⟩
def wholeCExp : DyadicInterval precision := ⟨588009058598433817213696549564095295848345414379, 597326167321274749556343269918222906334796950442⟩
def wholeCLog : DyadicInterval precision := ⟨494187273274007061243092561185882271821086404499, 500816227045226244175523267872891557888414766811⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨588009058598433817213696549564095296398101228267, scale precision, 597326167321274749556343269918222905785041136554, scale precision,
    1, 128, 1, 128, ⟨-1330664139677047548916748806668862956512981274587, -1330664139677047548916748806668862956512979177434⟩, ⟨-1307687938842491083674265947163375713429229633741, -1307687938842491083674265947163375713429227536588⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1562476086449565366661337867154286308443342063328, 1595879221200114006908024192304002937959226794494⟩
def wholeBExp : DyadicInterval precision := ⟨164569003578971258843155232517907579238686007341, 172266149456677795668291256452901764129528324381⟩
def wholeBLog : DyadicInterval precision := ⟨155945189942259527117746601938382153390227397774, 162847011893758190924076478570162133426979047967⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨164569003578971258843155232517907579788441821229, scale precision, 172266149456677795668291256452901763579772510493, scale precision,
    3, 128, 3, 128, ⟨-3191758442400228013816048384608005880800716817296, -3191758442400228013816048384608005880800714720143⟩, ⟨-3124952172899130733322675734308572612222570811129, -3124952172899130733322675734308572612222568713976⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0472StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0473StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0473StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨643330890011571853191447487766205018317129467057, 643330890011571853191447487766205018317129467058⟩
def centerDExp : DyadicInterval precision := ⟨605981822530277187962366989116632506149582094264, 605981822530277187962366989116632508348605349817⟩
def centerDLog : DyadicInterval precision := ⟨506947743551831449885580746844042863375923706013, 506947743551831449885580746844042865574946961566⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨605981822530277187962366989116632506699337908152, scale precision, 605981822530277187962366989116632507798849535929, scale precision,
    1, 128, 1, 128, ⟨-1286661780023143706382894975532410037960156226204, -1286661780023143706382894975532410037960154129051⟩, ⟨-1286661780023143706382894975532410035308363739178, -1286661780023143706382894975532410035308361642025⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨648508543295138311207240196614030948336037531372, 648508543295138311207240196614030948336037531373⟩
def centerCExp : DyadicInterval precision := ⟨601703381137535856225822622004238737859441672419, 601703381137535856225822622004238740058464927972⟩
def centerCLog : DyadicInterval precision := ⟨503920184649912452491911021023416808299791438141, 503920184649912452491911021023416810498814693694⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨601703381137535856225822622004238738409197486307, scale precision, 601703381137535856225822622004238739508709114084, scale precision,
    1, 128, 1, 128, ⟨-1297017086590276622414480393228061898007400205083, -1297017086590276622414480393228061898007398107930⟩, ⟨-1297017086590276622414480393228061895336752017562, -1297017086590276622414480393228061895336749920409⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1546450793650391328374462964120825244763705439787, 1546450793650391328374462964120825244763705439788⟩
def centerBExp : DyadicInterval precision := ⟨176085656620996735113738322900791105623308409097, 176085656620996735113738322900791107822331664650⟩
def centerBLog : DyadicInterval precision := ⟨166259798566702731232447636397671984300262986656, 166259798566702731232447636397671986499286242209⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176085656620996735113738322900791106173064222985, scale precision, 176085656620996735113738322900791107272575850762, scale precision,
    3, 128, 3, 128, ⟨-3092901587300782656748925928241650494090356108551, -3092901587300782656748925928241650494090354011398⟩, ⟨-3092901587300782656748925928241650484964467747756, -3092901587300782656748925928241650484964465650603⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088060941844, 648844592727412176647428020776866274458569907209⟩
def wholeDExp : DyadicInterval precision := ⟨601426740197304508434017275821189105530124808412, 610558820864912509175272747825498146169006720984⟩
def wholeDLog : DyadicInterval precision := ⟨503724208829984298099852655433700219831811463479, 510179642243321146984571771117295507804948082651⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨601426740197304508434017275821189106079880622300, scale precision, 610558820864912509175272747825498145619250907096, scale precision,
    1, 128, 1, 128, ⟨-1297689185454824353294856041553732550253079171733, -1297689185454824353294856041553732550253077074580⟩, ⟨-1275664494960944649878652869905243774860166148623, -1275664494960944649878652869905243774860164051470⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨642804283485696949720313088527385772989900685978, 654229053852446988667848133809557594352805518261⟩
def wholeCExp : DyadicInterval precision := ⟨597011476725021492713305914757895052383890251356, 606418673211174923115031299917793991265764048135⟩
def wholeCLog : DyadicInterval precision := ⟨500592820321492206435592408256845577925753734765, 507256520166267712877957353476735214441710920537⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨597011476725021492713305914757895052933646065244, scale precision, 606418673211174923115031299917793990716008234247, scale precision,
    1, 128, 1, 128, ⟨-1308458107704893977335696267619115190051430471265, -1308458107704893977335696267619115190051428374112⟩, ⟨-1285608566971393899440626177054771544654861323528, -1285608566971393899440626177054771544654859226375⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1529931963585041799566182224815425274029133970706, 1563044622907844287293104039396809878921268868738⟩
def wholeBExp : DyadicInterval precision := ⟨172132175611494670117194362716041869587491502383, 180111453677423112827199908442090259259036827625⟩
def wholeBLog : DyadicInterval precision := ⟨162727159473890019091318074144283722508662779841, 169848302625479736742058629975826814171630296028⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172132175611494670117194362716041870137247316271, scale precision, 180111453677423112827199908442090258709281013737, scale precision,
    3, 128, 3, 128, ⟨-3126089245815688574586208078793619762510283321764, -3126089245815688574586208078793619762510281224611⟩, ⟨-3059863927170083599132364449630850543597314365919, -3059863927170083599132364449630850543597312268766⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0473StableWitnesses

end


