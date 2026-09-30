-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0501StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0501StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:35:32.945624+00:00
-- url     : https://prove2.me/theorems/295c6fc8-2469-4225-8bc3-5243afc8d9d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0501StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisProd0502StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0501StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisProd0502StableWitnesses, GeneralCK.Certificates.E8TAxisProd0503StableWitnesses, GeneralCK.Certificates.E8TAxisProd0504StableWitnesses, GeneralCK.Certificates.E8TAxisProd0505StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0501StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisProd0502StableWitnesses, GeneralCK.Certificates.E8TAxisProd0503StableWitnesses, GeneralCK.Certificates.E8TAxisProd0504StableWitnesses, GeneralCK.Certificates.E8TAxisProd0505StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0501StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisProd0502StableWitnesses, GeneralCK.Certificates.E8TAxisProd0503StableWitnesses, GeneralCK.Certificates.E8TAxisProd0504StableWitnesses, GeneralCK.Certificates.E8TAxisProd0505StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0501StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisProd0502StableWitnesses, GeneralCK/Certificates/E8TAxisProd0503StableWitnesses, GeneralCK/Certificates/E8TAxisProd0504StableWitnesses, GeneralCK/Certificates/E8TAxisProd0505StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0501StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0501StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨625787633523397854220155343330735517858765174712, 625787633523397854220155343330735517858765174713⟩
def centerCExp : DyadicInterval precision := ⟨620705761834721880248997022587296383417417343777, 620705761834721880248997022587296385616440599330⟩
def centerCLog : DyadicInterval precision := ⟨517319191661850012208605048296712578797336571314, 517319191661850012208605048296712580996359826867⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨620705761834721880248997022587296383967173157665, scale precision, 620705761834721880248997022587296385066684785442, scale precision,
    1, 128, 1, 128, ⟨-1251575267046795708440310686661471037011975676650, -1251575267046795708440310686661471037011973579497⟩, ⟨-1251575267046795708440310686661471034423087119355, -1251575267046795708440310686661471034423085022202⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1480836327282882749009959670039871488024797854240, 1480836327282882749009959670039871488024797854241⟩
def centerBExp : DyadicInterval precision := ⟨192628033444435979414754817378398385390344782149, 192628033444435979414754817378398387589368037702⟩
def centerBLog : DyadicInterval precision := ⟨180949344845556442915907033376163912450747766474, 180949344845556442915907033376163914649771022027⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨192628033444435979414754817378398385940100596037, scale precision, 192628033444435979414754817378398387039612223814, scale precision,
    2, 128, 2, 128, ⟨-2961672654565765498019919340079742980220687577865, -2961672654565765498019919340079742980220685480712⟩, ⟨-2961672654565765498019919340079742971878505936251, -2961672654565765498019919340079742971878503839098⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨620147000625435167268220529674147902694474565282, 631443966323288810080153350465840136918934305191⟩
def wholeCExp : DyadicInterval precision := ⟨615919772910066643020626982422751038456348901908, 625515501058813146130620533630963153356492092924⟩
def wholeCLog : DyadicInterval precision := ⟨513956038814922220835639008241075999122479327844, 520691255126520165462341919941114714931158351803⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨615919772910066643020626982422751039006104715796, scale precision, 625515501058813146130620533630963152806736279036, scale precision,
    1, 128, 1, 128, ⟨-1262887932646577620160306700931680275142372383936, -1262887932646577620160306700931680275142370286783⟩, ⟨-1240294001250870334536441059348295804104459194075, -1240294001250870334536441059348295804104457096922⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1464628191474595856146348944423271746888965021500, 1497123676053440205135470205913651314011892645190⟩
def wholeBExp : DyadicInterval precision := ⟨188382134268756602102177682084215228644905131612, 196948279674787721664414623367534027643348942285⟩
def wholeBLog : DyadicInterval precision := ⟨177193069563197443997018860725128597926453640820, 184761510169840793488040226900295537388432040710⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨188382134268756602102177682084215229194660945500, scale precision, 196948279674787721664414623367534027093593128397, scale precision,
    2, 128, 2, 128, ⟨-2994247352106880410270940411827302632288888362819, -2994247352106880410270940411827302632288886265666⟩, ⟨-2929256382949191712292697888846543489698337081127, -2929256382949191712292697888846543489698334983974⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0501StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0502StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0502StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨636352565668236199839542689727199316860771086513, 636352565668236199839542689727199316860771086514⟩
def centerCExp : DyadicInterval precision := ⟨611796380985325269136056771644269248137919170008, 611796380985325269136056771644269250336942425561⟩
def centerCLog : DyadicInterval precision := ⟨511052279052061021045313602429445341557232976129, 511052279052061021045313602429445343756256231682⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨611796380985325269136056771644269248687674983896, scale precision, 611796380985325269136056771644269249787186611673, scale precision,
    1, 128, 1, 128, ⟨-1272705131336472399679085379454398635034838048286, -1272705131336472399679085379454398635034835951133⟩, ⟨-1272705131336472399679085379454398632408248394924, -1272705131336472399679085379454398632408246297771⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1512367751751378521935765076296113974168487962840, 1512367751751378521935765076296113974168487962841⟩
def centerBExp : DyadicInterval precision := ⟨184493030778921765402136612439325713977827931621, 184493030778921765402136612439325716176851187174⟩
def centerBLog : DyadicInterval precision := ⟨173743953426072440685616183495623705089127667714, 173743953426072440685616183495623707288150923267⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨184493030778921765402136612439325714527583745509, scale precision, 184493030778921765402136612439325715627095373286, scale precision,
    2, 128, 2, 128, ⟨-3024735503502757043871530152592227952691987126882, -3024735503502757043871530152592227952691985029729⟩, ⟨-3024735503502757043871530152592227943981966821638, -3024735503502757043871530152592227943981964724485⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨630682532447705272568064943199114446114497262136, 642038556107706771519437909253661699708218268493⟩
def wholeCExp : DyadicInterval precision := ⟨607054450472385817399100603070939273026933256050, 616561888648609682612590672722236082814917503703⟩
def wholeCLog : DyadicInterval precision := ⟨507705786365840927233039466663271107965301345026, 514407708463644061462437028091316654051443815520⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨607054450472385817399100603070939273576689069938, scale precision, 616561888648609682612590672722236082265161689815, scale precision,
    1, 128, 1, 128, ⟨-1284077112215413543038875818507323400739991051820, -1284077112215413543038875818507323400739988954667⟩, ⟨-1261365064895410545136129886398228890925851416646, -1261365064895410545136129886398228890925849319493⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1496007508605897899776464737226725573616869202727, 1528805238241515381407522062180279457224473427590⟩
def wholeBExp : DyadicInterval precision := ⟨180389376966321532756749657576281889703482492408, 188670093810116829211011627198871721851175938718⟩
def wholeBLog : DyadicInterval precision := ⟨170095712301070591920436434725734273033783840014, 177448127905035425609773373983425725066524354857⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨180389376966321532756749657576281890253238306296, scale precision, 188670093810116829211011627198871721301420124830, scale precision,
    3, 128, 2, 128, ⟨-3057610476483030762815044124360558918903029599929, -3057610476483030762815044124360558918903027502776⟩, ⟨-2992015017211795799552929474453451142975147083060, -2992015017211795799552929474453451142975144985907⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0502StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0503StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0503StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨625407940601788738278269086072024053403019371504, 625407940601788738278269086072024053403019371505⟩
def centerCExp : DyadicInterval precision := ⟨621028359931025540996501172428923668384493894730, 621028359931025540996501172428923670583517150283⟩
def centerCLog : DyadicInterval precision := ⟨517545605767716570642713187396517030620433426124, 517545605767716570642713187396517032819456681677⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨621028359931025540996501172428923668934249708618, scale precision, 621028359931025540996501172428923670033761336395, scale precision,
    1, 128, 1, 128, ⟨-1250815881203577476556538172144048108099811660908, -1250815881203577476556538172144048108099809563755⟩, ⟨-1250815881203577476556538172144048105512267922263, -1250815881203577476556538172144048105512265825110⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1480280889597626473222745787495998775892556293874, 1480280889597626473222745787495998775892556293875⟩
def centerBExp : DyadicInterval precision := ⟨192774504086386616343802446982779581121615002470, 192774504086386616343802446982779583320638258023⟩
def centerBLog : DyadicInterval precision := ⟨181078752841626763004002619937433910553288566466, 181078752841626763004002619937433912752311822019⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨192774504086386616343802446982779581671370816358, scale precision, 192774504086386616343802446982779582770882444135, scale precision,
    2, 128, 2, 128, ⟨-2960561779195252946445491574991997555953035249914, -2960561779195252946445491574991997555953033152761⟩, ⟨-2960561779195252946445491574991997547617192022740, -2960561779195252946445491574991997547617189925587⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨619768358204472053069880958419278713734905123126, 631063213617052482596365474153866441891585767493⟩
def wholeCExp : DyadicInterval precision := ⟨616240777308156875716256065274209978177762319659, 625839699225833222945352786936769250866567172537⟩
def wholeCLog : DyadicInterval precision := ⟨514181853475477112667501827515251921778521689789, 520918267806775538561289918659906467932159240406⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨616240777308156875716256065274209978727518133547, scale precision, 625839699225833222945352786936769250316811358649, scale precision,
    1, 128, 1, 128, ⟨-1262126427234104965192730948307732885086995783383, -1262126427234104965192730948307732885086993686230⟩, ⟨-1239536716408944106139761916838557426185985703191, -1239536716408944106139761916838557426185983606038⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1464075479239015014715438862741379860894144557563, 1496565546601214938744607001064488393205083070375⟩
def wholeBExp : DyadicInterval precision := ⟨188526070857308122758872876189931117413206920860, 197097300242025195590307555409347233618274201179⟩
def wholeBLog : DyadicInterval precision := ⟨177320566049852779622305800641112054275612712034, 184892827984385156534905626802871803869241105154⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨188526070857308122758872876189931117962962734748, scale precision, 197097300242025195590307555409347233068518387291, scale precision,
    2, 128, 2, 128, ⟨-2993131093202429877489214002128976790672012877174, -2993131093202429877489214002128976790672010780021⟩, ⟨-2928150958478030029430877725482759717711780636966, -2928150958478030029430877725482759717711778539813⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0503StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0504StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0504StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨658035746130957653293239497840058411916822248170, 658035746130957653293239497840058411916822248171⟩
def centerCExp : DyadicInterval precision := ⟨593909557754456609419092873281990548128310955383, 593909557754456609419092873281990550327334210936⟩
def centerCLog : DyadicInterval precision := ⟨498388861194971071716991204787252117310153127642, 498388861194971071716991204787252119509176383195⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨593909557754456609419092873281990548678066769271, scale precision, 593909557754456609419092873281990549777578397048, scale precision,
    1, 128, 1, 128, ⟨-1316071492261915306586478995680116825186492980421, -1316071492261915306586478995680116825186490883268⟩, ⟨-1316071492261915306586478995680116822480798109411, -1316071492261915306586478995680116822480796012258⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1576857957181083848070257187888179196795715580876, 1576857957181083848070257187888179196795715580877⟩
def centerBExp : DyadicInterval precision := ⟨168908932858152414707627567452642325404924108004, 168908932858152414707627567452642327603947363557⟩
def centerBLog : DyadicInterval precision := ⟨159840693764589695136086148017921270659022480898, 159840693764589695136086148017921272858045736451⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨168908932858152414707627567452642325954679921892, scale precision, 168908932858152414707627567452642327054191549669, scale precision,
    3, 128, 3, 128, ⟨-3153715914362167696140514375776358398348250032419, -3153715914362167696140514375776358398348247935266⟩, ⟨-3153715914362167696140514375776358388834614388235, -3153715914362167696140514375776358388834612291082⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨652304371507745325717206333434171699804581453401, 663783599519049857841775919016609371875526963557⟩
def wholeCExp : DyadicInterval precision := ⟨589256378381469864148853767327750516563601325174, 598585983337739835606422266214440969926664386671⟩
def wholeCLog : DyadicInterval precision := ⟨495076463758639930681622557628266368893214847405, 501710260079697744030511740788522869329942263091⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨589256378381469864148853767327750517113357139062, scale precision, 598585983337739835606422266214440969376908572783, scale precision,
    1, 128, 1, 128, ⟨-1327567199038099715683551838033218745114585438164, -1327567199038099715683551838033218745114583341011⟩, ⟨-1304608743015490651434412666868343398266885578512, -1304608743015490651434412666868343398266883481359⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1560202804951297029128873659482932888130390501906, 1593586020583485385273734162987893917601500901205⟩
def wholeBExp : DyadicInterval precision := ⟨165086255838201970939638484960698548459331926498, 172802884001974606575684170562900639372979860654⟩
def wholeBLog : DyadicInterval precision := ⟨156410018956575553590368168631115389572347579024, 163327073746653659407470183565768383114490339531⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨165086255838201970939638484960698549009087740386, scale precision, 172802884001974606575684170562900638823224046766, scale precision,
    3, 128, 3, 128, ⟨-3187172041166970770547468325975787840069967808493, -3187172041166970770547468325975787840069965711340⟩, ⟨-3120405609902594058257747318965865771611154664687, -3120405609902594058257747318965865771611152567534⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0504StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0505StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0505StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨646973032980419367680550213130115210477233824457, 646973032980419367680550213130115210477233824458⟩
def centerCExp : DyadicInterval precision := ⟨602969056266196988326080060067867148565077643286, 602969056266196988326080060067867150764100898839⟩
def centerCLog : DyadicInterval precision := ⟨504816469367936313368139357601862081211693367103, 504816469367936313368139357601862083410716622656⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨602969056266196988326080060067867149114833457174, scale precision, 602969056266196988326080060067867150214345084951, scale precision,
    1, 128, 1, 128, ⟨-1293946065960838735361100426260230422286989850576, -1293946065960838735361100426260230422286987753423⟩, ⟨-1293946065960838735361100426260230419621947544407, -1293946065960838735361100426260230419621945447254⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1544187356533398083925395641670161042790508935295, 1544187356533398083925395641670161042790508935296⟩
def centerBExp : DyadicInterval precision := ⟨176631912183340190180341921927136620862145875581, 176631912183340190180341921927136623061169131134⟩
def centerBLog : DyadicInterval precision := ⟨166747235344326097913139701524879977347008500506, 166747235344326097913139701524879979546031756059⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176631912183340190180341921927136621411901689469, scale precision, 176631912183340190180341921927136622511413317246, scale precision,
    3, 128, 3, 128, ⟨-3088374713066796167850791283340322090129851642531, -3088374713066796167850791283340322090129849545378⟩, ⟨-3088374713066796167850791283340322081032186195800, -3088374713066796167850791283340322081032184098647⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨641273119690173612337267687418374481434737173716, 652689160097701375149760824218316252802232452654⟩
def wholeCExp : DyadicInterval precision := ⟨598270871237249103783331905252593795460036464947, 607690652328709209641027373483032208444001083728⟩
def wholeCLog : DyadicInterval precision := ⟨501486690911201062394386188931103339738359195861, 508155214401185533128683922186735533635231270824⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨598270871237249103783331905252593796009792278835, scale precision, 607690652328709209641027373483032207894245269840, scale precision,
    1, 128, 1, 128, ⟨-1305378320195402750299521648436632506947451315127, -1305378320195402750299521648436632506947449217974⟩, ⟨-1282546239380347224674535374836748961547307580770, -1282546239380347224674535374836748961547305483617⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1527678869049269554975872165558453836971951270535, 1560770995584367941983354918839190096856090425700⟩
def wholeBExp : DyadicInterval precision := ⟨172668574445433742047323109746427574430229572295, 180667641055007148721940436397820242569883376475⟩
def wholeBLog : DyadicInterval precision := ⟨163206960450432814319954841461018521041608390366, 170343383406929253441287321187679669045393602111⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172668574445433742047323109746427574979985386183, scale precision, 180667641055007148721940436397820242020127562587, scale precision,
    3, 128, 3, 128, ⟨-3121541991168735883966709837678380198365425981654, -3121541991168735883966709837678380198365423884501⟩, ⟨-3055357738098539109951744331116907669496682064869, -3055357738098539109951744331116907669496679967716⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0505StableWitnesses

end


