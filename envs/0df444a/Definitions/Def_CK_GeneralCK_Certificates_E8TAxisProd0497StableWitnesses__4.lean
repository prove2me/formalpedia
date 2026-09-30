-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0497StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0497StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:48:24.430734+00:00
-- url     : https://prove2.me/theorems/281d6759-f6f3-4be2-b1f3-d54cf2f921a5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0497StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0498StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0497StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0498StableWitnesses, GeneralCK.Certificates.E8TAxisProd0499StableWitnesses, GeneralCK.Certificates.E8TAxisProd0500StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0497StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0498StableWitnesses, GeneralCK.Certificates.E8TAxisProd0499StableWitnesses, GeneralCK.Certificates.E8TAxisProd0500StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0497StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0498StableWitnesses, GeneralCK.Certificates.E8TAxisProd0499StableWitnesses, GeneralCK.Certificates.E8TAxisProd0500StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0497StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0498StableWitnesses, GeneralCK/Certificates/E8TAxisProd0499StableWitnesses, GeneralCK/Certificates/E8TAxisProd0500StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0497StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0497StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨647740641415391239891880120459957078192841452944, 647740641415391239891880120459957078192841452945⟩
def centerCExp : DyadicInterval precision := ⟨602336007198906237680254250029189048756254675405, 602336007198906237680254250029189050955277930958⟩
def centerCLog : DyadicInterval precision := ⟨504368245940890737409267218521454654505945986897, 504368245940890737409267218521454656704969242450⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨602336007198906237680254250029189049306010489293, scale precision, 602336007198906237680254250029189050405522117070, scale precision,
    1, 128, 1, 128, ⟨-1295481282830782479783760240919914157719605573839, -1295481282830782479783760240919914157719603476686⟩, ⟨-1295481282830782479783760240919914155051762335090, -1295481282830782479783760240919914155051760237937⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1545318899586643288051806144145480836687550463241, 1545318899586643288051806144145480836687550463242⟩
def centerBExp : DyadicInterval precision := ⟨176358615261065977076316543223550816707206836340, 176358615261065977076316543223550818906230091893⟩
def centerBLog : DyadicInterval precision := ⟨166503386347999506385839019660224824736447236177, 166503386347999506385839019660224826935470491730⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176358615261065977076316543223550817256962650228, scale precision, 176358615261065977076316543223550818356474278005, scale precision,
    3, 128, 3, 128, ⟨-3090637799173286576103612288290961677930983869124, -3090637799173286576103612288290961677930981771971⟩, ⟨-3090637799173286576103612288290961668819220080995, -3090637799173286576103612288290961668819217983842⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨642038556107706771519437909253661699708218268492, 653458959012810235663762021274855672119955297823⟩
def wholeCExp : DyadicInterval precision := ⟨597640963254864920093835532221194965538480240080, 607054450472385817399100603070939275225956511603⟩
def wholeCLog : DyadicInterval precision := ⟨501039674388450532315592984713357278062061321674, 507705786365840927233039466663271110164324600579⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨597640963254864920093835532221194966088236053968, scale precision, 607054450472385817399100603070939274676200697715, scale precision,
    1, 128, 1, 128, ⟨-1306917918025620471327524042549711345584312499467, -1306917918025620471327524042549711345584310402314⟩, ⟨-1284077112215413543038875818507323398092884119303, -1284077112215413543038875818507323398092882022150⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1528805238241515381407522062180279457224473427589, 1561907636379118110012157572174780284627827831543⟩
def wholeBExp : DyadicInterval precision := ⟨172400207195537114399054400389565205796614028719, 180389376966321532756749657576281891902505747961⟩
def wholeBLog : DyadicInterval precision := ⟨162966929527457841269198141521789398865622922603, 170095712301070591920436434725734275232807095567⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172400207195537114399054400389565206346369842607, scale precision, 180389376966321532756749657576281891352749934073, scale precision,
    3, 128, 3, 128, ⟨-3123815272758236220024315144349560573916144278352, -3123815272758236220024315144349560573916142181199⟩, ⟨-3057610476483030762815044124360558909994866207578, -3057610476483030762815044124360558909994864110425⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0497StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0498StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0498StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨658421638246372675589328181806567521549868616643, 658421638246372675589328181806567521549868616644⟩
def centerCExp : DyadicInterval precision := ⟨593596011047659933983215643002931596822294026588, 593596011047659933983215643002931599021317282141⟩
def centerCLog : DyadicInterval precision := ⟨498165896572486198887190504948690179457310524246, 498165896572486198887190504948690181656333779799⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨593596011047659933983215643002931597372049840476, scale precision, 593596011047659933983215643002931598471561468253, scale precision,
    1, 128, 1, 128, ⟨-1316843276492745351178656363613135044453300312565, -1316843276492745351178656363613135044453298215412⟩, ⟨-1316843276492745351178656363613135041746176251161, -1316843276492745351178656363613135041746174154008⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1577428659686715545727981613295559120636218611436, 1577428659686715545727981613295559120636218611437⟩
def centerBExp : DyadicInterval precision := ⟨168777069688757119801911497610997630758990564865, 168777069688757119801911497610997632958013820418⟩
def centerBLog : DyadicInterval precision := ⟨159722486709764220547751419125752202814476432739, 159722486709764220547751419125752205013499688292⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨168777069688757119801911497610997631308746378753, scale precision, 168777069688757119801911497610997632408258006530, scale precision,
    3, 128, 3, 128, ⟨-3154857319373431091455963226591118246032972528930, -3154857319373431091455963226591118246032970431777⟩, ⟨-3154857319373431091455963226591118236511904013972, -3154857319373431091455963226591118236511901916819⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨652689160097701375149760824218316252802232452653, 664170604356148777566692885139367032399673075377⟩
def wholeCExp : DyadicInterval precision := ⟨588944391466983465608803865955127967047693778911, 598270871237249103783331905252593797659059720500⟩
def wholeCLog : DyadicInterval precision := ⟨494854104967280797095451782711959471416874727523, 501486690911201062394386188931103341937382451414⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨588944391466983465608803865955127967597449592799, scale precision, 598270871237249103783331905252593797109303906612, scale precision,
    1, 128, 1, 128, ⟨-1328341208712297555133385770278734066163599977303, -1328341208712297555133385770278734066163597880150⟩, ⟨-1305378320195402750299521648436632504261480592640, -1305378320195402750299521648436632504261478495487⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1560770995584367941983354918839190096856090425699, 1594159195088642481552023836766490869778453736005⟩
def wholeBExp : DyadicInterval precision := ⟨164956818921044295790491242147040251805381447551, 172668574445433742047323109746427576629252827848⟩
def wholeBLog : DyadicInterval precision := ⟨156293714270974927969249608627502326190368810807, 163206960450432814319954841461018523240631645919⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨164956818921044295790491242147040252355137261439, scale precision, 172668574445433742047323109746427576079497013960, scale precision,
    3, 128, 3, 128, ⟨-3188318390177284963104047673532981744427692446856, -3188318390177284963104047673532981744427690349703⟩, ⟨-3121541991168735883966709837678380189058937818296, -3121541991168735883966709837678380189058935721143⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0498StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0499StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0499StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨647356800538167128039896899232235298576818339340, 647356800538167128039896899232235298576818339341⟩
def centerCExp : DyadicInterval precision := ⟨602652478843602930752605267299353835565869867031, 602652478843602930752605267299353837764893122584⟩
def centerCLog : DyadicInterval precision := ⟨504592337390007518137603083157430375715618864655, 504592337390007518137603083157430377914642120208⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨602652478843602930752605267299353836115625680919, scale precision, 602652478843602930752605267299353837215137308696, scale precision,
    1, 128, 1, 128, ⟨-1294713601076334256079793798464470598486858862715, -1294713601076334256079793798464470598486856765562⟩, ⟨-1294713601076334256079793798464470595820416591799, -1294713601076334256079793798464470595820414494646⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1544753084161447229997755809528279635461102668334, 1544753084161447229997755809528279635461102668335⟩
def centerBExp : DyadicInterval precision := ⟨176495221425960227723735189878458868205049656040, 176495221425960227723735189878458870404072911593⟩
def centerBLog : DyadicInterval precision := ⟨166625278193090371767791449796412755180097921538, 166625278193090371767791449796412757379121177091⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176495221425960227723735189878458868754805469928, scale precision, 176495221425960227723735189878458869854317097705, scale precision,
    3, 128, 3, 128, ⟨-3089506168322894459995511619056559275474562056059, -3089506168322894459995511619056559275474559958906⟩, ⟨-3089506168322894459995511619056559266369850714429, -3089506168322894459995511619056559266369848617276⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨641655801549778186778377018714330017261833043959, 653074022585508322159584705333174808766390467135⟩
def wholeCExp : DyadicInterval precision := ⟨597955864551580265661874408781708067519785384310, 607372498312647309159538880823927252095187965162⟩
def wholeCLog : DyadicInterval precision := ⟨501263162345617387802195947079395589547298465192, 507930480156480886961416247419702938286935327996⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨597955864551580265661874408781708068069541198198, scale precision, 607372498312647309159538880823927251545432151274, scale precision,
    1, 128, 1, 128, ⟨-1306148045171016644319169410666349618876474836721, -1306148045171016644319169410666349618876472739568⟩, ⟨-1283311603099556373556754037428660033200806742977, -1283311603099556373556754037428660033200804645824⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1528242009104821242391341807650484682207402501059, 1561339272742174114391065573324879044629562419184⟩
def wholeBExp : DyadicInterval precision := ⟨172534348850867092377001815672534219463332890529, 180528466400148423444948024688901033029922327441⟩
def wholeBLog : DyadicInterval precision := ⟨163086912378518788522097794447961436249056612636, 170219515174579951484234859052498667600223799069⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172534348850867092377001815672534220013088704417, scale precision, 180528466400148423444948024688901032480166513553, scale precision,
    3, 128, 3, 128, ⟨-3122678545484348228782131146649758093915990027224, -3122678545484348228782131146649758093915987930071⟩, ⟨-3056484018209642484782683615300969359964156033270, -3056484018209642484782683615300969359964153936117⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0499StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0500StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0500StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨636734315271741079111585712310120543102689433933, 636734315271741079111585712310120543102689433934⟩
def centerCExp : DyadicInterval precision := ⟨611476857523133868808092949017717231967107724365, 611476857523133868808092949017717234166130979918⟩
def centerCLog : DyadicInterval precision := ⟨510827024386773040568846715799797651083021450893, 510827024386773040568846715799797653282044706446⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨611476857523133868808092949017717232516863538253, scale precision, 611476857523133868808092949017717233616375166030, scale precision,
    1, 128, 1, 128, ⟨-1273468630543482158223171424620241087519360997239, -1273468630543482158223171424620241087519358900086⟩, ⟨-1273468630543482158223171424620241084891398835647, -1273468630543482158223171424620241084891396738494⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1512928447835852000467239699373569934855038975001, 1512928447835852000467239699373569934855038975002⟩
def centerBExp : DyadicInterval precision := ⟨184351525847793953238314549275750398945374063543, 184351525847793953238314549275750401144397319096⟩
def centerBLog : DyadicInterval precision := ⟨173618303821801318259904303739948066053744757287, 173618303821801318259904303739948068252768012840⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨184351525847793953238314549275750399495129877431, scale precision, 184351525847793953238314549275750400594641505208, scale precision,
    2, 128, 2, 128, ⟨-3025856895671704000934479398747139874068431979038, -3025856895671704000934479398747139874068429881885⟩, ⟨-3025856895671704000934479398747139865351726018127, -3025856895671704000934479398747139865351723920974⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨631063213617052482596365474153866441891585767492, 642421383405750773454509727691472322364334736001⟩
def wholeCExp : DyadicInterval precision := ⟨606736508780892232919049409149877068372477357855, 616240777308156875716256065274209980376785575212⟩
def wholeCLog : DyadicInterval precision := ⟨507481133034138324131981688368331851910714797993, 514181853475477112667501827515251923977544945342⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨606736508780892232919049409149877068922233171743, scale precision, 616240777308156875716256065274209979827029761324, scale precision,
    1, 128, 1, 128, ⟨-1284842766811501546909019455382944646052917554506, -1284842766811501546909019455382944646052915457353⟩, ⟨-1262126427234104965192730948307732882479349383740, -1262126427234104965192730948307732882479347286587⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1496565546601214938744607001064488393205083070374, 1529368556416040230825773363391982007926840863166⟩
def wholeBExp : DyadicInterval precision := ⟨180250372732448738968050648516587286725100805000, 188526070857308122758872876189931119612230176413⟩
def wholeBLog : DyadicInterval precision := ⟨169971974785137702614095550467225413808634603595, 177320566049852779622305800641112056474635967587⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨180250372732448738968050648516587287274856618888, scale precision, 188526070857308122758872876189931119062474362525, scale precision,
    3, 128, 2, 128, ⟨-3058737112832080461651546726783964020311199338951, -3058737112832080461651546726783964020311197241798⟩, ⟨-2993131093202429877489214002128976782148321501477, -2993131093202429877489214002128976782148319404324⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0500StableWitnesses

end


