-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0590StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0590StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:42:53.994208+00:00
-- url     : https://prove2.me/theorems/95711111-c282-4553-b25e-6bf915d846be
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0590StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0591StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0590StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0591StableWitnesses, GeneralCK.Certificates.E8TAxisProd0592StableWitnesses, GeneralCK.Certificates.E8TAxisProd0593StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0590StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0591StableWitnesses, GeneralCK.Certificates.E8TAxisProd0592StableWitnesses, GeneralCK.Certificates.E8TAxisProd0593StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0590StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0591StableWitnesses, GeneralCK.Certificates.E8TAxisProd0592StableWitnesses, GeneralCK.Certificates.E8TAxisProd0593StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0590StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0591StableWitnesses, GeneralCK/Certificates/E8TAxisProd0592StableWitnesses, GeneralCK/Certificates/E8TAxisProd0593StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0590StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0590StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112195118, 676643340013426075185609328596269506214112195119⟩
def centerDExp : DyadicInterval precision := ⟨578977364869803800462989438501500576320691752033, 578977364869803800462989438501500578519715007586⟩
def centerDLog : DyadicInterval precision := ⟨487732559398326774108745629110692920177628439235, 487732559398326774108745629110692922376651694788⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500576870447565921, scale precision, 578977364869803800462989438501500577969959193698, scale precision,
    1, 128, 1, 128, ⟨-1353286680026852150371218657192539013815963666390, -1353286680026852150371218657192539013815961569237⟩, ⟨-1353286680026852150371218657192539011040487211240, -1353286680026852150371218657192539011040485114087⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨678396763307284100242022250028447090279839297086, 678396763307284100242022250028447090279839297087⟩
def centerCExp : DyadicInterval precision := ⟨577589784619443616982065453057931008561721753204, 577589784619443616982065453057931010760745008757⟩
def centerCLog : DyadicInterval precision := ⟨486738361149399883164836502040306708720050253827, 486738361149399883164836502040306710919073509380⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨577589784619443616982065453057931009111477567092, scale precision, 577589784619443616982065453057931010210989194869, scale precision,
    1, 128, 1, 128, ⟨-1356793526614568200484044500056894181950751721110, -1356793526614568200484044500056894181950749623957⟩, ⟨-1356793526614568200484044500056894179168607564389, -1356793526614568200484044500056894179168605467236⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1640135608499735189152178959803831161133034989061, 1640135608499735189152178959803831161133034989062⟩
def centerBExp : DyadicInterval precision := ⟨154898034558330555276738759319449395715752118457, 154898034558330555276738759319449397914775374010⟩
def centerBLog : DyadicInterval precision := ⟨147227035198054116579953710780809594516054216716, 147227035198054116579953710780809596715077472269⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨154898034558330555276738759319449396265507932345, scale precision, 154898034558330555276738759319449397365019560122, scale precision,
    3, 128, 3, 128, ⟨-3280271216999470378304357919607662327453154416239, -3280271216999470378304357919607662327453152319086⟩, ⟨-3280271216999470378304357919607662317078987637155, -3280271216999470378304357919607662317078985540002⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    1, 128, 1, 128, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨672606619126264403234399907347378932518033989561, 684203867031448761187390591904118350751842849267⟩
def wholeCExp : DyadicInterval precision := ⟨573018004851415669248642023961905504304816249798, 582184528261318561542974128240133718994720508629⟩
def wholeCLog : DyadicInterval precision := ⟨483457897542752173561803383298775830305683783660, 490027900217700237265770295072014896057533545755⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨573018004851415669248642023961905504854572063686, scale precision, 582184528261318561542974128240133718444964694741, scale precision,
    1, 128, 1, 128, ⟨-1368407734062897522374781183808236702905857386300, -1368407734062897522374781183808236702905855289147⟩, ⟨-1345213238252528806468799814694757863655975632690, -1345213238252528806468799814694757863655973535537⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1623212446444601877699036107917138977246706917968, 1657127135793409752084630621174960629163626651647⟩
def wholeBExp : DyadicInterval precision := ⟨151337873401335094049884330518337267792833090481, 158527115376033404379940493823984529004347652909⟩
def wholeBLog : DyadicInterval precision := ⟨144004490707580048224987599297905515352318024364, 150504666638783057683211232125050983022985779083⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨151337873401335094049884330518337268342588904369, scale precision, 158527115376033404379940493823984528454591839021, scale precision,
    3, 128, 3, 128, ⟨-3314254271586819504169261242349921263636361742317, -3314254271586819504169261242349921263636359645164⟩, ⟨-3246424892889203755398072215834277949425076763148, -3246424892889203755398072215834277949425074665995⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0590StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0591StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0591StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345921467119, 665477300625433477361232002502002625345921467120⟩
def centerDExp : DyadicInterval precision := ⟨587892208188294475401269251844616962692532348577, 587892208188294475401269251844616964891555604130⟩
def centerDLog : DyadicInterval precision := ⟨494103945124224218680176638976803110922563855190, 494103945124224218680176638976803113121587110743⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963242288162465, scale precision, 587892208188294475401269251844616964341799790242, scale precision,
    1, 128, 1, 128, ⟨-1330954601250866954722464005004005252058538439621, -1330954601250866954722464005004005252058536342468⟩, ⟨-1330954601250866954722464005004005249325149526009, -1330954601250866954722464005004005249325147428856⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨667220896356154730146739909946720181593500002294, 667220896356154730146739909946720181593500002295⟩
def centerCExp : DyadicInterval precision := ⟨586491149998691989899560703053105230790789157537, 586491149998691989899560703053105232989812413090⟩
def centerCLog : DyadicInterval precision := ⟨493104454911858434609070104807911981870506629681, 493104454911858434609070104807911984069529885234⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨586491149998691989899560703053105231340544971425, scale precision, 586491149998691989899560703053105232440056599202, scale precision,
    1, 128, 1, 128, ⟨-1334441792712309460293479819893440364556960381847, -1334441792712309460293479819893440364556958284694⟩, ⟨-1334441792712309460293479819893440361817041724482, -1334441792712309460293479819893440361817039627329⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1606933915111647846147013510607685393823829502314, 1606933915111647846147013510607685393823829502315⟩
def centerBExp : DyadicInterval precision := ⟨162098163598967934665613765750618726933348183983, 162098163598967934665613765750618729132371439536⟩
def centerBLog : DyadicInterval precision := ⟨153722726195940909633418102455210366346368421681, 153722726195940909633418102455210368545391677234⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨162098163598967934665613765750618727483103997871, scale precision, 162098163598967934665613765750618728582615625648, scale precision,
    3, 128, 3, 128, ⟨-3213867830223295692294027021215370792604341882855, -3213867830223295692294027021215370792604339785702⟩, ⟨-3213867830223295692294027021215370782690978223560, -3213867830223295692294027021215370782690976126407⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946022027567, 671052481512572809340093335645151882932874114538⟩
def wholeDExp : DyadicInterval precision := ⟨583424017396714902499808941799093863591730436308, 592382009410612930615839145836493983293758080466⟩
def wholeDLog : DyadicInterval precision := ⟨490914027605645316992013980560028280616805628608, 497302293015079090720897450218278679747777485235⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864141486250196, scale precision, 592382009410612930615839145836493982744002266578, scale precision,
    1, 128, 1, 128, ⟨-1342104963025145618680186671290303767242910652864, -1342104963025145618680186671290303767242908555711⟩, ⟨-1319835348806670606797894308613140024535709142512, -1319835348806670606797894308613140024535707045359⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨661463145992160127123643008792143655553538655043, 672995343512409831386744538705553841396537988880⟩
def wholeCExp : DyadicInterval precision := ⟨581874916372543621964231506754334887938548671139, 591130499163526447569362111430565053909297112161⟩
def wholeCLog : DyadicInterval precision := ⟨489806470641339221794152557105145552212192485646, 496411472461388011322656184405716805010410520000⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨581874916372543621964231506754334888488304485027, scale precision, 591130499163526447569362111430565053359541298273, scale precision,
    1, 128, 1, 128, ⟨-1345990687024819662773489077411107684173904760135, -1345990687024819662773489077411107684173902662982⟩, ⟨-1322926291984320254247286017584287309747870834663, -1322926291984320254247286017584287309747868737510⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1590148735967663479591327288168217592213673191452, 1623789873960548274424612548147302389380249261622⟩
def wholeBExp : DyadicInterval precision := ⟨158401899283577761975354947039996263109481986173, 165864612976829662891887576032413201019807867272⟩
def wholeBLog : DyadicInterval precision := ⟨150391699139531064164672162195379210975434694756, 157109211510662189994234305122461101149387616971⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨158401899283577761975354947039996263659237800061, scale precision, 165864612976829662891887576032413200470052053384, scale precision,
    3, 128, 3, 128, ⟨-3247579747921096548849225096294604783832844194980, -3247579747921096548849225096294604783832842097827⟩, ⟨-3180297471935326959182654576336435179583221805706, -3180297471935326959182654576336435179583219708553⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0591StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0592StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0592StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨657264185283996171951032456349988512108042006169, 657264185283996171951032456349988512108042006170⟩
def centerCExp : DyadicInterval precision := ⟨594536966371809583151276127989498849307259445534, 594536966371809583151276127989498851506282701087⟩
def centerCLog : DyadicInterval precision := ⟨498834912477866403349706966593701201187054492504, 498834912477866403349706966593701203386077748057⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨594536966371809583151276127989498849857015259422, scale precision, 594536966371809583151276127989498850956526887199, scale precision,
    1, 128, 1, 128, ⟨-1314528370567992343902064912699977025567504850728, -1314528370567992343902064912699977025567502753575⟩, ⟨-1314528370567992343902064912699977022864665271102, -1314528370567992343902064912699977022864663173949⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1575716807884272703145672071498521517529787280919, 1575716807884272703145672071498521517529787280920⟩
def centerBExp : DyadicInterval precision := ⟨169172909146657023088613235873494648813187203830, 169172909146657023088613235873494651012210459383⟩
def centerBLog : DyadicInterval precision := ⟨160077303215067962731805141097497030886654713884, 160077303215067962731805141097497033085677969437⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨169172909146657023088613235873494649362943017718, scale precision, 169172909146657023088613235873494650462454645495, scale precision,
    3, 128, 3, 128, ⟨-3151433615768545406291344142997043039808970925444, -3151433615768545406291344142997043039808968828291⟩, ⟨-3151433615768545406291344142997043030310180295394, -3151433615768545406291344142997043030310178198241⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨651535015854781642443308114413367692140820958207, 663009815081596323194924310459735315692685213045⟩
def wholeCExp : DyadicInterval precision := ⟨589880666296200405133412701671308644049541822383, 599216523886861167643580363684731910917113700466⟩
def wholeCLog : DyadicInterval precision := ⟨495521303644924158182122142436134223951472994727, 502157520203524569108738803556459322111450498482⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨589880666296200405133412701671308644599297636271, scale precision, 599216523886861167643580363684731910367357886578, scale precision,
    1, 128, 1, 128, ⟨-1326019630163192646389848620919470632747458873079, -1326019630163192646389848620919470632747456775926⟩, ⟨-1303070031709563284886616228826735382940777034062, -1303070031709563284886616228826735382940774936909⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1559066683441564552691763259795535931106228428157, 1592439923156716240542310445691678097554891955265⟩
def wholeBExp : DyadicInterval precision := ⟨165345377523334666999875155609120834411168035256, 173071755091786713252852979150000408148296783764⟩
def wholeBLog : DyadicInterval precision := ⟨156642823225661256699787012659815292362746921149, 163567496025640542003248558374583495647471040734⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨165345377523334666999875155609120834960923849144, scale precision, 173071755091786713252852979150000407598540969876, scale precision,
    3, 128, 3, 128, ⟨-3184879846313432481084620891383356199969122632557, -3184879846313432481084620891383356199969120535404⟩, ⟨-3118133366883129105383526519591071857570053823973, -3118133366883129105383526519591071857570051726820⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0592StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0593StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0593StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨646205717656452371992114969547318813583009282196, 646205717656452371992114969547318813583009282197⟩
def centerCExp : DyadicInterval precision := ⟨603602528550989230117674990472092708751974857399, 603602528550989230117674990472092710950998112952⟩
def centerCLog : DyadicInterval precision := ⟨505264854889542435797577781731909647140053644701, 505264854889542435797577781731909649339076900254⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨603602528550989230117674990472092709301730671287, scale precision, 603602528550989230117674990472092710401242299064, scale precision,
    1, 128, 1, 128, ⟨-1292411435312904743984229939094637628497142304021, -1292411435312904743984229939094637628497140206868⟩, ⟨-1292411435312904743984229939094637625834896921918, -1292411435312904743984229939094637625834894824765⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1543056164846586775622614099144776584759218071762, 1543056164846586775622614099144776584759218071763⟩
def centerBExp : DyadicInterval precision := ⟨176905547563121841119263856349594573411594801248, 176905547563121841119263856349594575610618056801⟩
def centerBLog : DyadicInterval precision := ⟨166991345574553108848082278792072233614226549615, 166991345574553108848082278792072235813249805168⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176905547563121841119263856349594573961350615136, scale precision, 176905547563121841119263856349594575060862242913, scale precision,
    3, 128, 3, 128, ⟨-3086112329693173551245228198289553174060233835553, -3086112329693173551245228198289553174060231738400⟩, ⟨-3086112329693173551245228198289553164976640548649, -3086112329693173551245228198289553164976638451496⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨640507973898747819750051985640282712173820457560, 651919656773990497585933705479073939223208353806⟩
def wholeCExp : DyadicInterval precision := ⟨598901200878960973333986508624571043504093316634, 608327278996568749887339419792642762141730444831⟩
def wholeCLog : DyadicInterval precision := ⟨501933869845625558169767361263358869787722470689, 508604804233408033068482699525888449783662002648⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨598901200878960973333986508624571044053849130522, scale precision, 608327278996568749887339419792642761591974630943, scale precision,
    1, 128, 1, 128, ⟨-1303839313547980995171867410958147879787989656446, -1303839313547980995171867410958147879787987559293⟩, ⟨-1281015947797495639500103971280565423026857823528, -1281015947797495639500103971280565423026855726375⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1526552856354628728457747057684365987718472412125, 1559634700888521595392643067494422865595914689687⟩
def wholeBExp : DyadicInterval precision := ⟨172937277543198744294506206777865391613277908562, 180946246111985039709756072176697246576237963238⟩
def wholeBLog : DyadicInterval precision := ⟨163447252270597019622730124841286006113754731055, 170591315953011217689222963583457441525783115181⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172937277543198744294506206777865392163033722450, scale precision, 180946246111985039709756072176697246026482149350, scale precision,
    3, 128, 3, 128, ⟨-3119269401777043190785286134988845735837844483125, -3119269401777043190785286134988845735837842385972⟩, ⟨-3053105712709257456915494115368731970996571787186, -3053105712709257456915494115368731970996569690033⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0593StableWitnesses

end


