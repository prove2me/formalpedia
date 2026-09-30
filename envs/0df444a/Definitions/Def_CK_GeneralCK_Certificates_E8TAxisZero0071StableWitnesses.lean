-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0071StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0071StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:16:54.786114+00:00
-- url     : https://prove2.me/theorems/3b04d792-1763-4ca0-9fc9-2a7cdd91f3b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0071StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0071StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0071StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0071StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0071StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0071StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0071StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨654373479606638252589496685135113086385905445322, 654373479606638252589496685135113086385905445323⟩
def centerDExp : DyadicInterval precision := ⟨596893494903452163994038347155718252372053594473, 596893494903452163994038347155718254571076850026⟩
def centerDLog : DyadicInterval precision := ⟨500509053273440340443871498920685505225663393173, 500509053273440340443871498920685507424686648726⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨596893494903452163994038347155718252921809408361, scale precision, 596893494903452163994038347155718254021321036138, scale precision,
    0, 512, 0, 512, ⟨-1308746959213276505178993370270226174117896339520, -1308746959213276505178993370270226174117894242367⟩, ⟨-1308746959213276505178993370270226171425727538920, -1308746959213276505178993370270226171425725441767⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨654566063484273122992984643910125750251252484139, 654566063484273122992984643910125750251252484140⟩
def centerCExp : DyadicInterval precision := ⟨596736208842591566632762780877414828577073785224, 596736208842591566632762780877414830776097040777⟩
def centerCLog : DyadicInterval precision := ⟨500397372763278438904349189558155862019651159230, 500397372763278438904349189558155864218674414783⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨596736208842591566632762780877414829126829599112, scale precision, 596736208842591566632762780877414830226341226889, scale precision,
    0, 512, 0, 512, ⟨-1309132126968546245985969287820251501848945214316, -1309132126968546245985969287820251501848943117163⟩, ⟨-1309132126968546245985969287820251499156066819393, -1309132126968546245985969287820251499156064722240⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1571725475230391432901411083389706526352765284825, 1571725475230391432901411083389706526352765284826⟩
def centerBExp : DyadicInterval precision := ⟨170099453090810021613012895602268860981881278297, 170099453090810021613012895602268863180904533850⟩
def centerBLog : DyadicInterval precision := ⟨160907487833763711336931943272193644897211050811, 160907487833763711336931943272193647096234306364⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨170099453090810021613012895602268861531637092185, scale precision, 170099453090810021613012895602268862631148719962, scale precision,
    0, 512, 0, 512, ⟨-3143450950460782865802822166779413057429056635682, -3143450950460782865802822166779413057429054538529⟩, ⟨-3143450950460782865802822166779413047982006600767, -3143450950460782865802822166779413047982004503614⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458569907208, 659917674403335303398947154306570012946022027568⟩
def wholeDExp : DyadicInterval precision := ⟨592382009410612930615839145836493981094734824913, 601426740197304508434017275821189107729148063965⟩
def wholeDLog : DyadicInterval precision := ⟨497302293015079090720897450218278677548754229682, 503724208829984298099852655433700222030834719032⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨592382009410612930615839145836493981644490638801, scale precision, 601426740197304508434017275821189107179392250077, scale precision,
    0, 512, 0, 512, ⟨-1319835348806670606797894308613140027248381064907, -1319835348806670606797894308613140027248378967754⟩, ⟨-1297689185454824353294856041553732547581202554253, -1297689185454824353294856041553732547581200457100⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458569907208, 660303930180161063936819287286141739973453703873⟩
def wholeCExp : DyadicInterval precision := ⟨592068974506944363188532861723407472364269567778, 601426740197304508434017275821189107729148063965⟩
def wholeCLog : DyadicInterval precision := ⟨497079526797204120577535414863912712323639962729, 503724208829984298099852655433700222030834719032⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨592068974506944363188532861723407472914025381666, scale precision, 601426740197304508434017275821189107179392250077, scale precision,
    0, 512, 0, 512, ⟨-1320607860360322127873638574572283481303961530753, -1320607860360322127873638574572283481303959433600⟩, ⟨-1297689185454824353294856041553732547581202554253, -1297689185454824353294856041553732547581200457100⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1555092990371828267132069363079500915962314763769, 1588431228776355760173672161545818050501958495067⟩
def wholeBExp : DyadicInterval precision := ⟨166254908402566908362908935684900847643171873927, 174015452037264545294049153225953940749178405047⟩
def wholeBLog : DyadicInterval precision := ⟨157459685174626573909984749578690504944524373636, 164411029057480154481205173504561254565031458958⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨166254908402566908362908935684900848192927687815, scale precision, 174015452037264545294049153225953940199422591159, scale precision,
    0, 512, 0, 512, ⟨-3176862457552711520347344323091636105836671729110, -3176862457552711520347344323091636105836669631957⟩, ⟨-3110185980743656534264138726159001827307402549965, -3110185980743656534264138726159001827307400452812⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0071StableWitnesses

end


