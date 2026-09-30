-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:11:38.839831+00:00
-- url     : https://prove2.me/theorems/3b7cdb64-a702-4d95-bc60-58c4bafbd7fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0475StableWitnesses, GeneralCK/Certificates/E8TAxisProd0476StableWitnesses, GeneralCK/Certificates/E8TAxisProd0477StableWitnesses) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0475StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0475StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨648124555653810440831541398454845609294990836235, 648124555653810440831541398454845609294990836236⟩
def centerCExp : DyadicInterval precision := ⟨602019641305679521052300593845154243119416897775, 602019641305679521052300593845154245318440153328⟩
def centerCLog : DyadicInterval precision := ⟨504144195025785291294973075828702087566977097789, 504144195025785291294973075828702089766000353342⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨602019641305679521052300593845154243669172711663, scale precision, 602019641305679521052300593845154244768684339440, scale precision,
    1, 128, 1, 128, ⟨-1296249111307620881663082796909691219924605326364, -1296249111307620881663082796909691219924603229211⟩, ⟨-1296249111307620881663082796909691217255360115734, -1296249111307620881663082796909691217255358018581⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1545884802764474973024305085461446231659400204078, 1545884802764474973024305085461446231659400204079⟩
def centerBExp : DyadicInterval precision := ⟨176222093666730186303395243163634830568278720878, 176222093666730186303395243163634832767301976431⟩
def centerBLog : DyadicInterval precision := ⟨166381559806675622050704991191460615485479223051, 166381559806675622050704991191460617684502478604⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨176222093666730186303395243163634831118034534766, scale precision, 176222093666730186303395243163634832217546162543, scale precision,
    3, 128, 3, 128, ⟨-3091769605528949946048610170922892467878212852954, -3091769605528949946048610170922892467878210755801⟩, ⟨-3091769605528949946048610170922892458759390060509, -3091769605528949946048610170922892458759387963356⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨642421383405750773454509727691472322364334736000, 653843969421245541837132973581687857387168975507⟩
def wholeCExp : DyadicInterval precision := ⟨597326167321274749556343269918222904135773694889, 606736508780892232919049409149877070571500613408⟩
def wholeCLog : DyadicInterval precision := ⟨500816227045226244175523267872891555689391511258, 507481133034138324131981688368331854109738053546⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨597326167321274749556343269918222904685529508777, scale precision, 606736508780892232919049409149877070021744799520, scale precision,
    1, 128, 1, 128, ⟨-1307687938842491083674265947163375716119448365438, -1307687938842491083674265947163375716119446268285⟩, ⟨-1284842766811501546909019455382944643404423486646, -1284842766811501546909019455382944643404421389493⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1529368556416040230825773363391982007926840863165, 1562476086449565366661337867154286308443342063329⟩
def wholeBExp : DyadicInterval precision := ⟨172266149456677795668291256452901761930505068828, 180250372732448738968050648516587288924124060553⟩
def wholeBLog : DyadicInterval precision := ⟨162847011893758190924076478570162131227955792414, 169971974785137702614095550467225416007657859148⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨172266149456677795668291256452901762480260882716, scale precision, 180250372732448738968050648516587288374368246665, scale precision,
    3, 128, 3, 128, ⟨-3124952172899130733322675734308572621550799539342, -3124952172899130733322675734308572621550797442189⟩, ⟨-3058737112832080461651546726783964011396166210860, -3058737112832080461651546726783964011396164113707⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0475StableWitnesses

end


