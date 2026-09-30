-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:54:04.580284+00:00
-- url     : https://prove2.me/theorems/b88c7fc6-813f-48f0-b15d-b1aa1e50bda3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0475StableWitnesses, GeneralCK/Certificates/E8TAxisProd0476StableWitnesses, GeneralCK/Certificates/E8TAxisProd0477StableWitnesses) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0474StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0474StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨659193646068884188838294114912886130381928572211, 659193646068884188838294114912886130381928572212⟩
def centerCExp : DyadicInterval precision := ⟨592969232711252703137387449700542138718186863782, 592969232711252703137387449700542140917210119335⟩
def centerCLog : DyadicInterval precision := ⟨497720089394482265088775180755735136522239064300, 497720089394482265088775180755735138721262319853⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨592969232711252703137387449700542139267942677670, scale precision, 592969232711252703137387449700542140367454305447, scale precision,
    1, 128, 1, 128, ⟨-1318387292137768377676588229825772262118850961269, -1318387292137768377676588229825772262118848864116⟩, ⟨-1318387292137768377676588229825772259408865424730, -1318387292137768377676588229825772259408863327577⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1578570320179376067456018354378352136405583695309, 1578570320179376067456018354378352136405583695310⟩
def centerBExp : DyadicInterval precision := ⟨168513593182003423742880535430122990935175608423, 168513593182003423742880535430122993134198863976⟩
def centerBLog : DyadicInterval precision := ⟨159486267918308587097415437515191853620291384957, 159486267918308587097415437515191855819314640510⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨168513593182003423742880535430122991484931422311, scale precision, 168513593182003423742880535430122992584443050088, scale precision,
    3, 128, 3, 128, ⟨-3157140640358752134912036708756704277579145947468, -3157140640358752134912036708756704277579143850315⟩, ⟨-3157140640358752134912036708756704268043190930920, -3157140640358752134912036708756704268043188833767⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨653458959012810235663762021274855672119955297822, 664944839474428300624170671856361288566189920439⟩
def wholeCExp : DyadicInterval precision := ⟨588320731600133497360363279009797257925379477931, 597640963254864920093835532221194967737503495633⟩
def wholeCLog : DyadicInterval precision := ⟨494409509718797692649801030573121383026645592500, 501039674388450532315592984713357280261084577227⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨588320731600133497360363279009797258475135291819, scale precision, 597640963254864920093835532221194967187747681745, scale precision,
    1, 128, 1, 128, ⟨-1329889678948856601248341343712722578498079867873, -1329889678948856601248341343712722578498077770720⟩, ⟨-1306917918025620471327524042549711342895510788974, -1306917918025620471327524042549711342895508691821⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1561907636379118110012157572174780284627827831542, 1595305795444587362115348256487193952426407007961⟩
def wholeBExp : DyadicInterval precision := ⟨164698192815816083075077914790547839225154965164, 172400207195537114399054400389565207995637284272⟩
def wholeBLog : DyadicInterval precision := ⟨156061299769504127648140409191613612897858195121, 162966929527457841269198141521789401064646178156⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨164698192815816083075077914790547839774910779052, scale precision, 172400207195537114399054400389565207445881470384, scale precision,
    3, 128, 3, 128, ⟨-3190611590889174724230696512974387909731247598538, -3190611590889174724230696512974387909731245501385⟩, ⟨-3123815272758236220024315144349560564595169144964, -3123815272758236220024315144349560564595167047811⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0474StableWitnesses

end


