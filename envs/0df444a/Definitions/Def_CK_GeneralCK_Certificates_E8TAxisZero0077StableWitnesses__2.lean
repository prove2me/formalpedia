-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0077StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0077StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:43:55.645526+00:00
-- url     : https://prove2.me/theorems/e0085454-ea75-4096-94c7-6528eefe2646
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0077StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0078StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0077StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0078StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0077StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0078StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0077StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0078StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0077StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisZero0078StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0077StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨589001631572899351572124980299114401874513713575, 589001631572899351572124980299114401874513713576⟩
def centerDExp : DyadicInterval precision := ⟨652751929826838909185228475799900996561578066054, 652751929826838909185228475799900998760601321607⟩
def centerDLog : DyadicInterval precision := ⟨539641066124454758744190885645098755336345326342, 539641066124454758744190885645098757535368581895⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨652751929826838909185228475799900997111333879942, scale precision, 652751929826838909185228475799900998210845507719, scale precision,
    0, 256, 0, 256, ⟨-1178003263145798703144249960598228804979923376863, -1178003263145798703144249960598228804979921279710⟩, ⟨-1178003263145798703144249960598228802518133574591, -1178003263145798703144249960598228802518131477438⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨589188136620753529644801452363937789074904480617, 589188136620753529644801452363937789074904480618⟩
def centerCExp : DyadicInterval precision := ⟨652585353214880659796910358033188156154820221919, 652585353214880659796910358033188158353843477472⟩
def centerCLog : DyadicInterval precision := ⟨539525913625302144069978373536286282627004770294, 539525913625302144069978373536286284826028025847⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨652585353214880659796910358033188156704576035807, scale precision, 652585353214880659796910358033188157804087663584, scale precision,
    0, 256, 0, 256, ⟨-1178376273241507059289602904727875579381019104793, -1178376273241507059289602904727875579381017007640⟩, ⟨-1178376273241507059289602904727875576918600914829, -1178376273241507059289602904727875576918598817676⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1380501973237890023033602634807355823912324893691, 1380501973237890023033602634807355823912324893692⟩
def centerBExp : DyadicInterval precision := ⟨220978219694471083122677102328822994344933053496, 220978219694471083122677102328822996543956309049⟩
def centerBLog : DyadicInterval precision := ⟨205785838545256337326739341008481024943800050107, 205785838545256337326739341008481027142823305660⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨220978219694471083122677102328822994894688867384, scale precision, 220978219694471083122677102328822995994200495161, scale precision,
    0, 256, 0, 256, ⟨-2761003946475780046067205269614711651460615607696, -2761003946475780046067205269614711651460613510543⟩, ⟨-2761003946475780046067205269614711644188686064222, -2761003946475780046067205269614711644188683967069⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨583646737036782134467503622221012937253099239179, 594370338528145575810628189240163754488538282194⟩
def wholeDExp : DyadicInterval precision := ⟨647973841382699837641744325099416506198004171002, 657552822402718366845230970835233707672091898233⟩
def wholeDLog : DyadicInterval precision := ⟨536334420746670162773197764634792505120063760737, 542955975091047008060968952594356693577949672231⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨647973841382699837641744325099416506747759984890, scale precision, 657552822402718366845230970835233707122336084345, scale precision,
    0, 256, 0, 256, ⟨-1188740677056291151621256378480327510217048998869, -1188740677056291151621256378480327510217046901716⟩, ⟨-1167293474073564268935007244442025873284291575580, -1167293474073564268935007244442025873284289478427⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨583646737036782134467503622221012937253099239179, 594744330860052389027389161313773445021387305466⟩
def wholeCExp : DyadicInterval precision := ⟨647642298482951318824865167693805805201668214435, 657552822402718366845230970835233707672091898233⟩
def wholeCLog : DyadicInterval precision := ⟨536104700810258324974082061428404157561639366643, 542955975091047008060968952594356693577949672231⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨647642298482951318824865167693805805751424028323, scale precision, 657552822402718366845230970835233707122336084345, scale precision,
    0, 256, 0, 256, ⟨-1189488661720104778054778322627546891283381815117, -1189488661720104778054778322627546891283379717964⟩, ⟨-1167293474073564268935007244442025873284291575580, -1167293474073564268935007244442025873284289478427⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1364811274234846338402132329395097564650264276652, 1396277294727754898993757472472361982396946679571⟩
def wholeBExp : DyadicInterval precision := ⟨216258903514821547674149009457818933516780163741, 225774376624880677049417044690386074234384448820⟩
def wholeBLog : DyadicInterval precision := ⟨201680600799179076763764949226107750974578053609, 209946137515475163379133007721374350849558788259⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨216258903514821547674149009457818934066535977629, scale precision, 225774376624880677049417044690386073684628634932, scale precision,
    0, 256, 0, 256, ⟨-2792554589455509797987514944944723968509205125894, -2792554589455509797987514944944723968509203028741⟩, ⟨-2729622548469692676804264658790195125741804142683, -2729622548469692676804264658790195125741802045530⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0077StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0078StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨578305529745348302256248804406759576517080537351, 578305529745348302256248804406759576517080537352⟩
def centerDExp : DyadicInterval precision := ⟨662376618137962680502649166797816345145246286664, 662376618137962680502649166797816347344269542217⟩
def centerDLog : DyadicInterval precision := ⟨546279142756386118646189338978646827486920449598, 546279142756386118646189338978646829685943705151⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨662376618137962680502649166797816345695002100552, scale precision, 662376618137962680502649166797816346794513728329, scale precision,
    0, 256, 0, 256, ⟨-1156611059490696604512497608813519154247171459854, -1156611059490696604512497608813519154247169362701⟩, ⟨-1156611059490696604512497608813519151821152786705, -1156611059490696604512497608813519151821150689552⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨578491082485641230246868751220132637049297534547, 578491082485641230246868751220132637049297534548⟩
def centerCExp : DyadicInterval precision := ⟨662208448372535388491536878120813760211527604157, 662208448372535388491536878120813762410550859710⟩
def centerCLog : DyadicInterval precision := ⟨546163415728289921926110635196918648560268510575, 546163415728289921926110635196918650759291766128⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨662208448372535388491536878120813760761283418045, scale precision, 662208448372535388491536878120813761860795045822, scale precision,
    0, 256, 0, 256, ⟨-1156982164971282460493737502440265275311913501503, -1156982164971282460493737502440265275311911404350⟩, ⟨-1156982164971282460493737502440265272885278733840, -1156982164971282460493737502440265272885276636687⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1349738005339703279395649835805725417843393791367, 1349738005339703279395649835805725417843393791368⟩
def centerBExp : DyadicInterval precision := ⟨230479809740986410799807369142750516517620386480, 230479809740986410799807369142750518716643642033⟩
def centerBLog : DyadicInterval precision := ⟨214016264001824600552051573770399573270525057141, 214016264001824600552051573770399575469548312694⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨230479809740986410799807369142750517067376200368, scale precision, 230479809740986410799807369142750518166887828145, scale precision,
    0, 256, 0, 256, ⟨-2699476010679406558791299671611450839172859810530, -2699476010679406558791299671611450839172857713377⟩, ⟨-2699476010679406558791299671611450832200717452090, -2699476010679406558791299671611450832200715354937⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨572977884517961874928161575521614457065497220141, 583646737036782134467503622221012937253099239180⟩
def wholeDExp : DyadicInterval precision := ⟨657552822402718366845230970835233705473068642680, 667223417983630662234844101180676645055775852155⟩
def wholeDLog : DyadicInterval precision := ⟨542955975091047008060968952594356691378926416678, 549610565162722028431892812520915520687805740148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨657552822402718366845230970835233706022824456568, scale precision, 667223417983630662234844101180676644506020038267, scale precision,
    0, 256, 0, 256, ⟨-1167293474073564268935007244442025875728107478292, -1167293474073564268935007244442025875728105381139⟩, ⟨-1145955769035923749856323151043228912926797613794, -1145955769035923749856323151043228912926795516641⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨572977884517961874928161575521614457065497220141, 584018807035349444430159681280902230224535388379⟩
def wholeCExp : DyadicInterval precision := ⟨657218107206489678688831994703353252014509705482, 667223417983630662234844101180676645055775852155⟩
def wholeCLog : DyadicInterval precision := ⟨542725105401080048159096910323872463088285754508, 549610565162722028431892812520915520687805740148⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨657218107206489678688831994703353252564265519370, scale precision, 667223417983630662234844101180676644506020038267, scale precision,
    0, 256, 0, 256, ⟨-1168037614070698888860319362561804461671602083281, -1168037614070698888860319362561804461671599986128⟩, ⟨-1145955769035923749856323151043228912926797613794, -1145955769035923749856323151043228912926795516641⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1334215675231939330750047836493612725537766613625, 1365346303531531080154923529324198679231538962027⟩
def wholeBExp : DyadicInterval precision := ⟨225609133299185621494590770188613342041418411398, 235427941038873312407366610325559151950085482210⟩
def wholeBLog : DyadicInterval precision := ⟨209802998387288936798841810999377793838723749470, 218284128857725660156212244474398800326049891368⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨225609133299185621494590770188613342591174225286, scale precision, 235427941038873312407366610325559151400329668322, scale precision,
    0, 256, 0, 256, ⟨-2730692607063062160309847058648397362024410955870, -2730692607063062160309847058648397362024408858717⟩, ⟨-2668431350463878661500095672987225447662731961093, -2668431350463878661500095672987225447662729863940⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0078StableWitnesses

end


