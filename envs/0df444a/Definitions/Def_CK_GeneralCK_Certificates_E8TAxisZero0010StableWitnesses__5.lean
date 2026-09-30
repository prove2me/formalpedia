-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0010StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0010StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:46:46.693636+00:00
-- url     : https://prove2.me/theorems/11a1c472-10fe-45b9-a2ff-c4cef64c9a3c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0010StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0011StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0010StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0011StableWitnesses, GeneralCK.Certificates.E8TAxisZero0012StableWitnesses, GeneralCK.Certificates.E8TAxisZero0013StableWitnesses, GeneralCK.Certificates.E8TAxisZero0015StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0010StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0011StableWitnesses, GeneralCK.Certificates.E8TAxisZero0012StableWitnesses, GeneralCK.Certificates.E8TAxisZero0013StableWitnesses, GeneralCK.Certificates.E8TAxisZero0015StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0010StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0011StableWitnesses, GeneralCK.Certificates.E8TAxisZero0012StableWitnesses, GeneralCK.Certificates.E8TAxisZero0013StableWitnesses, GeneralCK.Certificates.E8TAxisZero0015StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0010StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0011StableWitnesses, GeneralCK/Certificates/E8TAxisZero0012StableWitnesses, GeneralCK/Certificates/E8TAxisZero0013StableWitnesses, GeneralCK/Certificates/E8TAxisZero0015StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0010StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0010StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨51467959962003113552544491254031858203557026049, 51467959962003113552544491254031858203557026050⟩
def centerDExp : DyadicInterval precision := ⟨1362107062367078087011245274026450153640437332371, 1362107062367078087011245274026450155839460587924⟩
def centerDLog : DyadicInterval precision := ⟨962473834965157682455461912650904923379559762004, 962473834965157682455461912650904925578583017557⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1362107062367078087011245274026450154190193146259, scale precision, 1362107062367078087011245274026450155289704774036, scale precision,
    0, 128, 0, 128, ⟨-102935919924006227105088982508063716996987251205, -102935919924006227105088982508063716996985154052⟩, ⟨-102935919924006227105088982508063715817242950146, -102935919924006227105088982508063715817240852993⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨52102032233946378483314155386921642067692021000, 52102032233946378483314155386921642067692021001⟩
def centerCExp : DyadicInterval precision := ⟨1360925675085681898565034342337875046391550989164, 1360925675085681898565034342337875048590574244717⟩
def centerCLog : DyadicInterval precision := ⟨961862220208335089960733784578790899919159458385, 961862220208335089960733784578790902118182713938⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1360925675085681898565034342337875046941306803052, scale precision, 1360925675085681898565034342337875048040818430829, scale precision,
    0, 128, 0, 128, ⟨-104204064467892756966628310773843284725769295122, -104204064467892756966628310773843284725767197969⟩, ⟨-104204064467892756966628310773843283545000886032, -104204064467892756966628310773843283544998788879⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨103721381968098678271045173324731583805157659748, 103721381968098678271045173324731583805157659749⟩
def centerBExp : DyadicInterval precision := ⟨1268108381816549729844874804944596210409385699902, 1268108381816549729844874804944596212608408955455⟩
def centerBLog : DyadicInterval precision := ⟨912991775876267943086525526453637719484850144799, 912991775876267943086525526453637721683873400352⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1268108381816549729844874804944596210959141513790, scale precision, 1268108381816549729844874804944596212058653141567, scale precision,
    0, 128, 0, 128, ⟨-207442763936197356542090346649463168243912860022, -207442763936197356542090346649463168243910762869⟩, ⟨-207442763936197356542090346649463166976719876124, -207442763936197356542090346649463166976717778971⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨49090387085558120317010643908319081445949446151, 53845849274430363340356920789158241656378561385⟩
def wholeDExp : DyadicInterval precision := ⟨1357681920934804568838490939788917161712039721239, 1366546035068101924073630463753607685068326572837⟩
def wholeDLog : DyadicInterval precision := ⟨960181582307675404146178190201383837609742600174, 964769645884129960942701944278613212870985597104⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1357681920934804568838490939788917162261795535127, scale precision, 1366546035068101924073630463753607684518570758949, scale precision,
    0, 128, 0, 128, ⟨-107691698548860726680713841578316483904552913354, -107691698548860726680713841578316483904550816201⟩, ⟨-98180774171116240634021287816638162303943881213, -98180774171116240634021287816638162303941784060⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨49090387085558120317010643908319081445949446151, 55114191349500929383767732776807590001211495095⟩
def wholeCExp : DyadicInterval precision := ⟨1355327477382912160807407512816259138697699329805, 1366546035068101924073630463753607685068326572837⟩
def wholeCLog : DyadicInterval precision := ⟨958960498003603095356594726853619708881235835788, 964769645884129960942701944278613212870985597104⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1355327477382912160807407512816259139247455143693, scale precision, 1366546035068101924073630463753607684518570758949, scale precision,
    0, 128, 0, 128, ⟨-110228382699001858767535465553615180595246832915, -110228382699001858767535465553615180595244735762⟩, ⟨-98180774171116240634021287816638162303943881213, -98180774171116240634021287816638162303941784060⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨98309741716498835487952089708536877216616049748, 109136304863157575849981745590334233255913005862⟩
def wholeBExp : DyadicInterval precision := ⟨1258746325388888982740306017261621818175635827758, 1277534330619707633875339699833693416292156731992⟩
def wholeBLog : DyadicInterval precision := ⟨907970480164479711642721375997620059260516583397, 918029971175151294472245480103499483761218012325⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1258746325388888982740306017261621818725391641646, scale precision, 1277534330619707633875339699833693415742400918104, scale precision,
    0, 128, 0, 128, ⟨-218272609726315151699963491180668467150135991913, -218272609726315151699963491180668467150133894760⟩, ⟨-196619483432997670975904179417073753804311480081, -196619483432997670975904179417073753804309382928⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0010StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0011StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0011StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨46713116010029980514615076818759635730538499645, 46713116010029980514615076818759635730538499646⟩
def centerDExp : DyadicInterval precision := ⟨1370998907719543522785095389796795666922964041466, 1370998907719543522785095389796795669121987297019⟩
def centerDLog : DyadicInterval precision := ⟨967069028121789112925837016599212484240830577134, 967069028121789112925837016599212486439853832687⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1370998907719543522785095389796795667472719855354, scale precision, 1370998907719543522785095389796795668572231483131, scale precision,
    0, 128, 0, 128, ⟨-93426232020059961029230153637519272047124482774, -93426232020059961029230153637519272047122385621⟩, ⟨-93426232020059961029230153637519270875031612960, -93426232020059961029230153637519270875029515807⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨47347026280704359022052696135487566779086284115, 47347026280704359022052696135487566779086284116⟩
def centerCExp : DyadicInterval precision := ⟨1369810112008180772281144368022328811406480282761, 1369810112008180772281144368022328813605503538314⟩
def centerCLog : DyadicInterval precision := ⟨966455509589106140927568541732500652529383358983, 966455509589106140927568541732500654728406614536⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1369810112008180772281144368022328811956236096649, scale precision, 1369810112008180772281144368022328813055747724426, scale precision,
    0, 128, 0, 128, ⟨-94694052561408718044105392270975134144728654682, -94694052561408718044105392270975134144726557529⟩, ⟨-94694052561408718044105392270975132971618578933, -94694052561408718044105392270975132971616481780⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨94173536515609520496219441434446986744413476895, 94173536515609520496219441434446986744413476896⟩
def centerBExp : DyadicInterval precision := ⟨1284785950396523518994958384447558237375476572228, 1284785950396523518994958384447558239574499827781⟩
def centerBLog : DyadicInterval precision := ⟨921894195498007892935102799731546180927157326115, 921894195498007892935102799731546183126180581668⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1284785950396523518994958384447558237925232386116, scale precision, 1284785950396523518994958384447558239024744013893, scale precision,
    0, 128, 0, 128, ⟨-188347073031219040992438882868893974114199895548, -188347073031219040992438882868893974114197798395⟩, ⟨-188347073031219040992438882868893972863456109188, -188347073031219040992438882868893972863454012035⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 49090387085558120317010643908319081445949446152⟩
def wholeDExp : DyadicInterval precision := ⟨1366546035068101924073630463753607682869303317284, 1375465749469112915336031076552653134255992540413⟩
def wholeDLog : DyadicInterval precision := ⟨964769645884129960942701944278613210671962341551, 969371994805781330198871946178310256493558400824⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1366546035068101924073630463753607683419059131172, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-98180774171116240634021287816638163479856000544, -98180774171116240634021287816638163479853903391⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 50358387464788094565508226754163990527967612750⟩
def wholeCExp : DyadicInterval precision := ⟨1364176857568604256874790178069699266527439465291, 1375465749469112915336031076552653134255992540413⟩
def wholeCLog : DyadicInterval precision := ⟨963544769795384609901545553993877875672062457030, 969371994805781330198871946178310256493558400824⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1364176857568604256874790178069699267077195279179, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-100716774929576189131016453508327981644913442008, -100716774929576189131016453508327981644911344855⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨88767269567754834584825661095297626477549199804, 99582782619590846946456695311079788932288258448⟩
def wholeBExp : DyadicInterval precision := ⟨1275310675710689402948086131683640039236663132398, 1294326347490277919388066411782599923462580251022⟩
def wholeBLog : DyadicInterval precision := ⟨916842985962171777418736964129359077345279424595, 926962544122603266974221631602295216623085103625⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1275310675710689402948086131683640039786418946286, scale precision, 1294326347490277919388066411782599922912824437134, scale precision,
    0, 128, 0, 128, ⟨-199165565239181693892913390622159578494595832733, -199165565239181693892913390622159578494593735580⟩, ⟨-177534539135509669169651322190595252334337131411, -177534539135509669169651322190595252334335034258⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0011StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0012StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0012StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨41959420742712281670701379146144140997527296443, 41959420742712281670701379146144140997527296444⟩
def centerDExp : DyadicInterval precision := ⟨1379946629933930331657679320297936454916277018329, 1379946629933930331657679320297936457115300273882⟩
def centerDLog : DyadicInterval precision := ⟨971678559134379732480531149474418344828596219705, 971678559134379732480531149474418347027619475258⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1379946629933930331657679320297936455466032832217, scale precision, 1379946629933930331657679320297936456565544459994, scale precision,
    0, 128, 0, 128, ⟨-83918841485424563341402758292288282577302088319, -83918841485424563341402758292288282577299991166⟩, ⟨-83918841485424563341402758292288281412809194607, -83918841485424563341402758292288281412807097454⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨42593184616700157279002174546188137178366406059, 42593184616700157279002174546188137178366406060⟩
def centerCExp : DyadicInterval precision := ⟨1378750351851109407665205515175028998799746331147, 1378750351851109407665205515175029000998769586700⟩
def centerCLog : DyadicInterval precision := ⟨971063122795372724329116573588195310691640849083, 971063122795372724329116573588195312890664104636⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1378750351851109407665205515175028999349502145035, scale precision, 1378750351851109407665205515175029000449013772812, scale precision,
    0, 128, 0, 128, ⟨-85186369233400314558004349092376274939485495937, -85186369233400314558004349092376274939483398784⟩, ⟨-85186369233400314558004349092376273773982225455, -85186369233400314558004349092376273773980128302⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨84634968829546219504469541596784659832228095922, 84634968829546219504469541596784659832228095923⟩
def centerBExp : DyadicInterval precision := ⟨1301666328226487153855349235809742246990597862318, 1301666328226487153855349235809742249189621117871⟩
def centerBLog : DyadicInterval precision := ⟨930849990420858921420752763571031277777582972273, 930849990420858921420752763571031279976606227826⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1301666328226487153855349235809742247540353676206, scale precision, 1301666328226487153855349235809742248639865303983, scale precision,
    0, 128, 0, 128, ⟨-169269937659092439008939083193569320281719133664, -169269937659092439008939083193569320281717036511⟩, ⟨-169269937659092439008939083193569319047195347180, -169269937659092439008939083193569319047193250027⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨39582967301423713423413965103485819080159470448, 44336132104644388932745897738796280177181849965⟩
def wholeDExp : DyadicInterval precision := ⟨1375465749469112915336031076552653132056969284860, 1384441619203923782885550597943121613215597964582⟩
def wholeDLog : DyadicInterval precision := ⟨969371994805781330198871946178310254294535145271, 973988734376663612812883207699140571860322172920⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1375465749469112915336031076552653132606725098748, scale precision, 1384441619203923782885550597943121612665842150694, scale precision,
    0, 128, 0, 128, ⟨-88672264209288777865491795477592560938507990487, -88672264209288777865491795477592560938505893334⟩, ⟨-79165934602847426846827930206971637579963973744, -79165934602847426846827930206971637579961876591⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨39582967301423713423413965103485819080159470448, 45603822007427965209743755626378939214500302404⟩
def wholeCExp : DyadicInterval precision := ⟨1373081691268201893610801308403049805626026600993, 1384441619203923782885550597943121613215597964582⟩
def wholeCLog : DyadicInterval precision := ⟨968143299041892371692199594756639106359771954853, 973988734376663612812883207699140571860322172920⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1373081691268201893610801308403049806175782414881, scale precision, 1384441619203923782885550597943121612665842150694, scale precision,
    0, 128, 0, 128, ⟨-91207644014855930419487511252757879014159133263, -91207644014855930419487511252757879014157036110⟩, ⟨-79165934602847426846827930206971637579963973744, -79165934602847426846827930206971637579961876591⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096871869275, 90039073446665143782344453410578939042533249235⟩
def wholeBExp : DyadicInterval precision := ⟨1292075651917351569123771717317878746813884597221, 1311323390486212533981803318339124544384464892381⟩
def wholeBLog : DyadicInterval precision := ⟨925768442296972979924489385850065357218572549765, 935948922676490622602857379124864312093157411787⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1292075651917351569123771717317878747363640411109, scale precision, 1311323390486212533981803318339124543834709078493, scale precision,
    0, 128, 0, 128, ⟨-180078146893330287564688906821157878706911183630, -180078146893330287564688906821157878706909086477⟩, ⟨-158467081097196404323724233909852887581028634911, -158467081097196404323724233909852887581026537758⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0012StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0013StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0013StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨37206757161641482619932256052528860593904680845, 37206757161641482619932256052528860593904680846⟩
def centerDExp : DyadicInterval precision := ⟨1388950787845256886456725666204969956264618651552, 1388950787845256886456725666204969958463641907105⟩
def centerDLog : DyadicInterval precision := ⟨976302533872699309670390604038035412903529768221, 976302533872699309670390604038035415102553023774⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1388950787845256886456725666204969956814374465440, scale precision, 1388950787845256886456725666204969957913886093217, scale precision,
    0, 128, 0, 128, ⟨-74413514323282965239864512105057721766282325300, -74413514323282965239864512105057721766280228147⟩, ⟨-74413514323282965239864512105057720609338495235, -74413514323282965239864512105057720609336398082⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨37840390235191305892336944079192201941563681197, 37840390235191305892336944079192201941563681198⟩
def centerCExp : DyadicInterval precision := ⟨1387746952441778045686980109656109681935886508188, 1387746952441778045686980109656109684134909763741⟩
def centerCLog : DyadicInterval precision := ⟨975685165545901457318424736603544462165725957104, 975685165545901457318424736603544464364749212657⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1387746952441778045686980109656109682485642322076, scale precision, 1387746952441778045686980109656109683585153949853, scale precision,
    0, 128, 0, 128, ⟨-75680780470382611784673888158384404462102135768, -75680780470382611784673888158384404462100038615⟩, ⟨-75680780470382611784673888158384403304154686175, -75680780470382611784673888158384403304152589022⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨75104735860464000039654512611793576370486962764, 75104735860464000039654512611793576370486962765⟩
def centerBExp : DyadicInterval precision := ⟨1318753450381580412863595815200602612723987019566, 1318753450381580412863595815200602614923010275119⟩
def centerBLog : DyadicInterval precision := ⟨939859923763028657024581547280875579540660982398, 939859923763028657024581547280875581739684237951⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1318753450381580412863595815200602613273742833454, scale precision, 1318753450381580412863595815200602614373254461231, scale precision,
    0, 128, 0, 128, ⟨-150209471720928000079309025223587153350238989224, -150209471720928000079309025223587153350236892071⟩, ⟨-150209471720928000079309025223587152131710958988, -150209471720928000079309025223587152131708861835⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨34830775707694518323356855819802492385993843109, 39582967301423713423413965103485819080159470449⟩
def wholeDExp : DyadicInterval precision := ⟨1384441619203923782885550597943121611016574709029, 1393474206903787201785230037422771621528978564036⟩
def wholeDLog : DyadicInterval precision := ⟨973988734376663612812883207699140569661298917367, 978619971033722696354607064598753115511294545328⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1384441619203923782885550597943121611566330522917, scale precision, 1393474206903787201785230037422771620979222750148, scale precision,
    0, 128, 0, 128, ⟨-79165934602847426846827930206971638740676005201, -79165934602847426846827930206971638740673908048⟩, ⟨-69661551415389036646713711639604984195394623365, -69661551415389036646713711639604984195392526212⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨34830775707694518323356855819802492385993843109, 40850377929490787525132265847486563880844462281⟩
def wholeCExp : DyadicInterval precision := ⟨1382042531548774472754394678349177424965897883659, 1393474206903787201785230037422771621528978564036⟩
def wholeCLog : DyadicInterval precision := ⟨972756190746019273686271467148684857525744169409, 978619971033722696354607064598753115511294545328⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1382042531548774472754394678349177425515653697547, scale precision, 1393474206903787201785230037422771620979222750148, scale precision,
    0, 128, 0, 128, ⟨-81700755858981575050264531694973128343053428885, -81700755858981575050264531694973128343051331732⟩, ⟨-69661551415389036646713711639604984195394623365, -69661551415389036646713711639604984195392526212⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨69707612696994983038122081738595481911167034584, 80504233142141611642933172006386671113699818849⟩
def wholeBExp : DyadicInterval precision := ⟨1309045129588817403044812046386576903929543094186, 1328529455126788247381324478097073719567411994040⟩
def wholeBLog : DyadicInterval precision := ⟨934747602489940959407298357260346040404373450625, 944989879800761038932679125711787605107730027645⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1309045129588817403044812046386576904479298908074, scale precision, 1328529455126788247381324478097073719017656180152, scale precision,
    0, 128, 0, 128, ⟨-161008466284283223285866344012773342841183209099, -161008466284283223285866344012773342841181111946⟩, ⟨-139415225393989966076244163477190963217554381400, -139415225393989966076244163477190963217552284247⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0013StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0015StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0015StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨28891726686864493073308866557218512689468036345, 28891726686864493073308866557218512689468036346⟩
def centerDExp : DyadicInterval precision := ⟨1404845570733299448806020978545363434893586848252, 1404845570733299448806020978545363437092610103805⟩
def centerDLog : DyadicInterval precision := ⟨984429567376195802766596711550261497182688044895, 984429567376195802766596711550261499381711300448⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1404845570733299448806020978545363435443342662140, scale precision, 1404845570733299448806020978545363436542854289917, scale precision,
    0, 128, 0, 128, ⟨-57783453373728986146617733114437025950864056774, -57783453373728986146617733114437025950861959621⟩, ⟨-57783453373728986146617733114437024807010185760, -57783453373728986146617733114437024807008088607⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨29208445930956847001745901419912041242994854069, 29208445930956847001745901419912041242994854070⟩
def centerCExp : DyadicInterval precision := ⟨1404236819833074111635485632719571415897569387518, 1404236819833074111635485632719571418096592643071⟩
def centerCLog : DyadicInterval precision := ⟨984119142692158780108535358453974810836928627780, 984119142692158780108535358453974813035951883333⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1404236819833074111635485632719571416447325201406, scale precision, 1404236819833074111635485632719571417546836829183, scale precision,
    0, 128, 0, 128, ⟨-58416891861913694003491802839824083058165628347, -58416891861913694003491802839824083058163531194⟩, ⟨-58416891861913694003491802839824081913815885081, -58416891861913694003491802839824081913813787928⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨58126894187953343854819435514497108971398845100, 58126894187953343854819435514497108971398845101⟩
def centerBExp : DyadicInterval precision := ⟨1349751303692396389863417078706891290236382775426, 1349751303692396389863417078706891292435406030979⟩
def centerBLog : DyadicInterval precision := ⟨956064452933657876698540702963988539410987956707, 956064452933657876698540702963988541610011212260⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1349751303692396389863417078706891290786138589314, scale precision, 1349751303692396389863417078706891291885650217091, scale precision,
    0, 128, 0, 128, ⟨-116253788375906687709638871028994218538070638077, -116253788375906687709638871028994218538068540924⟩, ⟨-116253788375906687709638871028994217347526839479, -116253788375906687709638871028994217347524742326⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1407130684310035281592181556628555968954183377026⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 985594243690497964310298929048384652090474380348⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30712906510507917234502164183742803301164702364⟩
def wholeCExp : DyadicInterval precision := ⟨1401348768720553324036225060278420615938848935074, 1407130684310035281592181556628555968954183377026⟩
def wholeCLog : DyadicInterval precision := ⟨982645519121667378070732396231484449175146225372, 985594243690497964310298929048384652090474380348⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1401348768720553324036225060278420616488604748962, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-61425813021015834469004328367485607175684524799, -61425813021015834469004328367485607175682427646⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨55431291843038576317649119811896400965808125883, 60822955643229857628256257214766697813574124014⟩
def wholeBExp : DyadicInterval precision := ⟨1344780652055839977465096103447757877808053269800, 1354739476977498872460179569071634781883400195606⟩
def wholeBLog : DyadicInterval precision := ⟨953478045513531253803742851842590029293375265462, 958655384265110573140733977981650086419547699316⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1344780652055839977465096103447757878357809083688, scale precision, 1354739476977498872460179569071634781333644381718, scale precision,
    0, 128, 0, 128, ⟨-121645911286459715256512514429533396224621472383, -121645911286459715256512514429533396224619375230⟩, ⟨-110862583686077152635298239623792801338537202079, -110862583686077152635298239623792801338535104926⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0015StableWitnesses

end


