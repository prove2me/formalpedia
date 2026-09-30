-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0025StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0025StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:54:35.128315+00:00
-- url     : https://prove2.me/theorems/47c0f2a3-bdb9-412e-acaf-730190f7f83a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0025StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0026StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0025StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0026StableWitnesses, GeneralCK.Certificates.E8TAxisProd0027StableWitnesses, GeneralCK.Certificates.E8TAxisProd0029StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0025StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0026StableWitnesses, GeneralCK.Certificates.E8TAxisProd0027StableWitnesses, GeneralCK.Certificates.E8TAxisProd0029StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0025StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0026StableWitnesses, GeneralCK.Certificates.E8TAxisProd0027StableWitnesses, GeneralCK.Certificates.E8TAxisProd0029StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0025StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0026StableWitnesses, GeneralCK/Certificates/E8TAxisProd0027StableWitnesses, GeneralCK/Certificates/E8TAxisProd0029StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0025StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0025StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨43860768496766159427869749838833067361716087425, 43860768496766159427869749838833067361716087426⟩
def centerCExp : DyadicInterval precision := ⟨1376360800228808921311124489185785280578555586946, 1376360800228808921311124489185785282777578842499⟩
def centerCLog : DyadicInterval precision := ⟨969833019436342728581468974910634532650706508841, 969833019436342728581468974910634534849729764394⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1376360800228808921311124489185785281128311400834, scale precision, 1376360800228808921311124489185785282227823028611, scale precision,
    0, 128, 0, 128, ⟨-87721536993532318855739499677666135307196595646, -87721536993532318855739499677666135307194498493⟩, ⟨-87721536993532318855739499677666134139669851210, -87721536993532318855739499677666134139667754057⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨85906275728821593024606426695861450515629767237, 85906275728821593024606426695861450515629767238⟩
def centerBExp : DyadicInterval precision := ⟨1299403752926418098992940291339903065555149779400, 1299403752926418098992940291339903067754173034953⟩
def centerBLog : DyadicInterval precision := ⟨929652773266938244148227191584431047940688573165, 929652773266938244148227191584431050139711828718⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1299403752926418098992940291339903066104905593288, scale precision, 1299403752926418098992940291339903067204417221065, scale precision,
    0, 128, 0, 128, ⟨-171812551457643186049212853391722901649597278109, -171812551457643186049212853391722901649595180956⟩, ⟨-171812551457643186049212853391722900412923887993, -171812551457643186049212853391722900412921790840⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨40850377929490787525132265847486563880844462280, 46871591652396955948239255283142047275791395946⟩
def wholeCExp : DyadicInterval precision := ⟨1370701615716012189539119176421333096411901624091, 1382042531548774472754394678349177427164921139212⟩
def wholeCLog : DyadicInterval precision := ⟨966915624602095365704810787008635852288416019661, 972756190746019273686271467148684859724767424962⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1370701615716012189539119176421333096961657437979, scale precision, 1382042531548774472754394678349177426615165325324, scale precision,
    0, 128, 0, 128, ⟨-93743183304793911896478510566284095137757383212, -93743183304793911896478510566284095137755286059⟩, ⟨-81700755858981575050264531694973127180326517392, -81700755858981575050264531694973127180324420239⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨80504233142141611642933172006386671113699818848, 91311034991450526690257298210518105305139512279⟩
def wholeBExp : DyadicInterval precision := ⟨1289828591772333900582106418481172346383940129373, 1309045129588817403044812046386576906128566349739⟩
def wholeBLog : DyadicInterval precision := ⟨924575295181394674888129935513667207246540453139, 934747602489940959407298357260346042603396706178⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1289828591772333900582106418481172346933695943261, scale precision, 1309045129588817403044812046386576905578810535851, scale precision,
    0, 128, 0, 128, ⟨-182622069982901053380514596421036211233207047505, -182622069982901053380514596421036211233204950352⟩, ⟨-161008466284283223285866344012773341613618163450, -161008466284283223285866344012773341613616066297⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0025StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0026StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0026StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨39107706277096836940774231574352615804253481455, 39107706277096836940774231574352615804253481456⟩
def centerCExp : DyadicInterval precision := ⟨1385342316315945397940282454262541132616560239215, 1385342316315945397940282454262541134815583494768⟩
def centerCLog : DyadicInterval precision := ⟨974451203907437061916813820279207484389720112455, 974451203907437061916813820279207486588743368008⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1385342316315945397940282454262541133166316053103, scale precision, 1385342316315945397940282454262541134265827680880, scale precision,
    0, 128, 0, 128, ⟨-78215412554193673881548463148705232188486701713, -78215412554193673881548463148705232188484604560⟩, ⟨-78215412554193673881548463148705231028529321263, -78215412554193673881548463148705231028527224110⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨76374985881963571005968758312776897107481839193, 76374985881963571005968758312776897107481839194⟩
def centerBExp : DyadicInterval precision := ⟨1316463077984154067335507827451789360010015547518, 1316463077984154067335507827451789362209038803071⟩
def centerBLog : DyadicInterval precision := ⟨938655443437664033907002461647759913077301408905, 938655443437664033907002461647759915276324664458⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1316463077984154067335507827451789360559771361406, scale precision, 1316463077984154067335507827451789361659282989183, scale precision,
    0, 128, 0, 128, ⟨-152749971763927142011937516625553794825288734955, -152749971763927142011937516625553794825286637802⟩, ⟨-152749971763927142011937516625553793604640718969, -152749971763927142011937516625553793604638621816⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨36097938246870058546958457136650379086153782135, 42117859980909830503480774531012101070616760210⟩
def wholeCExp : DyadicInterval precision := ⟨1379647466406858027522323513753790949644910570372, 1391059939013504036843525882064723713679662965519⟩
def wholeCLog : DyadicInterval precision := ⟨971524675986761039573550901211246878397029605455, 977383551042037225952002295716720301818895510063⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1379647466406858027522323513753790950194666384260, scale precision, 1391059939013504036843525882064723713129907151631, scale precision,
    0, 128, 0, 128, ⟨-84235719961819661006961549062024202723607270496, -84235719961819661006961549062024202723605173343⟩, ⟨-72195876493740117093916914273300757594713787782, -72195876493740117093916914273300757594711690629⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨70977319494027914470138645364705689093823642822, 81775066651422335775660018154838453034717622375⟩
def wholeBExp : DyadicInterval precision := ⟨1306770574892044410141964846722889501420659583114, 1326223089935828755009860249456747406383889881462⟩
def wholeBLog : DyadicInterval precision := ⟨933547250713536054780546866575375685442815155182, 943781237183937452238576505826193086503727820955⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1306770574892044410141964846722889501970415397002, scale precision, 1326223089935828755009860249456747405834134067574, scale precision,
    0, 128, 0, 128, ⟨-163550133302844671551320036309676906684287161234, -163550133302844671551320036309676906684285064081⟩, ⟨-141954638988055828940277290729411377581815855336, -141954638988055828940277290729411377581813758183⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0026StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0027StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0027StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 32455008327171042732967145611016798201694283383⟩
def centerDExp : DyadicInterval precision := ⟨1398011947908555347946217879565997676739193473356, 1398011947908555347946217879565997678938216728909⟩
def centerDLog : DyadicInterval precision := ⟨980941059342323278062008541570423721439995577604, 980941059342323278062008541570423723639018833157⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1398011947908555347946217879565997677288949287244, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-64910016654342085465934291222033596978112187156, -64910016654342085465934291222033596978110090003⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨34355605573258088945334955873702879143933967628, 34355605573258088945334955873702879143933967629⟩
def centerCExp : DyadicInterval precision := ⟨1394380607051568937157594261767049270886468629598, 1394380607051568937157594261767049273085491885151⟩
def centerCLog : DyadicInterval precision := ⟨979083896170935862718206209575299149042628845753, 979083896170935862718206209575299151241652101306⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1394380607051568937157594261767049271436224443486, scale precision, 1394380607051568937157594261767049272535736071263, scale precision,
    0, 128, 0, 128, ⟨-68711211146516177890669911747405758864088287277, -68711211146516177890669911747405758864086190124⟩, ⟨-68711211146516177890669911747405757711649680390, -68711211146516177890669911747405757711647583237⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨66851214966288020615652614474858511769550484953, 66851214966288020615652614474858511769550484954⟩
def centerBExp : DyadicInterval precision := ⟨1333732644465142918244754744225873804587369638660, 1333732644465142918244754744225873806786392894213⟩
def centerBLog : DyadicInterval precision := ⟨947712927472689031935025397022671173707323142478, 947712927472689031935025397022671175906346398031⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1333732644465142918244754744225873805137125452548, scale precision, 1333732644465142918244754744225873806236637080325, scale precision,
    0, 128, 0, 128, ⟨-133702429932576041231305228949717024141523369916, -133702429932576041231305228949717024141521272763⟩, ⟨-133702429932576041231305228949717022936680667048, -133702429932576041231305228949717022936678569895⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153469388, 34830775707694518323356855819802492385993843110⟩
def wholeDExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1402564082875305177309105820725636622954765925773⟩
def wholeDLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 983265812352629886822137551849227704024579594240⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1402564082875305177309105820725636622405010111885, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-60158880821423046134148083721089853083450724046, -60158880821423046134148083721089853083448626893⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨31346386032679070535045081536548693653924672478, 37365163894633166934139863628747988917988881051⟩
def wholeCExp : DyadicInterval precision := ⟨1388649734044654119234359722553860932945539022911, 1400134481911348653688989637727172606715982560919⟩
def wholeCLog : DyadicInterval precision := ⟨976148167549896511977221673672472961671603524501, 982025487201383144445202772375046411806502327038⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1388649734044654119234359722553860933495294836799, scale precision, 1400134481911348653688989637727172606166226747031, scale precision,
    0, 128, 0, 128, ⟨-74730327789266333868279727257495978414576136146, -74730327789266333868279727257495978414574038993⟩, ⟨-62692772065358141070090163073097386733999072458, -62692772065358141070090163073097386733996975305⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨61457392076055156498029487396398058132119341835, 72247150488409424271229859008789322648796023084⟩
def wholeBExp : DyadicInterval precision := ⟨1323920503649282092956694500381848421519630865539, 1343613622801088944511759060966816955704487896919⟩
def wholeBLog : DyadicInterval precision := ⟨942573576988029917998135757461079987510309572818, 952870134498076907370678439784785833837070021022⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1323920503649282092956694500381848422069386679427, scale precision, 1343613622801088944511759060966816955154732083031, scale precision,
    0, 128, 0, 128, ⟨-144494300976818848542459718017578645904479248343, -144494300976818848542459718017578645904477151190⟩, ⟨-122914784152110312996058974792796115666248607048, -122914784152110312996058974792796115666246509895⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0027StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0029StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0029StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨30475355165025993017494601641177695851462554448, 30475355165025993017494601641177695851462554449⟩
def centerCExp : DyadicInterval precision := ⟨1401804391062551113417608753122537973562415299669, 1401804391062551113417608753122537975761438555222⟩
def centerCLog : DyadicInterval precision := ⟨982878098447036142052069827287644417312223565163, 982878098447036142052069827287644419511246820716⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1401804391062551113417608753122537974112171113557, scale precision, 1401804391062551113417608753122537975211682741334, scale precision,
    0, 128, 0, 128, ⟨-60950710330051986034989203282355392276093874206, -60950710330051986034989203282355392276091777053⟩, ⟨-60950710330051986034989203282355391129758440742, -60950710330051986034989203282355391129756343589⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨59395570497876155871827030919663866166637369624, 59395570497876155871827030919663866166637369625⟩
def centerBExp : DyadicInterval precision := ⟨1347409996848020761489776342990284079242469447724, 1347409996848020761489776342990284081441492703277⟩
def centerBLog : DyadicInterval precision := ⟨954846757637119094317035204684427443722289228504, 954846757637119094317035204684427445921312484057⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1347409996848020761489776342990284079792225261612, scale precision, 1347409996848020761489776342990284080891736889389, scale precision,
    0, 128, 0, 128, ⟨-118791140995752311743654061839327732929582052443, -118791140995752311743654061839327732929579955290⟩, ⟨-118791140995752311743654061839327731736969523206, -118791140995752311743654061839327731736967426053⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨28970906200610226455572444536056688958626202819, 31979879254202141632754280872451116846196146086⟩
def wholeCExp : DyadicInterval precision := ⟨1398921221071837101259074561931713634018288384467, 1404693358843559643395315496180722841618823701283⟩
def wholeCLog : DyadicInterval precision := ⟨981405716333254798664228969930567514235146701471, 984351955064518882387948220261005847101884602265⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1398921221071837101259074561931713634568044198355, scale precision, 1404693358843559643395315496180722841069067887395, scale precision,
    0, 128, 0, 128, ⟨-63959758508404283265508561744902234266742353421, -63959758508404283265508561744902234266740256268⟩, ⟨-57941812401220452911144889072113377345264544985, -57941812401220452911144889072113377345262447832⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨56699754757671754622654702159398489524282633260, 62091855385633174163343427359524556513592908542⟩
def wholeBExp : DyadicInterval precision := ⟨1342447556944409104672146832061141263615537488170, 1352389912470905746515802614073206789203217545336⟩
def wholeBLog : DyadicInterval precision := ⟨952262472668844398759546987704520907738711710201, 957435557743212078261424134828821331847652814343⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1342447556944409104672146832061141264165293302058, scale precision, 1352389912470905746515802614073206788653461731448, scale precision,
    0, 128, 0, 128, ⟨-124183710771266348326686854719049113625697413036, -124183710771266348326686854719049113625695315883⟩, ⟨-113399509515343509245309404318796978454455833556, -113399509515343509245309404318796978454453736403⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0029StableWitnesses

end


