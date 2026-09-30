-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0042StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0042StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:48:43.300759+00:00
-- url     : https://prove2.me/theorems/dd0e3ffe-4f02-4a5a-8dfe-475ea96cc1b0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0042StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0043StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0042StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0043StableWitnesses, GeneralCK.Certificates.E8TAxisProd0044StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0042StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0043StableWitnesses, GeneralCK.Certificates.E8TAxisProd0044StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0042StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0043StableWitnesses, GeneralCK.Certificates.E8TAxisProd0044StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0042StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0043StableWitnesses, GeneralCK/Certificates/E8TAxisProd0044StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0042StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0042StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨115032946497916170088737142525822549131339623218, 115032946497916170088737142525822549131339623219⟩
def centerDExp : DyadicInterval precision := ⟨1248630004573113102149096526493550178299957551294, 1248630004573113102149096526493550180498980806847⟩
def centerDLog : DyadicInterval precision := ⟨902525175189120016129211831586767280434114094617, 902525175189120016129211831586767282633137350170⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1248630004573113102149096526493550178849713365182, scale precision, 1248630004573113102149096526493550179949224992959, scale precision,
    0, 128, 0, 128, ⟨-230065892995832340177474285051645098906160764959, -230065892995832340177474285051645098906158667806⟩, ⟨-230065892995832340177474285051645097619199825069, -230065892995832340177474285051645097619197727916⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨116946286482606675496618989933559049782940784740, 116946286482606675496618989933559049782940784741⟩
def centerCExp : DyadicInterval precision := ⟨1245364967126066099211065003480390993594716300988, 1245364967126066099211065003480390995793739556541⟩
def centerCLog : DyadicInterval precision := ⟨900763366181382189926550775030646374771493382092, 900763366181382189926550775030646376970516637645⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1245364967126066099211065003480390994144472114876, scale precision, 1245364967126066099211065003480390995243983742653, scale precision,
    0, 128, 0, 128, ⟨-233892572965213350993237979867118100211050133878, -233892572965213350993237979867118100211048036725⟩, ⟨-233892572965213350993237979867118098920715102237, -233892572965213350993237979867118098920713005084⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨233681671635039144761899573780282067648184319234, 233681671635039144761899573780282067648184319235⟩
def centerBExp : DyadicInterval precision := ⟨1061498352066095884067179771616752342755095415174, 1061498352066095884067179771616752344954118670727⟩
def centerBLog : DyadicInterval precision := ⟨797956860102054195230619147335081589706255247658, 797956860102054195230619147335081591905278503211⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1061498352066095884067179771616752343304851229062, scale precision, 1061498352066095884067179771616752344404362856839, scale precision,
    0, 128, 0, 128, ⟨-467363343270078289523799147560564136053289394519, -467363343270078289523799147560564136053287297366⟩, ⟨-467363343270078289523799147560564134539449979571, -467363343270078289523799147560564134539447882418⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨111048270122241576078328386047482676587330985904, 119019592332330079773337734920394720791278241018⟩
def wholeDExp : DyadicInterval precision := ⟨1241836591959774864289057338296444368505369446693, 1255457196643991312782767932801799989113568160976⟩
def wholeDLog : DyadicInterval precision := ⟨898857069849833759981739512399832699836653175595, 906202267987834631995011695345793201716926871713⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1241836591959774864289057338296444369055125260581, scale precision, 1255457196643991312782767932801799988563812347088, scale precision,
    0, 128, 0, 128, ⟨-238039184664660159546675469840789442229558132246, -238039184664660159546675469840789442229556035093⟩, ⟨-222096540244483152156656772094965352534681805353, -222096540244483152156656772094965352534679708200⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨112323156467442955010968215135395036933059521668, 121572110958318617549910999863282960483547397041⟩
def wholeCExp : DyadicInterval precision := ⟨1237506413596899800280902874213208097376964133575, 1253268803809595188304966484721289876269894264032⟩
def wholeCLog : DyadicInterval precision := ⟨896514175190994470540006811065962630719526473327, 905024617290735910973596382386661962442987586466⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1237506413596899800280902874213208097926719947463, scale precision, 1253268803809595188304966484721289875720138450144, scale precision,
    0, 128, 0, 128, ⟨-243144221916637235099821999726565921616360374383, -243144221916637235099821999726565921616358277230⟩, ⟨-224646312934885910021936430270790073225021374952, -224646312934885910021936430270790073225019277799⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨224891258230253913064710509213309086355856044062, 242490916659753179449762138168969105284430212068⟩
def wholeBExp : DyadicInterval precision := ⟨1048778747491402917119097353667193949975927596083, 1074344533730943943617918492684994412399216515300⟩
def wholeBLog : DyadicInterval precision := ⟨790570121791082467784100830538504733032281088239, 805379404807415472260164889560497954347127117880⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1048778747491402917119097353667193950525683409971, scale precision, 1074344533730943943617918492684994411849460701412, scale precision,
    0, 128, 0, 128, ⟨-484981833319506358899524276337938211334961113893, -484981833319506358899524276337938211334959016740⟩, ⟨-449782516460507826129421018426618171963844090131, -449782516460507826129421018426618171963841992978⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0042StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0043StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0043StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨107065494589907116025240672481192988302250052280, 107065494589907116025240672481192988302250052281⟩
def centerDExp : DyadicInterval precision := ⟨1262318434497260164208401614240797141306259170539, 1262318434497260164208401614240797143505282426092⟩
def centerDLog : DyadicInterval precision := ⟨909888400376604858648946115122446892680058539307, 909888400376604858648946115122446894879081794860⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1262318434497260164208401614240797141856014984427, scale precision, 1262318434497260164208401614240797142955526612204, scale precision,
    0, 128, 0, 128, ⟨-214130989179814232050481344962385977241003797932, -214130989179814232050481344962385977241001700779⟩, ⟨-214130989179814232050481344962385975967998508344, -214130989179814232050481344962385975967996411191⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨108976993955917756773452715405137662308279193623, 108976993955917756773452715405137662308279193624⟩
def centerCExp : DyadicInterval precision := ⟨1259020774454877403503374053361450275205530720503, 1259020774454877403503374053361450277404553976056⟩
def centerCLog : DyadicInterval precision := ⟨908117925372432517740527183211960120081295635712, 908117925372432517740527183211960122280318891265⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1259020774454877403503374053361450275755286534391, scale precision, 1259020774454877403503374053361450276854798162168, scale precision,
    0, 128, 0, 128, ⟨-217953987911835513546905430810275325254729224942, -217953987911835513546905430810275325254727127789⟩, ⟨-217953987911835513546905430810275323978389646704, -217953987911835513546905430810275323978387549551⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨217417439704053488995770589174390533044902703769, 217417439704053488995770589174390533044902703770⟩
def centerBExp : DyadicInterval precision := ⟨1085388869505506174702796711066082459117268183193, 1085388869505506174702796711066082461316291438746⟩
def centerBLog : DyadicInterval precision := ⟨811730841541090239746954400894905887936212490830, 811730841541090239746954400894905890135235746383⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1085388869505506174702796711066082459667023997081, scale precision, 1085388869505506174702796711066082460766535624858, scale precision,
    0, 128, 0, 128, ⟨-434834879408106977991541178348781066830065587845, -434834879408106977991541178348781066830063490692⟩, ⟨-434834879408106977991541178348781065349547324383, -434834879408106977991541178348781065349545227230⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨103084551358829778834915002511195342403115231675, 111048270122241576078328386047482676587330985905⟩
def wholeDExp : DyadicInterval precision := ⟨1255457196643991312782767932801799986914544905423, 1269213987453105464161597200857722394416664115457⟩
def wholeDLog : DyadicInterval precision := ⟨906202267987834631995011695345793199517903616160, 913583624998653703523149262826058897164757379534⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1255457196643991312782767932801799987464300719311, scale precision, 1269213987453105464161597200857722393866908301569, scale precision,
    0, 128, 0, 128, ⟨-222096540244483152156656772094965353814644235419, -222096540244483152156656772094965353814642138266⟩, ⟨-206169102717659557669830005022390684173186942555, -206169102717659557669830005022390684173184845402⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨104358258011611726998445045028828451687585466341, 113598239705995084404205697354797805075838982127⟩
def wholeCExp : DyadicInterval precision := ⟨1251083888480320811413471717281821796178546720901, 1267003660491626537512866653176074205856514548492⟩
def wholeCLog : DyadicInterval precision := ⟨903847890529817803406659632589687593722886300910, 912400160656194878996222611181732226831622735125⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1251083888480320811413471717281821796728302534789, scale precision, 1267003660491626537512866653176074205306758734604, scale precision,
    0, 128, 0, 128, ⟨-227196479411990168808411394709595610793897356084, -227196479411990168808411394709595610793895258931⟩, ⟨-208716516023223453996890090057656902741023046111, -208716516023223453996890090057656902741020948958⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨208659993168738163327113473155546913729082918462, 226192381607875787764973691711067383103547195307⟩
def wholeBExp : DyadicInterval precision := ⟨1072433333592369868803923397647789074482818890749, 1098474615239151709131967435382893981734053878460⟩
def wholeBLog : DyadicInterval precision := ⟨804277494414882387092884188447412246493984831763, 819220710211348203542880090538222365260338778264⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1072433333592369868803923397647789075032574704637, scale precision, 1098474615239151709131967435382893981184298064572, scale precision,
    0, 128, 0, 128, ⟨-452384763215751575529947383422134766956297274832, -452384763215751575529947383422134766956295177679⟩, ⟨-417319986337476326654226946311093826726726203137, -417319986337476326654226946311093826726724105984⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0043StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0044StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0044StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨99105371957748756558358702025034649328540468989, 99105371957748756558358702025034649328540468990⟩
def centerDExp : DyadicInterval precision := ⟨1276144127861541994145963581661485621034162019732, 1276144127861541994145963581661485623233185275285⟩
def centerDLog : DyadicInterval precision := ⟨917287995011510229356867982908921321385400443938, 917287995011510229356867982908921323584423699491⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1276144127861541994145963581661485621583917833620, scale precision, 1276144127861541994145963581661485622683429461397, scale precision,
    0, 128, 0, 128, ⟨-198210743915497513116717404050069299286688787692, -198210743915497513116717404050069299286686690539⟩, ⟨-198210743915497513116717404050069298027475185421, -198210743915497513116717404050069298027473088268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨101015162271107827753493254530368148050498460383, 101015162271107827753493254530368148050498460384⟩
def centerCExp : DyadicInterval precision := ⟨1272813326608497994755527561486235398857010750319, 1272813326608497994755527561486235401056034005872⟩
def centerCLog : DyadicInterval precision := ⟨915508752678772655197306125671157169907361757448, 915508752678772655197306125671157172106385013001⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1272813326608497994755527561486235399406766564207, scale precision, 1272813326608497994755527561486235400506278191984, scale precision,
    0, 128, 0, 128, ⟨-202030324542215655506986509060736296732252376675, -202030324542215655506986509060736296732250279522⟩, ⟨-202030324542215655506986509060736295469743562014, -202030324542215655506986509060736295469741464861⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨201213207599686218730380712951692289967866670111, 201213207599686218730380712951692289967866670112⟩
def centerBExp : DyadicInterval precision := ⟨1109725956617690410777644231088260961951285083174, 1109725956617690410777644231088260964150308338727⟩
def centerBLog : DyadicInterval precision := ⟨825630075612994710682550141220154714959533469555, 825630075612994710682550141220154717158556725108⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1109725956617690410777644231088260962501040897062, scale precision, 1109725956617690410777644231088260963600552524839, scale precision,
    0, 128, 0, 128, ⟨-402426415199372437460761425903384580659759106199, -402426415199372437460761425903384580659757009046⟩, ⟨-402426415199372437460761425903384579211709671401, -402426415199372437460761425903384579211707574248⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733806994, 103084551358829778834915002511195342403115231676⟩
def wholeDExp : DyadicInterval precision := ⟨1269213987453105464161597200857722392217640859904, 1283109131137421329953040259475754031879254989498⟩
def wholeDLog : DyadicInterval precision := ⟨913583624998653703523149262826058894965734123981, 921001564088758741914731412563984562181431746082⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1269213987453105464161597200857722392767396673792, scale precision, 1283109131137421329953040259475754031329499175610, scale precision,
    0, 128, 0, 128, ⟨-206169102717659557669830005022390685439276081302, -206169102717659557669830005022390685439273984149⟩, ⟨-190255775967434873148705478927036470479279507931, -190255775967434873148705478927036470479277410778⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨96400502557886147002287983842112166506463198112, 105632147522948726430034597027139165605022884110⟩
def wholeCExp : DyadicInterval precision := ⟨1264796866303566207571429692709404438563736867156, 1280876520102510064005287526572790117664214634029⟩
def wholeCLog : DyadicInterval precision := ⟨911217631050199692609930985507329344794268436072, 919812217834489480032069487694193340986697633531⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1264796866303566207571429692709404439113492681044, scale precision, 1280876520102510064005287526572790117114458820141, scale precision,
    0, 128, 0, 128, ⟨-211264295045897452860069194054278331845302203283, -211264295045897452860069194054278331845300106130⟩, ⟨-192801005115772294004575967684224332385646821323, -192801005115772294004575967684224332385644724170⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨192486267482474676822962020884762084766255799607, 209956316671997090000842133265351880706535748529⟩
def wholeBExp : DyadicInterval precision := ⟨1096527691430814070408977739606207487193086405799, 1123058232017299231234434758861740124267546850256⟩
def wholeBLog : DyadicInterval precision := ⟨818108780016791024693045805775745553862022319202, 833188643880544430188545489483369909169399985973⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1096527691430814070408977739606207487742842219687, scale precision, 1123058232017299231234434758861740123717791036368, scale precision,
    0, 128, 0, 128, ⟨-419912633343994180001684266530703762145811926872, -419912633343994180001684266530703762145809829719⟩, ⟨-384972534964949353645924041769524168817083118651, -384972534964949353645924041769524168817081021498⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0044StableWitnesses

end


