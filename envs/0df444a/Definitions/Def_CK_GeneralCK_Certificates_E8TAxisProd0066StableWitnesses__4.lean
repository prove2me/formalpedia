-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0066StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0066StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:59:10.543336+00:00
-- url     : https://prove2.me/theorems/d6afaf52-68d5-4b99-843f-da79b8957955
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0066StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0067StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0066StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0067StableWitnesses, GeneralCK.Certificates.E8TAxisProd0068StableWitnesses, GeneralCK.Certificates.E8TAxisProd0069StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0066StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0067StableWitnesses, GeneralCK.Certificates.E8TAxisProd0068StableWitnesses, GeneralCK.Certificates.E8TAxisProd0069StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0066StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0067StableWitnesses, GeneralCK.Certificates.E8TAxisProd0068StableWitnesses, GeneralCK.Certificates.E8TAxisProd0069StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0066StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0067StableWitnesses, GeneralCK/Certificates/E8TAxisProd0068StableWitnesses, GeneralCK/Certificates/E8TAxisProd0069StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0066StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0066StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨231726644506236789334274380203310872944649121715, 231726644506236789334274380203310872944649121716⟩
def centerDExp : DyadicInterval precision := ⟨1064342052735172538949525898691347990568366073785, 1064342052735172538949525898691347992767389329338⟩
def centerDLog : DyadicInterval precision := ⟨799603206825097674192041553707670067993043651350, 799603206825097674192041553707670070192066906903⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1064342052735172538949525898691347991118121887673, scale precision, 1064342052735172538949525898691347992217633515450, scale precision,
    0, 128, 0, 128, ⟨-463453289012473578668548760406621746644196667401, -463453289012473578668548760406621746644194570248⟩, ⟨-463453289012473578668548760406621745134401916614, -463453289012473578668548760406621745134399819461⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨233681671635039144761899573780282067648184319234, 233681671635039144761899573780282067648184319235⟩
def centerCExp : DyadicInterval precision := ⟨1061498352066095884067179771616752342755095415174, 1061498352066095884067179771616752344954118670727⟩
def centerCLog : DyadicInterval precision := ⟨797956860102054195230619147335081589706255247658, 797956860102054195230619147335081591905278503211⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1061498352066095884067179771616752343304851229062, scale precision, 1061498352066095884067179771616752344404362856839, scale precision,
    0, 128, 0, 128, ⟨-467363343270078289523799147560564136053289394519, -467363343270078289523799147560564136053287297366⟩, ⟨-467363343270078289523799147560564134539449979571, -467363343270078289523799147560564134539447882418⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨479168318693266819909468923991435055930292470699, 479168318693266819909468923991435055930292470700⟩
def centerBExp : DyadicInterval precision := ⟨758618615769333099692909444315793069628551477508, 758618615769333099692909444315793071827574733061⟩
def centerBLog : DyadicInterval precision := ⟨611049357408705379871225940480394931196929469489, 611049357408705379871225940480394933395952725042⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨758618615769333099692909444315793070178307291396, scale precision, 758618615769333099692909444315793071277818919173, scale precision,
    0, 128, 0, 128, ⟨-958336637386533639818937847982870112919707141801, -958336637386533639818937847982870112919705044648⟩, ⟨-958336637386533639818937847982870110801464838149, -958336637386533639818937847982870110801462740996⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977217811276, 239878763828786629732963390089367294542248751091⟩
def wholeDExp : DyadicInterval precision := ⟨1052534436295863801714746685306812131164545959179, 1076258554488359441934578352032876250046492487573⟩
def wholeDLog : DyadicInterval precision := ⟨792755074273575496363197836249071886194744303106, 806482109433465224369192354012429701629745321451⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1052534436295863801714746685306812131714301773067, scale precision, 1076258554488359441934578352032876249496736673685, scale precision,
    0, 128, 0, 128, ⟨-479757527657573259465926780178734589847864569410, -479757527657573259465926780178734589847862472257⟩, ⟨-447181064593585716546276700234245027207897636639, -447181064593585716546276700234245027207895539486⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨224891258230253913064710509213309086355856044062, 242490916659753179449762138168969105284430212068⟩
def wholeCExp : DyadicInterval precision := ⟨1048778747491402917119097353667193949975927596083, 1074344533730943943617918492684994412399216515300⟩
def wholeCLog : DyadicInterval precision := ⟨790570121791082467784100830538504733032281088239, 805379404807415472260164889560497954347127117880⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1048778747491402917119097353667193950525683409971, scale precision, 1074344533730943943617918492684994411849460701412, scale precision,
    0, 128, 0, 128, ⟨-484981833319506358899524276337938211334961113893, -484981833319506358899524276337938211334959016740⟩, ⟨-449782516460507826129421018426618171963844090131, -449782516460507826129421018426618171963841992978⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨460795368920412028518162504643854518865778764227, 497687795998397117649244397984432485175960451124⟩
def wholeBExp : DyadicInterval precision := ⟨739634457227329619408055627098249370796716063738, 777934035523977631609093955857762635239218912162⟩
def wholeBLog : DyadicInterval precision := ⟨598498377720168544671336610201384664703675100463, 623709673634481061734914998481739644928680995264⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨739634457227329619408055627098249371346471877626, scale precision, 777934035523977631609093955857762634689463098274, scale precision,
    0, 128, 0, 128, ⟨-995375591996794235298488795968864971438227509304, -995375591996794235298488795968864971438225412151⟩, ⟨-921590737840824057036325009287709036698734474422, -921590737840824057036325009287709036698732377269⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0066StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0067StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0067StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨215469853832861228733019240262249168447508352861, 215469853832861228733019240262249168447508352862⟩
def centerDExp : DyadicInterval precision := ⟨1088285489568234168416510694967649720478852956927, 1088285489568234168416510694967649722677876212480⟩
def centerDLog : DyadicInterval precision := ⟨813392086659747652895796213383370383407954793069, 813392086659747652895796213383370385606978048622⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1088285489568234168416510694967649721028608770815, scale precision, 1088285489568234168416510694967649722128120398592, scale precision,
    0, 128, 0, 128, ⟨-430939707665722457466038480524498337633306585522, -430939707665722457466038480524498337633304488369⟩, ⟨-430939707665722457466038480524498336156728923076, -430939707665722457466038480524498336156726825923⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨217417439704053488995770589174390533044902703769, 217417439704053488995770589174390533044902703770⟩
def centerCExp : DyadicInterval precision := ⟨1085388869505506174702796711066082459117268183193, 1085388869505506174702796711066082461316291438746⟩
def centerCLog : DyadicInterval precision := ⟨811730841541090239746954400894905887936212490830, 811730841541090239746954400894905890135235746383⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1085388869505506174702796711066082459667023997081, scale precision, 1085388869505506174702796711066082460766535624858, scale precision,
    0, 128, 0, 128, ⟨-434834879408106977991541178348781066830065587845, -434834879408106977991541178348781066830063490692⟩, ⟨-434834879408106977991541178348781065349547324383, -434834879408106977991541178348781065349545227230⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨443960763151251609132321977767296496917259278939, 443960763151251609132321977767296496917259278940⟩
def centerBExp : DyadicInterval precision := ⟨796063648222342499064779916955612176856292022801, 796063648222342499064779916955612179055315278354⟩
def centerBLog : DyadicInterval precision := ⟨635493794846582383137405903634672746777735791497, 635493794846582383137405903634672748976759047050⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨796063648222342499064779916955612177406047836689, scale precision, 796063648222342499064779916955612178505559464466, scale precision,
    0, 128, 0, 128, ⟨-887921526302503218264643955534592994843822096180, -887921526302503218264643955534592994843819999027⟩, ⟨-887921526302503218264643955534592992825217116731, -887921526302503218264643955534592992825215019578⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 223590532296792858273138350117122513977217811277⟩
def wholeDExp : DyadicInterval precision := ⟨1076258554488359441934578352032876247847469232020, 1100424441361699833197968540687666015087121635409⟩
def wholeDLog : DyadicInterval precision := ⟨806482109433465224369192354012429699430722065898, 820333450761233184846212780159319759056095221943⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1076258554488359441934578352032876248397225045908, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-447181064593585716546276700234245028700975705620, -447181064593585716546276700234245028700973608467⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨208659993168738163327113473155546913729082918462, 226192381607875787764973691711067383103547195307⟩
def wholeCExp : DyadicInterval precision := ⟨1072433333592369868803923397647789074482818890749, 1098474615239151709131967435382893981734053878460⟩
def wholeCLog : DyadicInterval precision := ⟨804277494414882387092884188447412246493984831763, 819220710211348203542880090538222365260338778264⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1072433333592369868803923397647789075032574704637, scale precision, 1098474615239151709131967435382893981184298064572, scale precision,
    0, 128, 0, 128, ⟨-452384763215751575529947383422134766956297274832, -452384763215751575529947383422134766956295177679⟩, ⟨-417319986337476326654226946311093826726726203137, -417319986337476326654226946311093826726724105984⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨425853338453922988105921025000462397676821471068, 462203602748688269141792523640124819118951699960⟩
def wholeBExp : DyadicInterval precision := ⟨776436318258027888796895818405699247830777530902, 816035899282844599192681770600671263164726158372⟩
def wholeBLog : DyadicInterval precision := ⟨622731905639341251634754391147859034047642699034, 648366564209713227240650953399208862570974839308⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨776436318258027888796895818405699248380533344790, scale precision, 816035899282844599192681770600671262614970344484, scale precision,
    0, 128, 0, 128, ⟨-924407205497376538283585047280249639272720831033, -924407205497376538283585047280249639272718733880⟩, ⟨-851706676907845976211842050000924794369043897953, -851706676907845976211842050000924794369041800800⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0067StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0068StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0068StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨199272515379397466243712200840066988851184259851, 199272515379397466243712200840066988851184259852⟩
def centerDExp : DyadicInterval precision := ⟨1112677029363765823963422130229284076021359517329, 1112677029363765823963422130229284078220382772882⟩
def centerDLog : DyadicInterval precision := ⟨827306521710622256038181567611853437995191413469, 827306521710622256038181567611853440194214669022⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1112677029363765823963422130229284076571115331217, scale precision, 1112677029363765823963422130229284077670626958994, scale precision,
    0, 128, 0, 128, ⟨-398545030758794932487424401680133978424474007328, -398545030758794932487424401680133978424471910175⟩, ⟨-398545030758794932487424401680133976980265129232, -398545030758794932487424401680133976980263032079⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨201213207599686218730380712951692289967866670111, 201213207599686218730380712951692289967866670112⟩
def centerCExp : DyadicInterval precision := ⟨1109725956617690410777644231088260961951285083174, 1109725956617690410777644231088260964150308338727⟩
def centerCLog : DyadicInterval precision := ⟨825630075612994710682550141220154714959533469555, 825630075612994710682550141220154717158556725108⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1109725956617690410777644231088260962501040897062, scale precision, 1109725956617690410777644231088260963600552524839, scale precision,
    0, 128, 0, 128, ⟨-402426415199372437460761425903384580659759106199, -402426415199372437460761425903384580659757009046⟩, ⟨-402426415199372437460761425903384579211709671401, -402426415199372437460761425903384579211707574248⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨409254037795233993269467823541571913821038544816, 409254037795233993269467823541571913821038544817⟩
def centerBExp : DyadicInterval precision := ⟨834784621304994955524714233082077747148070343691, 834784621304994955524714233082077749347093599244⟩
def centerBLog : DyadicInterval precision := ⟨660348416871823013646048448585952555973405713802, 660348416871823013646048448585952558172428969355⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨834784621304994955524714233082077747697826157579, scale precision, 834784621304994955524714233082077748797337785356, scale precision,
    0, 128, 0, 128, ⟨-818508075590467986538935647083143828604564750474, -818508075590467986538935647083143828604562653321⟩, ⟨-818508075590467986538935647083143826679591525946, -818508075590467986538935647083143826679589428793⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 207364037900146833805279022757379167895402526014⟩
def wholeDExp : DyadicInterval precision := ⟨1100424441361699833197968540687666012888098379856, 1125044909933745912773463128462173915391977363052⟩
def wholeDLog : DyadicInterval precision := ⟨820333450761233184846212780159319756857071966390, 834311627217828832252519695712052890740898632922⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1100424441361699833197968540687666013437854193744, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-414728075800293667610558045514758336520950753820, -414728075800293667610558045514758336520948656667⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨192486267482474676822962020884762084766255799607, 209956316671997090000842133265351880706535748529⟩
def wholeCExp : DyadicInterval precision := ⟨1096527691430814070408977739606207487193086405799, 1123058232017299231234434758861740124267546850256⟩
def wholeCLog : DyadicInterval precision := ⟨818108780016791024693045805775745553862022319202, 833188643880544430188545489483369909169399985973⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1096527691430814070408977739606207487742842219687, scale precision, 1123058232017299231234434758861740123717791036368, scale precision,
    0, 128, 0, 128, ⟨-419912633343994180001684266530703762145811926872, -419912633343994180001684266530703762145809829719⟩, ⟨-384972534964949353645924041769524168817083118651, -384972534964949353645924041769524168817081021498⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨391390994830230264090034133324584929749196342428, 427241540043944272767980241125254450224304692814⟩
def wholeBExp : DyadicInterval precision := ⟨814487153830654407329274835310961497689453399530, 855442204069468392391412930235862396780536812154⟩
def wholeBLog : DyadicInterval precision := ⟨647372392247794569856006880382232489040091914188, 673437420530613622463329923875635179170588346809⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨814487153830654407329274835310961498239209213418, scale precision, 855442204069468392391412930235862396230780998266, scale precision,
    0, 128, 0, 128, ⟨-854483080087888545535960482250508901435082741779, -854483080087888545535960482250508901435080644626⟩, ⟨-782781989660460528180068266649169858559149657903, -782781989660460528180068266649169858559147560750⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0068StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0069StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0069StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨183130084206664803338173257357542686520853245489, 183130084206664803338173257357542686520853245490⟩
def centerDExp : DyadicInterval precision := ⟨1137529777074302590783266488860820386533899110215, 1137529777074302590783266488860820388732922365768⟩
def centerDLog : DyadicInterval precision := ⟨841349102754395012997791326891731422922496904416, 841349102754395012997791326891731425121520159969⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1137529777074302590783266488860820387083654924103, scale precision, 1137529777074302590783266488860820388183166551880, scale precision,
    0, 128, 0, 128, ⟨-366260168413329606676346514715085373748035442635, -366260168413329606676346514715085373748033345482⟩, ⟨-366260168413329606676346514715085372335379636478, -366260168413329606676346514715085372335377539325⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨187644691682397333940043399819643548548804667376, 187644691682397333940043399819643548548804667377⟩
def centerCExp : DyadicInterval precision := ⟨1130523737175883657858269274576851861196910964489, 1130523737175883657858269274576851863395934220042⟩
def centerCLog : DyadicInterval precision := ⟨837404108347216864497003198437610963611949278355, 837404108347216864497003198437610965810972533908⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1130523737175883657858269274576851861746666778377, scale precision, 1130523737175883657858269274576851862846178406154, scale precision,
    0, 128, 0, 128, ⟨-375289383364794667880086799639287097808315515570, -375289383364794667880086799639287097808313418417⟩, ⟨-375289383364794667880086799639287096386905251090, -375289383364794667880086799639287096386903153937⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨377731346157135098373979726371647444980012146880, 377731346157135098373979726371647444980012146881⟩
def centerBExp : DyadicInterval precision := ⟨871583049021038093838557160181216574930137994775, 871583049021038093838557160181216577129161250328⟩
def centerBLog : DyadicInterval precision := ⟨683583580248640024900874896368972878024355224590, 683583580248640024900874896368972880223378480143⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨871583049021038093838557160181216575479893808663, scale precision, 871583049021038093838557160181216576579405436440, scale precision,
    0, 128, 0, 128, ⟨-755462692314270196747959452743294890881875558486, -755462692314270196747959452743294890881873461333⟩, ⟨-755462692314270196747959452743294889038175126191, -755462692314270196747959452743294889038173029038⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨175078047236001450214222015517899197240067851934, 191194719185872429583518944051791718612165764689⟩
def wholeDExp : DyadicInterval precision := ⟨1125044909933745912773463128462173913192954107499, 1150133363234016597447468800724884781224161812840⟩
def wholeDLog : DyadicInterval precision := ⟨834311627217828832252519695712052888541875377369, 848419291580521843596292009329506550515087162287⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1125044909933745912773463128462173913742709921387, scale precision, 1150133363234016597447468800724884780674405998952, scale precision,
    0, 128, 0, 128, ⟨-382389438371744859167037888103583437938498754820, -382389438371744859167037888103583437938496657667⟩, ⟨-350156094472002900428444031035798393781549051388, -350156094472002900428444031035798393781546954235⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨178941488288963307887393676781801825848635031175, 196362957030864100704840821354813837189552226138⟩
def wholeCExp : DyadicInterval precision := ⟨1117116097011558262308417944608218308768982331719, 1144068714643020262775623526541037564997604254333⟩
def wholeCLog : DyadicInterval precision := ⟨829824651958942518772624474895005256789833599495, 845021496309331141540576730411200641999362073450⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1117116097011558262308417944608218309318738145607, scale precision, 1144068714643020262775623526541037564447848440445, scale precision,
    0, 128, 0, 128, ⟨-392725914061728201409681642709627675098340524212, -392725914061728201409681642709627675098338427059⟩, ⟨-357882976577926615774787353563603650994980232899, -357882976577926615774787353563603650994978135746⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨360074740751160892894090487962528567327495184603, 395502484258857815319500638290738212734295774002⟩
def wholeBExp : DyadicInterval precision := ⟨850642666916892482973072885744241869265832757134, 892898965645121959397532364804649249910439614843⟩
def wholeBLog : DyadicInterval precision := ⟨670406787412489536570811442140947324780582840560, 696875765659682097297052894707441002618043576303⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨850642666916892482973072885744241869815588571022, scale precision, 892898965645121959397532364804649249360683800955, scale precision,
    0, 128, 0, 128, ⟨-791004968517715630639001276581476426413136120409, -791004968517715630639001276581476426413134023256⟩, ⟨-720149481502321785788180975925057133755148263021, -720149481502321785788180975925057133755146165868⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0069StableWitnesses

end


