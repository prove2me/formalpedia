-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0422StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0422StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:21:38.909996+00:00
-- url     : https://prove2.me/theorems/c393d1bf-efc7-450a-967a-97ab5f61c0e1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0422StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0423StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0422StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0423StableWitnesses, GeneralCK.Certificates.E8TAxisProd0424StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0422StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0423StableWitnesses, GeneralCK.Certificates.E8TAxisProd0424StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0422StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0423StableWitnesses, GeneralCK.Certificates.E8TAxisProd0424StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0422StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0423StableWitnesses, GeneralCK/Certificates/E8TAxisProd0424StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0422StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0422StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385356161447, 721949241039261777105100229686264310385356161448⟩
def centerDExp : DyadicInterval precision := ⟨544171400918647169539408046331758482200227109223, 544171400918647169539408046331758484399250364776⟩
def centerDLog : DyadicInterval precision := ⟨462587568506596564045749998967475930132416323351, 462587568506596564045749998967475932331439578904⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758482749982923111, scale precision, 544171400918647169539408046331758483849494550888, scale precision,
    1, 128, 1, 128, ⟨-1443898482078523554210200459372528622247213277149, -1443898482078523554210200459372528622247211179996⟩, ⟨-1443898482078523554210200459372528619294213465789, -1443898482078523554210200459372528619294211368636⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨723743497563456579521756696765127262242199523030, 723743497563456579521756696765127262242199523031⟩
def centerCExp : DyadicInterval precision := ⟨542836903090086197898851395627212015184988369845, 542836903090086197898851395627212017384011625398⟩
def centerCLog : DyadicInterval precision := ⟨461614817782468067237557080735017255197870240335, 461614817782468067237557080735017257396893495888⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨542836903090086197898851395627212015734744183733, scale precision, 542836903090086197898851395627212016834255811510, scale precision,
    1, 128, 1, 128, ⟨-1447486995126913159043513393530254525964529793920, -1447486995126913159043513393530254525964527696767⟩, ⟨-1447486995126913159043513393530254523004270395354, -1447486995126913159043513393530254523004268298201⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1775487235868340233267332077170645784283607734532, 1775487235868340233267332077170645784283607734533⟩
def centerBExp : DyadicInterval precision := ⟨128707755838042626460076204751382885930997306723, 128707755838042626460076204751382888130020562276⟩
def centerBLog : DyadicInterval precision := ⟨123352602337763299968429960277568077282834146647, 123352602337763299968429960277568079481857402200⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨128707755838042626460076204751382886480753120611, scale precision, 128707755838042626460076204751382887580264748388, scale precision,
    3, 128, 3, 128, ⟨-3550974471736680466534664154341291574809800866176, -3550974471736680466534664154341291574809798769023⟩, ⟨-3550974471736680466534664154341291562324632169096, -3550974471736680466534664154341291562324630071943⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨716228578308099727358082939138935890959899212494, 727686670816724440524685346233204921246428500689⟩
def wholeDExp : DyadicInterval precision := ⟨539915612896337333160506278237532711076442060493, 548448150163327086956497611001597703886791384129⟩
def wholeDLog : DyadicInterval precision := ⟨459483149562382791203438629890379326034218128951, 465700648921796470149242465934935277251827483709⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨539915612896337333160506278237532711626197874381, scale precision, 548448150163327086956497611001597703337035570241, scale precision,
    1, 128, 1, 128, ⟨-1455373341633448881049370692466409843980996201432, -1455373341633448881049370692466409843980994104279⟩, ⟨-1432457156616199454716165878277871780454813181077, -1432457156616199454716165878277871780454811083924⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨717818738077276547266346525406500350592538334508, 729686250624038563936294882104931553976999782419⟩
def wholeCExp : DyadicInterval precision := ⟨538440241817928742225196763144133750817710699232, 547255990051665333475350274198462654007712862759⟩
def wholeCLog : DyadicInterval precision := ⟨458405387094799785143435470394481758629293462306, 464833532296279191069246239180209532529374414734⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨538440241817928742225196763144133751367466513120, scale precision, 547255990051665333475350274198462653457957048871, scale precision,
    1, 128, 1, 128, ⟨-1459372501248077127872589764209863109446216387288, -1459372501248077127872589764209863109446214290135⟩, ⟨-1435637476154553094532693050813000699716900051682, -1435637476154553094532693050813000699716897954529⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1758061084566505952455073141097382445118862838328, 1792971558778424535670036312396712867821559662760⟩
def wholeBExp : DyadicInterval precision := ⟨125664776469018869182627064158740332526510389574, 131813927617791960898726783414672095840788329878⟩
def wholeBLog : DyadicInterval precision := ⟨120553235212148088963329164475777220480828271405, 126204583485856205146568788615736156424223930790⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨125664776469018869182627064158740333076266203462, scale precision, 131813927617791960898726783414672095291032515990, scale precision,
    3, 128, 3, 128, ⟨-3585943117556849071340072624793425742036869240777, -3585943117556849071340072624793425742036867143624⟩, ⟨-3516122169133011904910146282194764884142247767504, -3516122169133011904910146282194764884142245670351⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0422StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0423StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0423StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823374015368, 710524563403850356500890582610538039823374015369⟩
def centerDExp : DyadicInterval precision := ⟨552745918518612785766768712299414359359889019406, 552745918518612785766768712299414361558912274959⟩
def centerDLog : DyadicInterval precision := ⟨468822363559667384554973018042110607773397723001, 468822363559667384554973018042110609972420978554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414359909644833294, scale precision, 552745918518612785766768712299414361009156461071, scale precision,
    1, 128, 1, 128, ⟨-1421049126807700713001781165221076081100344655889, -1421049126807700713001781165221076081100342558736⟩, ⟨-1421049126807700713001781165221076078193153502733, -1421049126807700713001781165221076078193151405580⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨712308385264467401372526157240222256166331415044, 712308385264467401372526157240222256166331415045⟩
def centerCExp : DyadicInterval precision := ⟨551398266551455001157658293084601539886487295551, 551398266551455001157658293084601542085510551104⟩
def centerCLog : DyadicInterval precision := ⟨467844204378872811806531983585227469733839770665, 467844204378872811806531983585227471932863026218⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨551398266551455001157658293084601540436243109439, scale precision, 551398266551455001157658293084601541535754737216, scale precision,
    1, 128, 1, 128, ⟨-1424616770528934802745052314480444513789812134055, -1424616770528934802745052314480444513789810036902⟩, ⟨-1424616770528934802745052314480444510875515623276, -1424616770528934802745052314480444510875513526123⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1741287164195526465436345526495502340289362854113, 1741287164195526465436345526495502340289362854114⟩
def centerBExp : DyadicInterval precision := ⟨134874626314568948780401481837134012967634654793, 134874626314568948780401481837134015166657910346⟩
def centerBLog : DyadicInterval precision := ⟨129009379541404474231670392736823511392944334489, 129009379541404474231670392736823513591967590042⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨134874626314568948780401481837134013517390468681, scale precision, 134874626314568948780401481837134014616902096458, scale precision,
    3, 128, 3, 128, ⟨-3482574328391052930872691052991004686535881516631, -3482574328391052930872691052991004686535879419478⟩, ⟨-3482574328391052930872691052991004674621571996970, -3482574328391052930872691052991004674621569899817⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    1, 128, 1, 128, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨706418028852297341274228471548718019078995975325, 718216479732007712890007372867500866930406184082⟩
def wholeCExp : DyadicInterval precision := ⟨546958204170090529048032573089878591478482858823, 555860879201464316956316918067312306504175607791⟩
def wholeCLog : DyadicInterval precision := ⟨464616857666307662905908345572522789475759380749, 471080776929200598171218428820192923799788118033⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨546958204170090529048032573089878592028238672711, scale precision, 555860879201464316956316918067312305954419793903, scale precision,
    1, 128, 1, 128, ⟨-1436432959464015425780014745735001735329790417184, -1436432959464015425780014745735001735329788320031⟩, ⟨-1412836057704594682548456943097436036712543153423, -1412836057704594682548456943097436036712541056270⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1723979223046414486173486635543667283668119371302, 1758655875698752868671039875538295491606201352997⟩
def wholeBExp : DyadicInterval precision := ⟨131706681954098771814973935346452997094854625403, 138107283635667777991122279470824755421777461895⟩
def wholeBLog : DyadicInterval precision := ⟨126106206873072014785992997170596336092339320769, 131965923646588169906884994468492927701100996025⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨131706681954098771814973935346452997644610439291, scale precision, 138107283635667777991122279470824754872021648007, scale precision,
    3, 128, 3, 128, ⟨-3517311751397505737342079751076590989312846117930, -3517311751397505737342079751076590989312844020777⟩, ⟨-3447958446092828972346973271087334561518523295866, -3447958446092828972346973271087334561518521198713⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0423StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0424StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0424StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611295173, 1108008086961741616166050582946352244611295174⟩
def centerAExp : DyadicInterval precision := ⟨1459287300336296999564987921182920319954750140059, 1459287300336296999564987921182920322153773395612⟩
def centerALog : DyadicInterval precision := ⟨1011928151219685967171369581941982746115885093399, 1011928151219685967171369581941982748314908348952⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459287300336296999564987921182920320504505953947, scale precision, 1459287300336296999564987921182920321604017581724, scale precision,
    0, 128, 0, 128, ⟨-2216016173923483232332101165892705039813657726, -2216016173923483232332101165892705039811560573⟩, ⟨-2216016173923483232332101165892703938633620121, -2216016173923483232332101165892703938631522968⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨791938512842554261609794269869582385953292906566, 791938512842554261609794269869582385953292906567⟩
def centerDExp : DyadicInterval precision := ⟨494470288976765335249663465240012275930998297549, 494470288976765335249663465240012278130021553102⟩
def centerDLog : DyadicInterval precision := ⟨425914889167615021373493039688154777291425506011, 425914889167615021373493039688154779490448761564⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨494470288976765335249663465240012276480754111437, scale precision, 494470288976765335249663465240012277580265739214, scale precision,
    1, 128, 1, 128, ⟨-1583877025685108523219588539739164773531495455899, -1583877025685108523219588539739164773531493358746⟩, ⟨-1583877025685108523219588539739164770281678267518, -1583877025685108523219588539739164770281676170365⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨793384974085761175881500914681664233967262216207, 793384974085761175881500914681664233967262216208⟩
def centerCExp : DyadicInterval precision := ⟨493492493692952655385907664486070548661072480248, 493492493692952655385907664486070550860095735801⟩
def centerCLog : DyadicInterval precision := ⟨425184098147139198503376659387307221802102861911, 425184098147139198503376659387307224001126117464⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨493492493692952655385907664486070549210828294136, scale precision, 493492493692952655385907664486070550310339921913, scale precision,
    1, 128, 1, 128, ⟨-1586769948171522351763001829363328469562653633696, -1586769948171522351763001829363328469562651536543⟩, ⟨-1586769948171522351763001829363328466306397328285, -1586769948171522351763001829363328466306395231132⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1984440098651787350683725656115206912272629582974, 1984440098651787350683725656115206912272629582975⟩
def centerBExp : DyadicInterval precision := ⟨96698865941554518641502323451355790382277478966, 96698865941554518641502323451355792581300734519⟩
def centerBLog : DyadicInterval precision := ⟨93634326498519700914848884426970766772809435350, 93634326498519700914848884426970768971832690903⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96698865941554518641502323451355790932033292854, scale precision, 96698865941554518641502323451355792031544920631, scale precision,
    3, 128, 3, 128, ⟨-3968880197303574701367451312230413832854241031493, -3968880197303574701367451312230413832854238934340⟩, ⟨-3968880197303574701367451312230413816236279397572, -3968880197303574701367451312230413816236277300419⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1459603428780171974367103696970164796353834591973⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012086326714990166522051059359330290859456642138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172029077196, 797886217135535601213561462349015058648188303748⟩
def wholeDExp : DyadicInterval precision := ⟨490462045819898463991457369988920386537963137363, 498498909896069833132911032342083545771079714894⟩
def wholeDLog : DyadicInterval precision := ⟨422916858198723400101802834922666846616439225893, 428921977795889549222947679819138374779521683823⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨490462045819898463991457369988920387087718951251, scale precision, 498498909896069833132911032342083545221323901006, scale precision,
    1, 128, 1, 128, ⟨-1595772434271071202427122924698030118934565623881, -1595772434271071202427122924698030118934563526728⟩, ⟨-1572017909849098277777678789423155846732282314032, -1572017909849098277777678789423155846732280216879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨787244934960362713248492454397955357972175880983, 799544472586682598084691358314518380474598781129⟩
def wholeCExp : DyadicInterval precision := ⟨489350327249073955708409513632780752418688141402, 497656469602704994474302344624992115104224121487⟩
def wholeCLog : DyadicInterval precision := ⟨422084239544854572878050279672743776679176030937, 428293665448410436788381560004412427320682957444⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨489350327249073955708409513632780752968443955290, scale precision, 497656469602704994474302344624992114554468307599, scale precision,
    1, 128, 1, 128, ⟨-1599088945173365196169382716629036762591108255908, -1599088945173365196169382716629036762591106158755⟩, ⟨-1574489869920725426496984908795910714329847481655, -1574489869920725426496984908795910714329845384502⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1966413164801763508313912999584903235670242461288, 2002509882964941298458757480146617772422553731731⟩
def wholeBExp : DyadicInterval precision := ⟨94337047264748479797762350201218585415428587331, 99114002907865010828061597352454785680972991332⟩
def wholeBLog : DyadicInterval precision := ⟨91417397091501345397551978576271787258330432160, 95897831093703115009974444514581912736616229912⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨94337047264748479797762350201218585965184401219, scale precision, 99114002907865010828061597352454785131217177444, scale precision,
    3, 128, 3, 128, ⟨-4005019765929882596917514960293235553362112652254, -4005019765929882596917514960293235553362110555101⟩, ⟨-3932826329603527016627825999169806463233972274224, -3932826329603527016627825999169806463233970177071⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0424StableWitnesses

end


