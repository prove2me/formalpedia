-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0186StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0186StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:48:56.327536+00:00
-- url     : https://prove2.me/theorems/a812220f-fe90-4ac0-95ce-7a600189f8ec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0186StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0187StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0186StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0187StableWitnesses, GeneralCK.Certificates.E8TAxisProd0188StableWitnesses, GeneralCK.Certificates.E8TAxisProd0189StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0186StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0187StableWitnesses, GeneralCK.Certificates.E8TAxisProd0188StableWitnesses, GeneralCK.Certificates.E8TAxisProd0189StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0186StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0187StableWitnesses, GeneralCK.Certificates.E8TAxisProd0188StableWitnesses, GeneralCK.Certificates.E8TAxisProd0189StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0186StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0187StableWitnesses, GeneralCK/Certificates/E8TAxisProd0188StableWitnesses, GeneralCK/Certificates/E8TAxisProd0189StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0186StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0186StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨381480886315733598228818968652248949197699359262, 381480886315733598228818968652248949197699359263⟩
def centerDExp : DyadicInterval precision := ⟨867122341474961541277039570779760212192757729340, 867122341474961541277039570779760214391780984893⟩
def centerDLog : DyadicInterval precision := ⟨680786608648623470121619561851525432077092876199, 680786608648623470121619561851525434276116131752⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨867122341474961541277039570779760212742513543228, scale precision, 867122341474961541277039570779760213842025171005, scale precision,
    0, 128, 0, 128, ⟨-762961772631467196457637937304497899321992225512, -762961772631467196457637937304497899321990128359⟩, ⟨-762961772631467196457637937304497897468807308690, -762961772631467196457637937304497897468805211537⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨383186931229429350970594589437212346504581219418, 383186931229429350970594589437212346504581219419⟩
def centerCExp : DyadicInterval precision := ⟨865100278568898040150507290712469778086832513290, 865100278568898040150507290712469780285855768843⟩
def centerCLog : DyadicInterval precision := ⟨679516960944860452105654850502294429049648184040, 679516960944860452105654850502294431248671439593⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨865100278568898040150507290712469778636588327178, scale precision, 865100278568898040150507290712469779736099954955, scale precision,
    0, 128, 0, 128, ⟨-766373862458858701941189178874424693937921738953, -766373862458858701941189178874424693937919641800⟩, ⟨-766373862458858701941189178874424692080405235873, -766373862458858701941189178874424692080403138720⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨825009676590796687890767097831475058742658335573, 825009676590796687890767097831475058742658335574⟩
def centerBExp : DyadicInterval precision := ⟨472591155174916574354047263539681250923570960962, 472591155174916574354047263539681253122594216515⟩
def centerBLog : DyadicInterval precision := ⟨409474686051675823736055072480328432343043409331, 409474686051675823736055072480328434542066664884⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨472591155174916574354047263539681251473326774850, scale precision, 472591155174916574354047263539681252572838402627, scale precision,
    1, 128, 1, 128, ⟨-1650019353181593375781534195662950119185453266763, -1650019353181593375781534195662950119185451169610⟩, ⟨-1650019353181593375781534195662950115785182172681, -1650019353181593375781534195662950115785180075528⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨372966609392870424646531471060848444542040850580, 390021907983024779256146395473341757167804190698⟩
def wholeDExp : DyadicInterval precision := ⟨857046406820575460675375243512252169980002923132, 877284626339432933560204346302551152435952374342⟩
def wholeDLog : DyadicInterval precision := ⟨674448983099953378325059509857368474307670227252, 687150831490084437187371430673459277974101520863⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨857046406820575460675375243512252170529758737020, scale precision, 877284626339432933560204346302551151886196560454, scale precision,
    0, 128, 0, 128, ⟨-780043815966049558512292790946683515273095446757, -780043815966049558512292790946683515273093349604⟩, ⟨-745933218785740849293062942121696888168223747987, -745933218785740849293062942121696888168221650834⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨374327121979865748895978949729971482563056499217, 392075801761638546678368963705776883596264828183⟩
def wholeCExp : DyadicInterval precision := ⟨854640920881250307716842165284237162820873370618, 875652816490321812361935498064993328036994911336⟩
def wholeCLog : DyadicInterval precision := ⟨672931892853288014779347199596696746706034181215, 686130761729925310680128142047483590544711468949⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨854640920881250307716842165284237163370629184506, scale precision, 875652816490321812361935498064993327487239097448, scale precision,
    0, 128, 0, 128, ⟨-784151603523277093356737927411553768132655384792, -784151603523277093356737927411553768132653287639⟩, ⟨-748654243959731497791957899459942964208548309771, -748654243959731497791957899459942964208546212618⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨803696310944812440969022459738225718904065351189, 846558906105246096241254902365722108228378969844⟩
def wholeBExp : DyadicInterval precision := ⟨458858317987499830828034589092883410180984914561, 486577914747696709790903248729443374910932363346⟩
def wholeBLog : DyadicInterval precision := ⟨399060419605594343747619764800622438619791789508, 420005779804942359384841535882528922602205548967⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨458858317987499830828034589092883410730740728449, scale precision, 486577914747696709790903248729443374361176549458, scale precision,
    1, 128, 1, 128, ⟨-1693117812210492192482509804731444218207776656754, -1693117812210492192482509804731444218207774559601⟩, ⟨-1607392621889624881938044919476451436156866870702, -1607392621889624881938044919476451436156864773549⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0186StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0187StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0187StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183100243, 364478458648618710654128585069611790600183100244⟩
def centerDExp : DyadicInterval precision := ⟨887534276475298848733503786031227102092850438854, 887534276475298848733503786031227104291873694407⟩
def centerDLog : DyadicInterval precision := ⟨693541818075819702070900853962455106453799173953, 693541818075819702070900853962455108652822429506⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨887534276475298848733503786031227102642606252742, scale precision, 887534276475298848733503786031227103742117880519, scale precision,
    0, 128, 0, 128, ⟨-728956917297237421308257170139223582105649493848, -728956917297237421308257170139223582105647396695⟩, ⟨-728956917297237421308257170139223580295085004280, -728956917297237421308257170139223580295082907127⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨366174028306096560398681968153894179008284153539, 366174028306096560398681968153894179008284153540⟩
def centerCExp : DyadicInterval precision := ⟨885477307657165677240025503609686238258137023395, 885477307657165677240025503609686240457160278948⟩
def centerCLog : DyadicInterval precision := ⟨692261471408144108574783502099291508955008619629, 692261471408144108574783502099291511154031875182⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨885477307657165677240025503609686238807892837283, scale precision, 885477307657165677240025503609686239907404465060, scale precision,
    0, 128, 0, 128, ⟨-732348056612193120797363936307788358923954576240, -732348056612193120797363936307788358923952479087⟩, ⟨-732348056612193120797363936307788357109184135073, -732348056612193120797363936307788357109182037920⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨783436518311852382580504242932969794815838678478, 783436518311852382580504242932969794815838678479⟩
def centerBExp : DyadicInterval precision := ⟨500256850610349565959720550440298744403591267944, 500256850610349565959720550440298746602614523497⟩
def centerBLog : DyadicInterval precision := ⟨430232223214483815940735502149705528524637775383, 430232223214483815940735502149705530723661030936⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨500256850610349565959720550440298744953347081832, scale precision, 500256850610349565959720550440298746052858709609, scale precision,
    1, 128, 1, 128, ⟨-1566873036623704765161008485865939591237791387595, -1566873036623704765161008485865939591237789290442⟩, ⟨-1566873036623704765161008485865939588025565423473, -1566873036623704765161008485865939588025563326320⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 372966609392870424646531471060848444542040850581⟩
def wholeDExp : DyadicInterval precision := ⟨877284626339432933560204346302551150236929118789, 897872332234039104779267097055247456527332583462⟩
def wholeDLog : DyadicInterval precision := ⟨687150831490084437187371430673459275775078265310, 699959742628865241142888209739517591976703657011⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨877284626339432933560204346302551150786684932677, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-745933218785740849293062942121696889999941751488, -745933218785740849293062942121696889999939654335⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨357368151647964377800168166755575814690708449890, 375007629872915579465429227647113556197499662128⟩
def wholeCExp : DyadicInterval precision := ⟨874837748939270527343756194198458032057629107576, 896212258825935063445621868699349683882669134745⟩
def wholeCLog : DyadicInterval precision := ⟨685620983558290487877774249648825815788860131768, 698931057061302088777017185007738619376053928466⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨874837748939270527343756194198458032607384921464, scale precision, 896212258825935063445621868699349683332913320857, scale precision,
    0, 128, 0, 128, ⟨-750015259745831158930858455294227113313420986373, -750015259745831158930858455294227113313418889220⟩, ⟨-714736303295928755600336333511151628484901510184, -714736303295928755600336333511151628484899413031⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨762571690262930842886348358041154597278412403555, 804527743768603565702130195390504626303088734563⟩
def wholeBExp : DyadicInterval precision := ⟨486024611517000907519255281789072218239958938267, 514746351050268520081006394940304791616391861303⟩
def wholeBLog : DyadicInterval precision := ⟨419590617889510464714352889163563095725923343314, 440987169559643747514126109985235682964278182179⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨486024611517000907519255281789072218789714752155, scale precision, 514746351050268520081006394940304791066636047415, scale precision,
    1, 128, 1, 128, ⟨-1609055487537207131404260390781009254259323241429, -1609055487537207131404260390781009254259321144276⟩, ⟨-1525143380525861685772696716082309192995923052801, -1525143380525861685772696716082309192995920955648⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0187StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0188StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0188StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705871997, 347578074592523924908318039364714024927705871998⟩
def centerDExp : DyadicInterval precision := ⟨908299859688922494739995341064431377288246704711, 908299859688922494739995341064431379487269960264⟩
def centerDLog : DyadicInterval precision := ⟨706404787120776184926021840452869055161422984619, 706404787120776184926021840452869057360446240172⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨908299859688922494739995341064431377838002518599, scale precision, 908299859688922494739995341064431378937514146376, scale precision,
    0, 128, 0, 128, ⟨-695156149185047849816636078729428050739998442960, -695156149185047849816636078729428050739996345807⟩, ⟨-695156149185047849816636078729428048970827142184, -695156149185047849816636078729428048970825045031⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨349938168514914026242709152922855428856828490758, 349938168514914026242709152922855428856828490759⟩
def centerCExp : DyadicInterval precision := ⟨905371070620342372930139639392735693954670173068, 905371070620342372930139639392735696153693428621⟩
def centerCLog : DyadicInterval precision := ⟨704597430152827970242813628007460562648337242909, 704597430152827970242813628007460564847360498462⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨905371070620342372930139639392735694504425986956, scale precision, 905371070620342372930139639392735695603937614733, scale precision,
    0, 128, 0, 128, ⟨-699876337029828052485418305845710858601105230698, -699876337029828052485418305845710858601103133545⟩, ⟨-699876337029828052485418305845710856826210829490, -699876337029828052485418305845710856826208732337⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨743539431694910481410123662499246691291479354845, 743539431694910481410123662499246691291479354846⟩
def centerBExp : DyadicInterval precision := ⟨528328926510004935372836995406258094326770101191, 528328926510004935372836995406258096525793356744⟩
def centerBLog : DyadicInterval precision := ⟨450997578390382866895352708329386191617149114719, 450997578390382866895352708329386193816172370272⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨528328926510004935372836995406258094876525915079, scale precision, 528328926510004935372836995406258095976037542856, scale precision,
    1, 128, 1, 128, ⟨-1487078863389820962820247324998493384103733999113, -1487078863389820962820247324998493384103731901960⟩, ⟨-1487078863389820962820247324998493381062185517421, -1487078863389820962820247324998493381062183420268⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773909588, 356015818146773315735630103594046256346147492781⟩
def wholeDExp : DyadicInterval precision := ⟨897872332234039104779267097055247454328309327909, 918817951079152880960489128094785338008821185250⟩
def wholeDLog : DyadicInterval precision := ⟨699959742628865241142888209739517589777680401458, 712877141250487397629906767735900639146197088161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨897872332234039104779267097055247454878065141797, scale precision, 918817951079152880960489128094785337459065371362, scale precision,
    0, 128, 0, 128, ⟨-712031636293546631471260207188092513587154905811, -712031636293546631471260207188092513587152808658⟩, ⟨-678329234677107700847743398667782514541089437367, -678329234677107700847743398667782514541087340214⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨341181664743207029901761625605753194818793566138, 358721125013013616465942719726870605036528329662⟩
def wholeCExp : DyadicInterval precision := ⟨894554471427663164708455914071574105789360909730, 916285290296825158783368498693788601140728251194⟩
def wholeCLog : DyadicInterval precision := ⟨697903064989442090312621735187922062299371825205, 711321275186003626837213087546784677284808715760⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨894554471427663164708455914071574106339116723618, scale precision, 916285290296825158783368498693788600590972437306, scale precision,
    0, 128, 0, 128, ⟨-717442250026027232931885439453741210971235569386, -717442250026027232931885439453741210971233472233⟩, ⟨-682363329486414059803523251211506388760711698564, -682363329486414059803523251211506388760709601411⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨723095381825490724288119292239514973318635896594, 764200081313133845645516728213200410612534991657⟩
def wholeBExp : DyadicInterval precision := ⟨513600577279727695561249074184567721601599743974, 543318568242366388450850122152057333799247976037⟩
def wholeBLog : DyadicInterval precision := ⟨440139585719911246472702045260891971537045039413, 461965990912139238006126035442713468878134312909⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨513600577279727695561249074184567722151355557862, scale precision, 543318568242366388450850122152057333249492162149, scale precision,
    1, 128, 1, 128, ⟨-1528400162626267691291033456426400822789455998873, -1528400162626267691291033456426400822789453901720⟩, ⟨-1446190763650981448576238584479029945158455313535, -1446190763650981448576238584479029945158453216382⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0188StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0189StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0189StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨330774838385704024446645164332729497941801346231, 330774838385704024446645164332729497941801346232⟩
def centerDExp : DyadicInterval precision := ⟨929427725267003858605636529731753968326593265085, 929427725267003858605636529731753970525616520638⟩
def centerDLog : DyadicInterval precision := ⟨719377002425149550154397054915826075326505911594, 719377002425149550154397054915826077525529167147⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨929427725267003858605636529731753968876349078973, scale precision, 929427725267003858605636529731753969975860706750, scale precision,
    0, 128, 0, 128, ⟨-661549676771408048893290328665458996748080881422, -661549676771408048893290328665458996748078784269⟩, ⟨-661549676771408048893290328665458995019126600658, -661549676771408048893290328665458995019124503505⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨333121624753268687411845674830606428712260579099, 333121624753268687411845674830606428712260579100⟩
def centerCExp : DyadicInterval precision := ⟨926447681147195357695674818277035204986085576952, 926447681147195357695674818277035207185108832505⟩
def centerCLog : DyadicInterval precision := ⟨717554256875150709024681962640204057704413369962, 717554256875150709024681962640204059903436625515⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨926447681147195357695674818277035205535841390840, scale precision, 926447681147195357695674818277035206635353018617, scale precision,
    0, 128, 0, 128, ⟨-666243249506537374823691349661212858291780054661, -666243249506537374823691349661212858291777957508⟩, ⟨-666243249506537374823691349661212856557264358890, -666243249506537374823691349661212856557262261737⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨703652196262695309670934442267165901299737319971, 703652196262695309670934442267165901299737319972⟩
def centerBExp : DyadicInterval precision := ⟨557968754104013092784479012742292650166610542371, 557968754104013092784479012742292652365633797924⟩
def centerBLog : DyadicInterval precision := ⟨472607054073476861308116084028600319883888378647, 472607054073476861308116084028600322082911634200⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨557968754104013092784479012742292650716366356259, scale precision, 557968754104013092784479012742292651815877984036, scale precision,
    1, 128, 1, 128, ⟨-1407304392525390619341868884534331804039464964298, -1407304392525390619341868884534331804039462867145⟩, ⟨-1407304392525390619341868884534331801159486412738, -1407304392525390619341868884534331801159484315585⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 339164617338553850423871699333891257707773909589⟩
def wholeDExp : DyadicInterval precision := ⟨918817951079152880960489128094785335809797929697, 940130328208408204655831711119657711878645153902⟩
def wholeDLog : DyadicInterval precision := ⟨712877141250487397629906767735900636947173832608, 725904575743015811666185701912516251881166002297⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨918817951079152880960489128094785336359553743585, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-678329234677107700847743398667782516290008298142, -678329234677107700847743398667782516290006200989⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨324414069859130179241454812482021708860680101599, 341854318407743454016368281757269571767095249300⟩
def wholeCExp : DyadicInterval precision := ⟨915442240848377048625704906156645268567554306540, 937553175193314205694480171750604712119961727935⟩
def wholeCLog : DyadicInterval precision := ⟨710803004767554370280158921986153509092924601342, 724335419542181150711051587565465268364327301126⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨915442240848377048625704906156645269117310120428, scale precision, 937553175193314205694480171750604711570205914047, scale precision,
    0, 128, 0, 128, ⟨-683708636815486908032736563514539144411875562921, -683708636815486908032736563514539144411873465768⟩, ⟨-648828139718260358482909624964043416864376236538, -648828139718260358482909624964043416864374139385⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨683617503977218638759679260554365617749392567493, 723893093223027775688689165539107035389142841533⟩
def wholeBExp : DyadicInterval precision := ⟨542725787603106952090962746584271116118482785655, 573477985762471067755756724795624694233558496163⟩
def wholeBLog : DyadicInterval precision := ⟨461533793562037058338836676920068877301805492424, 483788288489494779175312012082173590573761441245⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨542725787603106952090962746584271116668238599543, scale precision, 573477985762471067755756724795624693683802682275, scale precision,
    1, 128, 1, 128, ⟨-1447786186446055551377378331078214072258719466704, -1447786186446055551377378331078214072258717369551⟩, ⟨-1367235007954437277519358521108731234097740211307, -1367235007954437277519358521108731234097738114154⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0189StableWitnesses

end


