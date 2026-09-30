-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0011StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0011StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:20:09.121664+00:00
-- url     : https://prove2.me/theorems/19d08d13-118b-4970-bb84-c5336de83d07
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0011StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0012StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0011StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0012StableWitnesses, GeneralCK.Certificates.E8TAxisProd0013StableWitnesses, GeneralCK.Certificates.E8TAxisProd0014StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0011StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0012StableWitnesses, GeneralCK.Certificates.E8TAxisProd0013StableWitnesses, GeneralCK.Certificates.E8TAxisProd0014StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0011StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0012StableWitnesses, GeneralCK.Certificates.E8TAxisProd0013StableWitnesses, GeneralCK.Certificates.E8TAxisProd0014StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0011StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0012StableWitnesses, GeneralCK/Certificates/E8TAxisProd0013StableWitnesses, GeneralCK/Certificates/E8TAxisProd0014StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0011StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0011StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨60981562246941182391851692343549914653715634261, 60981562246941182391851692343549914653715634262⟩
def centerDExp : DyadicInterval precision := ⟨1344488804354560387653913977701155507615899604953, 1344488804354560387653913977701155509814922860506⟩
def centerDLog : DyadicInterval precision := ⟨953326044385255946846825783453523246727646501740, 953326044385255946846825783453523248926669757293⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1344488804354560387653913977701155508165655418841, scale precision, 1344488804354560387653913977701155509265167046618, scale precision,
    0, 128, 0, 128, ⟨-121963124493882364783703384687099829905034185949, -121963124493882364783703384687099829905032088796⟩, ⟨-121963124493882364783703384687099828709830448249, -121963124493882364783703384687099828709828351096⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨62884972741514630104325378199290343874001204815, 62884972741514630104325378199290343874001204816⟩
def centerCExp : DyadicInterval precision := ⟨1340991327481915638344123570530076470368162498843, 1340991327481915638344123570530076472567185754396⟩
def centerCLog : DyadicInterval precision := ⟨951503245433020359706488020348701563408683478368, 951503245433020359706488020348701565607706733921⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1340991327481915638344123570530076470917918312731, scale precision, 1340991327481915638344123570530076472017429940508, scale precision,
    0, 128, 0, 128, ⟨-125769945483029260208650756398580688347163949155, -125769945483029260208650756398580688347161852002⟩, ⟨-125769945483029260208650756398580687148842967260, -125769945483029260208650756398580687148840870107⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨124125482432655107267784619184625826590664438274, 124125482432655107267784619184625826590664438275⟩
def centerBExp : DyadicInterval precision := ⟨1233189894958627491970848091783125044561964271681, 1233189894958627491970848091783125046760987527234⟩
def centerBLog : DyadicInterval precision := ⟨894174927219586722108278281493878705517900685513, 894174927219586722108278281493878707716923941066⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1233189894958627491970848091783125045111720085569, scale precision, 1233189894958627491970848091783125046211231713346, scale precision,
    0, 128, 0, 128, ⟨-248250964865310214535569238369251653832867069092, -248250964865310214535569238369251653832864971939⟩, ⟨-248250964865310214535569238369251652529792781158, -248250964865310214535569238369251652529790684005⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 63360863746962342702697993485127651995684952634⟩
def wholeDExp : DyadicInterval precision := ⟨1340118310385255731396483422015350658626993302998, 1348872859460053731599279250908956040444361819487⟩
def wholeDLog : DyadicInterval precision := ⟨951047895604627342379828868169897140353010055619, 955607699899585814401544643147774225289199821907⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1340118310385255731396483422015350659176749116886, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-126721727493924685405395986970255304590921766561, -126721727493924685405395986970255304590919669408⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨59871350779906312655059654590921689440155693627, 65899215223265784759171254738762616571610796757⟩
def wholeCExp : DyadicInterval precision := ⟨1335471322730389028688153556972687527360759500040, 1346533005072431926854353225933980981500476150832⟩
def wholeCLog : DyadicInterval precision := ⟨948621721121932708792572285570935423759085624709, 954390379789352380913007499717796931002181128545⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1335471322730389028688153556972687527910515313928, scale precision, 1346533005072431926854353225933980980950720336944, scale precision,
    0, 128, 0, 128, ⟨-131798430446531569518342509477525233744859688468, -131798430446531569518342509477525233744857591315⟩, ⟨-119742701559812625310119309181843378283617799232, -119742701559812625310119309181843378283615702079⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨118700586572171500710721487428242681162025303743, 129554310903328861618553401759095070205044128552⟩
def wholeBExp : DyadicInterval precision := ⟨1224062337940262835884041942228948967468729640351, 1242378828106247998826148587803258950415954659395⟩
def wholeBLog : DyadicInterval precision := ⟨889216072642414855396552704879363494821126166276, 899150188757459813599771432452226605253656503759⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1224062337940262835884041942228948968018485454239, scale precision, 1242378828106247998826148587803258949866198845507, scale precision,
    0, 128, 0, 128, ⟨-259108621806657723237106803518190141066484815308, -259108621806657723237106803518190141066482718155⟩, ⟨-237401173144343001421442974856485361677333437793, -237401173144343001421442974856485361677331340640⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0011StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0012StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0012StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨56224069662401947129176131245290424868351320698, 56224069662401947129176131245290424868351320699⟩
def centerDExp : DyadicInterval precision := ⟨1353270542552318619031293173544076935377002222510, 1353270542552318619031293173544076937576025478063⟩
def centerDLog : DyadicInterval precision := ⟨957892874924759606731049484620710570189124178339, 957892874924759606731049484620710572388147433892⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1353270542552318619031293173544076935926758036398, scale precision, 1353270542552318619031293173544076937026269664175, scale precision,
    0, 128, 0, 128, ⟨-112448139324803894258352262490580850330427558828, -112448139324803894258352262490580850330425461675⟩, ⟨-112448139324803894258352262490580849142979821120, -112448139324803894258352262490580849142977723967⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨58126894187953343854819435514497108971398845100, 58126894187953343854819435514497108971398845101⟩
def centerCExp : DyadicInterval precision := ⟨1349751303692396389863417078706891290236382775426, 1349751303692396389863417078706891292435406030979⟩
def centerCLog : DyadicInterval precision := ⟨956064452933657876698540702963988539410987956707, 956064452933657876698540702963988541610011212260⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1349751303692396389863417078706891290786138589314, scale precision, 1349751303692396389863417078706891291885650217091, scale precision,
    0, 128, 0, 128, ⟨-116253788375906687709638871028994218538070638077, -116253788375906687709638871028994218538068540924⟩, ⟨-116253788375906687709638871028994217347526839479, -116253788375906687709638871028994217347524742326⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨114554682698653038499274232750549628108153969377, 114554682698653038499274232750549628108153969378⟩
def centerBExp : DyadicInterval precision := ⟨1249447478844033303923112619890185153278704387121, 1249447478844033303923112619890185155477727642674⟩
def centerBLog : DyadicInterval precision := ⟨902965950764249051155878321702144237504938468857, 902965950764249051155878321702144239703961724410⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1249447478844033303923112619890185153828460201009, scale precision, 1249447478844033303923112619890185154927971828786, scale precision,
    0, 128, 0, 128, ⟨-229109365397306076998548465501099256859368448200, -229109365397306076998548465501099256859366351047⟩, ⟨-229109365397306076998548465501099255573249526461, -229109365397306076998548465501099255573247429308⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 58602635770181898821662589353151101542136562993⟩
def wholeDExp : DyadicInterval precision := ⟨1348872859460053731599279250908956038245338563934, 1357681920934804568838490939788917163911062976792⟩
def wholeDLog : DyadicInterval precision := ⟨955607699899585814401544643147774223090176566354, 960181582307675404146178190201383839808765855727⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1348872859460053731599279250908956038795094377822, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-117205271540363797643325178706302203679933740618, -117205271540363797643325178706302203679931643465⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨55114191349500929383767732776807590001211495094, 61140170517420599824312204870708940218430869242⟩
def wholeCExp : DyadicInterval precision := ⟨1344197016924831398370770481048404981463711996272, 1355327477382912160807407512816259140896722585358⟩
def wholeCLog : DyadicInterval precision := ⟨953174058842438098605194693086279844816489615228, 958960498003603095356594726853619711080259091341⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1344197016924831398370770481048404982013467810160, scale precision, 1355327477382912160807407512816259140346966771470, scale precision,
    0, 128, 0, 128, ⟨-122280341034841199648624409741417881034594378495, -122280341034841199648624409741417881034592281342⟩, ⟨-110228382699001858767535465553615179409601244616, -110228382699001858767535465553615179409599147463⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨109136304863157575849981745590334233255913005861, 119976688018282527118403186318767332493118324028⟩
def wholeBExp : DyadicInterval precision := ⟨1240211169993063747833404125148284448985501473396, 1258746325388888982740306017261621820374659083311⟩
def wholeBLog : DyadicInterval precision := ⟨897978056156449534723239001596928880675494551536, 907970480164479711642721375997620061459539838950⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1240211169993063747833404125148284449535257287284, scale precision, 1258746325388888982740306017261621819824903269423, scale precision,
    0, 128, 0, 128, ⟨-239953376036565054236806372637534665634086257884, -239953376036565054236806372637534665634084160731⟩, ⟨-218272609726315151699963491180668465873518128688, -218272609726315151699963491180668465873516031535⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0012StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0013StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0013StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨53370245394433761539404939910283149997486243189, 53370245394433761539404939910283149997486243190⟩
def centerCExp : DyadicInterval precision := ⟨1358565846000905640574303170236611544459701108189, 1358565846000905640574303170236611546658724363742⟩
def centerCLog : DyadicInterval precision := ⟨960639748802635514472889052596215460521550014530, 960639748802635514472889052596215462720573270083⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1358565846000905640574303170236611545009456922077, scale precision, 1358565846000905640574303170236611546108968549854, scale precision,
    0, 128, 0, 128, ⟨-106740490788867523078809879820566300586383236954, -106740490788867523078809879820566300586381139801⟩, ⟨-106740490788867523078809879820566299403563832955, -106740490788867523078809879820566299403561735802⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨104995179769752213846513530911000044935304653781, 104995179769752213846513530911000044935304653782⟩
def centerBExp : DyadicInterval precision := ⟨1265899822359557709964801712149891931701978890345, 1265899822359557709964801712149891933901002145898⟩
def centerBLog : DyadicInterval precision := ⟨911808779120153267380676626687654617126771188086, 911808779120153267380676626687654619325794443639⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1265899822359557709964801712149891932251734704233, scale precision, 1265899822359557709964801712149891933351246332010, scale precision,
    0, 128, 0, 128, ⟨-209990359539504427693027061822000090505312255878, -209990359539504427693027061822000090505310158725⟩, ⟨-209990359539504427693027061822000089235908456401, -209990359539504427693027061822000089235906359248⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨50358387464788094565508226754163990527967612749, 56382629818508109569023805582825185317660096338⟩
def wholeCExp : DyadicInterval precision := ⟨1352976938350729088534078276200742856013974924063, 1364176857568604256874790178069699268726462720844⟩
def wholeCLog : DyadicInterval precision := ⟨957740420169989537447061925271607357119743920373, 963544769795384609901545553993877877871085712583⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1352976938350729088534078276200742856563730737951, scale precision, 1364176857568604256874790178069699268176706906956, scale precision,
    0, 128, 0, 128, ⟨-112765259637016219138047611165650371229173951785, -112765259637016219138047611165650371229171854632⟩, ⟨-100716774929576189131016453508327980466959106142, -100716774929576189131016453508327980466957008989⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨99582782619590846946456695311079788932288258447, 110410900082256569655872652612393379359363185642⟩
def wholeBExp : DyadicInterval precision := ⟨1256552699861900996669668890440374793567001288839, 1275310675710689402948086131683640041435686387951⟩
def wholeBLog : DyadicInterval precision := ⟨906791440347840233037779814200164605550295306012, 916842985962171777418736964129359079544302680148⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1256552699861900996669668890440374794116757102727, scale precision, 1275310675710689402948086131683640040885930574063, scale precision,
    0, 128, 0, 128, ⟨-220821800164513139311745305224786759358150678605, -220821800164513139311745305224786759358148581452⟩, ⟨-199165565239181693892913390622159577234559298212, -199165565239181693892913390622159577234557201059⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0013StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0014StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0014StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨48614909194624410160526379893730315390508931552, 48614909194624410160526379893730315390508931553⟩
def centerCExp : DyadicInterval precision := ⟨1367435495396362364102802013078620489926923523747, 1367435495396362364102802013078620492125946779300⟩
def centerCLog : DyadicInterval precision := ⟨965229236207097753989940631774174609012967958441, 965229236207097753989940631774174611211991213994⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1367435495396362364102802013078620490476679337635, scale precision, 1367435495396362364102802013078620491576190965412, scale precision,
    0, 128, 0, 128, ⟨-97229818389248820321052759787460631368592530206, -97229818389248820321052759787460631368590433053⟩, ⟨-97229818389248820321052759787460630193445293155, -97229818389248820321052759787460630193443196002⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨95446025919810144175011252655302405033343458652, 95446025919810144175011252655302405033343458653⟩
def centerBExp : DyadicInterval precision := ⟨1282550641382087255154689277512609644435074403335, 1282550641382087255154689277512609646634097658888⟩
def centerBLog : DyadicInterval precision := ⟨920704138763992455185319194312256812213493667115, 920704138763992455185319194312256814412516922668⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1282550641382087255154689277512609644984830217223, scale precision, 1282550641382087255154689277512609646084341845000, scale precision,
    0, 128, 0, 128, ⟨-190892051839620288350022505310604810693149796087, -190892051839620288350022505310604810693147698934⟩, ⟨-190892051839620288350022505310604809440226135678, -190892051839620288350022505310604809440224038525⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨45603822007427965209743755626378939214500302403, 51626475909575562598122397028042009565357232055⟩
def wholeCExp : DyadicInterval precision := ⟨1361811623389207099593779473574397852241884622991, 1373081691268201893610801308403049807825049856546⟩
def wholeCLog : DyadicInterval precision := ⟨962320907563890103076833485319333024780955938033, 968143299041892371692199594756639108558795210406⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1361811623389207099593779473574397852791640436879, scale precision, 1373081691268201893610801308403049807275294042658, scale precision,
    0, 128, 0, 128, ⟨-103252951819151125196244794056084019720715633356, -103252951819151125196244794056084019720713536203⟩, ⟨-91207644014855930419487511252757877843844173505, -91207644014855930419487511252757877843842076352⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨90039073446665143782344453410578939042533249234, 100855997974081054332202374750186544677787710249⟩
def wholeBExp : DyadicInterval precision := ⟨1273090587334595101171992503582187423926243214911, 1292075651917351569123771717317878749012907852774⟩
def wholeBLog : DyadicInterval precision := ⟨915656942067084075958202759333488409631267436180, 925768442296972979924489385850065359417595805318⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1273090587334595101171992503582187424475999028799, scale precision, 1292075651917351569123771717317878748463152038886, scale precision,
    0, 128, 0, 128, ⟨-201711995948162108664404749500373089986693398320, -201711995948162108664404749500373089986691301167⟩, ⟨-180078146893330287564688906821157877463223910461, -180078146893330287564688906821157877463221813308⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0014StableWitnesses

end


