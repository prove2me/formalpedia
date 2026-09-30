-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0055StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:29:36.974834+00:00
-- url     : https://prove2.me/theorems/1b004843-3529-4e27-98e0-670f6a51914d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0055StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0056StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0055StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0056StableWitnesses, GeneralCK.Certificates.E8TAxisProd0057StableWitnesses, GeneralCK.Certificates.E8TAxisProd0058StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0055StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0056StableWitnesses, GeneralCK.Certificates.E8TAxisProd0057StableWitnesses, GeneralCK.Certificates.E8TAxisProd0058StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0055StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0056StableWitnesses, GeneralCK.Certificates.E8TAxisProd0057StableWitnesses, GeneralCK.Certificates.E8TAxisProd0058StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0055StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0056StableWitnesses, GeneralCK/Certificates/E8TAxisProd0057StableWitnesses, GeneralCK/Certificates/E8TAxisProd0058StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0055StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0055StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨75263509879409481448600087548378166009129228127, 75263509879409481448600087548378166009129228128⟩
def centerDExp : DyadicInterval precision := ⟨1318466949108280820343673762456176585110097807004, 1318466949108280820343673762456176587309121062557⟩
def centerDLog : DyadicInterval precision := ⟨939709310368699983502098003954865527411730866232, 939709310368699983502098003954865529610754121785⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1318466949108280820343673762456176585659853620892, scale precision, 1318466949108280820343673762456176586759365248669, scale precision,
    0, 128, 0, 128, ⟨-150527019758818962897200175096756332627655912283, -150527019758818962897200175096756332627653815130⟩, ⟨-150527019758818962897200175096756331408863097380, -150527019758818962897200175096756331408861000227⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨77168959881869121339873083546476896294782046276, 77168959881869121339873083546476896294782046277⟩
def centerCExp : DyadicInterval precision := ⟨1315033493781227373745599839784663483317453607384, 1315033493781227373745599839784663485516476862937⟩
def centerCLog : DyadicInterval precision := ⟨937903138187081559899352940644049434159156404362, 937903138187081559899352940644049436358179659915⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1315033493781227373745599839784663483867209421272, scale precision, 1315033493781227373745599839784663484966721049049, scale precision,
    0, 128, 0, 128, ⟨-154337919763738242679746167092953793200552637593, -154337919763738242679746167092953793200550540440⟩, ⟨-154337919763738242679746167092953791978577644667, -154337919763738242679746167092953791978575547514⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨152915178463027122650990311385075366485501069608, 152915178463027122650990311385075366485501069609⟩
def centerBExp : DyadicInterval precision := ⟨1185550002510866574450539697030115399810086601719, 1185550002510866574450539697030115402009109857272⟩
def centerBLog : DyadicInterval precision := ⟨868105674307971667134088694511406443302996060876, 868105674307971667134088694511406445502019316429⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1185550002510866574450539697030115400359842415607, scale precision, 1185550002510866574450539697030115401459354043384, scale precision,
    0, 128, 0, 128, ⟨-305830356926054245301980622770150733648721563594, -305830356926054245301980622770150733648719466441⟩, ⟨-305830356926054245301980622770150732293284811996, -305830356926054245301980622770150732293282714843⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159908214514, 79233540548598202161862116954926444096871869276⟩
def wholeDExp : DyadicInterval precision := ⟨1311323390486212533981803318339124542185441636828, 1325647089475606555897615027767584925570467038145⟩
def wholeDLog : DyadicInterval precision := ⟨935948922676490622602857379124864309894134156234, 943479230106772831249544853595316780957610367733⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1311323390486212533981803318339124542735197450716, scale precision, 1325647089475606555897615027767584925020711224257, scale precision,
    0, 128, 0, 128, ⟨-158467081097196404323724233909852888806460939344, -158467081097196404323724233909852888806458842191⟩, ⟨-142589531024244066774107942510231079713721761400, -142589531024244066774107942510231079713719664247⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨72564627903854707163651962613527732691556708915, 81775066651422335775660018154838453034717622375⟩
def wholeCExp : DyadicInterval precision := ⟨1306770574892044410141964846722889501420659583114, 1323345446381383724377914098789029240465426820278⟩
def wholeCLog : DyadicInterval precision := ⟨933547250713536054780546866575375685442815155182, 942271815221164981759971436449019773495390052472⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1306770574892044410141964846722889501970415397002, scale precision, 1323345446381383724377914098789029239915671006390, scale precision,
    0, 128, 0, 128, ⟨-163550133302844671551320036309676906684287161234, -163550133302844671551320036309676906684285064081⟩, ⟨-145129255807709414327303925227055464775964591575, -145129255807709414327303925227055464775962494422⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨144265163383122164482546534975845208150899296286, 161577436401748847597890018140472027124415234622⟩
def wholeBExp : DyadicInterval precision := ⟨1171579559607242623643396951962840838141676836280, 1199666936116860123325924274283438623773957684532⟩
def wholeBLog : DyadicInterval precision := ⟨860371826143762983574909401721668985274065389503, 875879266733045019226793172335071309313097160060⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1171579559607242623643396951962840838691432650168, scale precision, 1199666936116860123325924274283438623224201870644, scale precision,
    0, 128, 0, 128, ⟨-323154872803497695195780036280944054934631313097, -323154872803497695195780036280944054934629215944⟩, ⟨-288530326766244328965093069951690415632056233257, -288530326766244328965093069951690415632054136104⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0055StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0056StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0056StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨67327239450709848584332901078869677125813867607, 67327239450709848584332901078869677125813867608⟩
def centerDExp : DyadicInterval precision := ⟨1332864109481912054585740658098352653964589647865, 1332864109481912054585740658098352656163612903418⟩
def centerDLog : DyadicInterval precision := ⟨947258739228882635667763210876156281479935267063, 947258739228882635667763210876156283678958522616⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1332864109481912054585740658098352654514345461753, scale precision, 1332864109481912054585740658098352655613857089530, scale precision,
    0, 128, 0, 128, ⟨-134654478901419697168665802157739354854442691388, -134654478901419697168665802157739354854440594235⟩, ⟨-134654478901419697168665802157739353648814876197, -134654478901419697168665802157739353648812779044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨69231504213203685635274745952757999619736937921, 69231504213203685635274745952757999619736937922⟩
def centerCExp : DyadicInterval precision := ⟨1329395318329971307223055964361939907019217037786, 1329395318329971307223055964361939909218240293339⟩
def centerCLog : DyadicInterval precision := ⟨945443374448389283883529012974166167552957337971, 945443374448389283883529012974166169751980593524⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1329395318329971307223055964361939907568972851674, scale precision, 1329395318329971307223055964361939908668484479451, scale precision,
    0, 128, 0, 128, ⟨-138463008426407371270549491905515999843861754321, -138463008426407371270549491905515999843859657168⟩, ⟨-138463008426407371270549491905515998635088094520, -138463008426407371270549491905515998635085997367⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨136905764311649914033194382418989884301169624464, 136905764311649914033194382418989884301169624465⟩
def centerBExp : DyadicInterval precision := ⟨1211809837277935567452580249344919281141666770478, 1211809837277935567452580249344919283340690026031⟩
def centerBLog : DyadicInterval precision := ⟨882532923854732389511070129155831046717867377455, 882532923854732389511070129155831048916890633008⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1211809837277935567452580249344919281691422584366, scale precision, 1211809837277935567452580249344919282790934212143, scale precision,
    0, 128, 0, 128, ⟨-273811528623299828066388764837979769265372563305, -273811528623299828066388764837979769265370466152⟩, ⟨-273811528623299828066388764837979767939308031704, -273811528623299828066388764837979767939305934551⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨63360863746962342702697993485127651995684952633, 71294765512122033387053971255115540159908214515⟩
def wholeDExp : DyadicInterval precision := ⟨1325647089475606555897615027767584923371443782592, 1340118310385255731396483422015350660826016558551⟩
def wholeDLog : DyadicInterval precision := ⟨943479230106772831249544853595316778758587112180, 951047895604627342379828868169897142552033311172⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1325647089475606555897615027767584923921199596480, scale precision, 1340118310385255731396483422015350660276260744663, scale precision,
    0, 128, 0, 128, ⟨-142589531024244066774107942510231080925913193810, -142589531024244066774107942510231080925911096657⟩, ⟨-126721727493924685405395986970255303391820141124, -126721727493924685405395986970255303391818043971⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨64629982951322598580719314150188454126481843138, 73834617277284679112775982643791805006453058900⟩
def wholeCExp : DyadicInterval precision := ⟨1321047569937851251477172603640981663771516652326, 1337792902321001359725941128831362489547180966641⟩
def wholeCLog : DyadicInterval precision := ⟨941065380399649366716716759699609515283451231391, 949834312395558470178147735810135995335009627374⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1321047569937851251477172603640981664321272466214, scale precision, 1337792902321001359725941128831362488997425152753, scale precision,
    0, 128, 0, 128, ⟨-147669234554569358225551965287583610621113138979, -147669234554569358225551965287583610621111041826⟩, ⟨-129259965902645197161438628300376907652371757618, -129259965902645197161438628300376907652369660465⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨128276576533857721025787388172632631798945739446, 145545901828368143194963992409340935150072244214⟩
def wholeBExp : DyadicInterval precision := ⟨1197566200971201614847448590493226404854019178586, 1226204510955732588180712779922086014561330502580⟩
def wholeBLog : DyadicInterval precision := ⟨874725096964288106315511122625193815440630015638, 890381392629473614381711917360076509590264386473⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1197566200971201614847448590493226405403774992474, scale precision, 1226204510955732588180712779922086014011574688692, scale precision,
    0, 128, 0, 128, ⟨-291091803656736286389927984818681870971063788938, -291091803656736286389927984818681870971061691785⟩, ⟨-256553153067715442051574776345265262942643737442, -256553153067715442051574776345265262942641640289⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0056StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0057StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0057StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨248047465841179905852080519169529384371630755610, 248047465841179905852080519169529384371630755611⟩
def centerDExp : DyadicInterval precision := ⟨1040834191819245838922303450900148559184359318387, 1040834191819245838922303450900148561383382573940⟩
def centerDLog : DyadicInterval precision := ⟨785937414897454142996966385139071281278247176763, 785937414897454142996966385139071283477270432316⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1040834191819245838922303450900148559734115132275, scale precision, 1040834191819245838922303450900148560833626760052, scale precision,
    0, 128, 0, 128, ⟨-496094931682359811704161038339058769515209742591, -496094931682359811704161038339058769515207645438⟩, ⟨-496094931682359811704161038339058767971315377004, -496094931682359811704161038339058767971313279851⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨252629397574248137835203746750995613110135119104, 252629397574248137835203746750995613110135119105⟩
def centerCExp : DyadicInterval precision := ⟨1034328402193971172474688220210670670183156827944, 1034328402193971172474688220210670672382180083497⟩
def centerCLog : DyadicInterval precision := ⟨782132728214745566577792381463024518020002349200, 782132728214745566577792381463024520219025604753⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1034328402193971172474688220210670670732912641832, scale precision, 1034328402193971172474688220210670671832424269609, scale precision,
    0, 128, 0, 128, ⟨-505258795148496275670407493501991226997073915839, -505258795148496275670407493501991226997071818686⟩, ⟨-505258795148496275670407493501991225443468657730, -505258795148496275670407493501991225443466560577⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨517802407414192458596602619857206278120042976220, 517802407414192458596602619857206278120042976221⟩
def centerBExp : DyadicInterval precision := ⟨719552964234240380085322697203156706210064698294, 719552964234240380085322697203156708409087953847⟩
def centerBLog : DyadicInterval precision := ⟨585103551996455244053877469859303467230213698372, 585103551996455244053877469859303469429236953925⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨719552964234240380085322697203156706759820512182, scale precision, 719552964234240380085322697203156707859332139959, scale precision,
    1, 128, 1, 128, ⟨-1035604814828384917193205239714412557356709490352, -1035604814828384917193205239714412557356707393199⟩, ⟨-1035604814828384917193205239714412555123464511686, -1035604814828384917193205239714412555123462414533⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542248751090, 256233328382592948799518632260864583083635375284⟩
def wholeDExp : DyadicInterval precision := ⟨1029239839924196772159254586274144058200357824470, 1052534436295863801714746685306812133363569214732⟩
def wholeDLog : DyadicInterval precision := ⟨779149939480909138582665574125961103221748177421, 792755074273575496363197836249071888393767558659⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1029239839924196772159254586274144058750113638358, scale precision, 1052534436295863801714746685306812132813813400844, scale precision,
    0, 128, 0, 128, ⟨-512466656765185897599037264521729166947914940776, -512466656765185897599037264521729166947912843623⟩, ⟨-479757527657573259465926780178734588321132532104, -479757527657573259465926780178734588321130434951⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨243797635752172854441566085746482099908275673539, 261481554085338207199210368615594053303071317312⟩
def wholeCExp : DyadicInterval precision := ⟨1021874357938466258669045575256879970086457865486, 1046905010795551553201549808992034661246932013298⟩
def wholeCLog : DyadicInterval precision := ⟨774821665406531776561079319035724441259170101514, 789478812706385577759978772296657462163373647542⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1021874357938466258669045575256879970636213679374, scale precision, 1046905010795551553201549808992034660697176199410, scale precision,
    0, 128, 0, 128, ⟨-522963108170676414398420737231188107392413556682, -522963108170676414398420737231188107392411459529⟩, ⟨-487595271504345708883132171492964199049081599505, -487595271504345708883132171492964199049079502352⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨499118607398289371570928132321858375692748600603, 536644883613847459699420042076475693246390244490⟩
def wholeBExp : DyadicInterval precision := ⟨701236387855383963878193299001347845372983630384, 738187668517019050850553078864002936812619200002⟩
def wholeBLog : DyadicInterval precision := ⟨572777979699668047747697419547858731524408609304, 597537428828638861458087364241545119280449804656⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨701236387855383963878193299001347845922739444272, scale precision, 738187668517019050850553078864002936262863386114, scale precision,
    1, 128, 0, 128, ⟨-1073289767227694919398840084152951387638570655242, -1073289767227694919398840084152951387638568558089⟩, ⟨-998237214796578743141856264643716750297063619408, -998237214796578743141856264643716750297061522255⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0057StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0058StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0058StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨236289822428373432150654949298107898906188217602, 236289822428373432150654949298107898906188217603⟩
def centerCExp : DyadicInterval precision := ⟨1057716470600957690177348546850699430402172016992, 1057716470600957690177348546850699432601195272545⟩
def centerCLog : DyadicInterval precision := ⟨795764480921592490878998218352018258725978223569, 795764480921592490878998218352018260925001479122⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1057716470600957690177348546850699430951927830880, scale precision, 1057716470600957690177348546850699432051439458657, scale precision,
    0, 128, 0, 128, ⟨-472579644856746864301309898596215798572003569281, -472579644856746864301309898596215798572001472128⟩, ⟨-472579644856746864301309898596215797052751398283, -472579644856746864301309898596215797052749301130⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨482007786130042976079423016479978656483757791435, 482007786130042976079423016479978656483757791436⟩
def centerBExp : DyadicInterval precision := ⟨755676582462510672810870636297793314548679988836, 755676582462510672810870636297793316747703244389⟩
def centerBLog : DyadicInterval precision := ⟨609111337168988866760315408143063289000326179929, 609111337168988866760315408143063291199349435482⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨755676582462510672810870636297793315098435802724, scale precision, 755676582462510672810870636297793316197947430501, scale precision,
    0, 128, 0, 128, ⟨-964015572260085952158846032959957314030761200324, -964015572260085952158846032959957314030759103171⟩, ⟨-964015572260085952158846032959957311904272062571, -964015572260085952158846032959957311904269965418⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨227493904775828364443481753968725214648101220906, 245104786449875745977549104126014224823483124985⟩
def wholeCExp : DyadicInterval precision := ⟨1045034004465915750166869454598200825920388086610, 1070524947694947175059872365104781310019638952323⟩
def wholeCLog : DyadicInterval precision := ⟨788388280140701814001405921433914844571445968825, 803176377000203245651677875656754748282636989136⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1045034004465915750166869454598200826470143900498, scale precision, 1070524947694947175059872365104781309469883138435, scale precision,
    0, 128, 0, 128, ⟨-490209572899751491955098208252028450415812157849, -490209572899751491955098208252028450415810060696⟩, ⟨-454987809551656728886963507937450428545666079879, -454987809551656728886963507937450428545663982726⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨463612671914032783328998846535993879410036316002, 500550322985418952666290655314410717262742449184⟩
def wholeBExp : DyadicInterval precision := ⟨736742798248134475464905005390791339684068173481, 774940598619922204718906818259703492641109940504⟩
def wholeBLog : DyadicInterval precision := ⟨596577123165191194143973799773058819722819201776, 621754788502250965904765341100031123597831526513⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨736742798248134475464905005390791340233823987369, scale precision, 774940598619922204718906818259703492091354126616, scale precision,
    0, 128, 0, 128, ⟨-1001100645970837905332581310628821435616055171427, -1001100645970837905332581310628821435616053074274⟩, ⟨-927225343828065566657997693071987757783259989880, -927225343828065566657997693071987757783257892727⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0058StableWitnesses

end


