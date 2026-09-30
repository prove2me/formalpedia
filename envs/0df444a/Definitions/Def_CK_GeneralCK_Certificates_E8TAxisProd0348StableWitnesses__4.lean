-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0348StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0348StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:14:16.853513+00:00
-- url     : https://prove2.me/theorems/016f912a-c94b-4e79-a451-87ce926d71c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0348StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0349StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0348StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0349StableWitnesses, GeneralCK.Certificates.E8TAxisProd0350StableWitnesses, GeneralCK.Certificates.E8TAxisProd0351StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0348StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0349StableWitnesses, GeneralCK.Certificates.E8TAxisProd0350StableWitnesses, GeneralCK.Certificates.E8TAxisProd0351StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0348StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0349StableWitnesses, GeneralCK.Certificates.E8TAxisProd0350StableWitnesses, GeneralCK.Certificates.E8TAxisProd0351StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0348StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0349StableWitnesses, GeneralCK/Certificates/E8TAxisProd0350StableWitnesses, GeneralCK/Certificates/E8TAxisProd0351StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0348StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0348StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029348165, 864539270161105163740168296694370154034029348166⟩
def centerDExp : DyadicInterval precision := ⟨447705727508954974656542730347776284626226541037, 447705727508954974656542730347776286825249796590⟩
def centerDLog : DyadicInterval precision := ⟨390547930354595539952804600044570644160315185441, 390547930354595539952804600044570646359338440994⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨447705727508954974656542730347776285175982354925, scale precision, 447705727508954974656542730347776286275493982702, scale precision,
    1, 128, 1, 128, ⟨-1729078540322210327480336593388740309862696205336, -1729078540322210327480336593388740309862694108183⟩, ⟨-1729078540322210327480336593388740306273423284479, -1729078540322210327480336593388740306273421187326⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨866899092778523922403211712430182959743263293973, 866899092778523922403211712430182959743263293974⟩
def centerCExp : DyadicInterval precision := ⟨446262277819258555846883293374914107482388882991, 446262277819258555846883293374914109681412138544⟩
def centerCLog : DyadicInterval precision := ⟨389442549134401372940690278214613788429907861970, 389442549134401372940690278214613790628931117523⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨446262277819258555846883293374914108032144696879, scale precision, 446262277819258555846883293374914109131656324656, scale precision,
    1, 128, 1, 128, ⟨-1733798185557047844806423424860365921286968906299, -1733798185557047844806423424860365921286966809146⟩, ⟨-1733798185557047844806423424860365917686086366746, -1733798185557047844806423424860365917686084269593⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2201236463931163914543836418758834429511489573563, 2201236463931163914543836418758834429511489573564⟩
def centerBExp : DyadicInterval precision := ⟨71874783684437529787138948385737410959674165701, 71874783684437529787138948385737413158697421254⟩
def centerBLog : DyadicInterval precision := ⟨70163316395477128660301020927536557129832390031, 70163316395477128660301020927536559328855645584⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71874783684437529787138948385737411509429979589, scale precision, 71874783684437529787138948385737412608941607366, scale precision,
    4, 128, 4, 128, ⟨-4402472927862327829087672837517668870201713277642, -4402472927862327829087672837517668870201711180489⟩, ⟨-4402472927862327829087672837517668847844247113770, -4402472927862327829087672837517668847844245016617⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 870712988176454679833831807012927217752922944019⟩
def wholeDExp : DyadicInterval precision := ⟨443939237141351316813290285207320724478560656031, 451492192509468156215846209344698069605083336703⟩
def wholeDLog : DyadicInterval precision := ⟨387661827478115861734404726101104695617766958964, 393443605556601543377574216062392477640846281111⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725028316469919, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1741425976352909359667663614025854437315709536964, -1741425976352909359667663614025854437315707439811⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨860523385637997187597699194182143622845389347403, 873295603373261018771555203622806852252707807171⟩
def wholeCExp : DyadicInterval precision := ⟨442373038984331337565501399025503959666705508188, 450172893944187176112303678503271104495455816372⟩
def wholeCLog : DyadicInterval precision := ⟨386460036096261595143723125341317717966069752885, 392435331422632358563970480015087042627313791708⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨442373038984331337565501399025503960216461322076, scale precision, 450172893944187176112303678503271103945700002484, scale precision,
    1, 128, 1, 128, ⟨-1746591206746522037543110407245613706321686985301, -1746591206746522037543110407245613706321684888148⟩, ⟨-1721046771275994375195398388364287243905978763719, -1721046771275994375195398388364287243905976666566⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2182777455391751358345891469798536797800420068856, 2219724758279219382234207696250944856682730950268⟩
def wholeBExp : DyadicInterval precision := ⟨70079133410597552889980881732338800003570102879, 73713490003967344269135003468799474825706293617⟩
def wholeBLog : DyadicInterval precision := ⟨68450831716991602558563110076712336989878161780, 71914786133848703389180051559349803431078861527⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨70079133410597552889980881732338800553325916767, scale precision, 73713490003967344269135003468799474275950479729, scale precision,
    4, 128, 4, 128, ⟨-4439449516558438764468415392501889724830630724844, -4439449516558438764468415392501889724830628627691⟩, ⟨-4365554910783502716691782939597073584700949971174, -4365554910783502716691782939597073584700947874021⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0348StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0349StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0349StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133789484, 852249911794452062012049136358764955095133789485⟩
def centerDExp : DyadicInterval precision := ⟨455298659801689467951201474539649436055069582612, 455298659801689467951201474539649438254092838165⟩
def centerDLog : DyadicInterval precision := ⟨396348806111750593903736846609666706637987139797, 396348806111750593903736846609666708837010395350⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649436604825396500, scale precision, 455298659801689467951201474539649437704337024277, scale precision,
    1, 128, 1, 128, ⟨-1704499823588904124024098272717529911954976264684, -1704499823588904124024098272717529911954974167531⟩, ⟨-1704499823588904124024098272717529908425560990410, -1704499823588904124024098272717529908425558893257⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨854594955749909921823516996891543855391572572933, 854594955749909921823516996891543855391572572934⟩
def centerCExp : DyadicInterval precision := ⟨453839908049977439405420110366070012428058722659, 453839908049977439405420110366070014627081978212⟩
def centerCLog : DyadicInterval precision := ⟨395236129042801160757822382900117372381628591609, 395236129042801160757822382900117374580651847162⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨453839908049977439405420110366070012977814536547, scale precision, 453839908049977439405420110366070014077326164324, scale precision,
    1, 128, 1, 128, ⟨-1709189911499819843647033993783087712553526030768, -1709189911499819843647033993783087712553523933615⟩, ⟨-1709189911499819843647033993783087709012766358123, -1709189911499819843647033993783087709012764260970⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2164978297926823868564731370961579631765668916307, 2164978297926823868564731370961579631765668916308⟩
def centerBExp : DyadicInterval precision := ⟨75531000704575343209415614080366213033516351720, 75531000704575343209415614080366215232539607273⟩
def centerBLog : DyadicInterval precision := ⟨73644005505169165114535736247400260506865952022, 73644005505169165114535736247400262705889207575⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75531000704575343209415614080366213583272165608, scale precision, 75531000704575343209415614080366214682783793385, scale precision,
    4, 128, 4, 128, ⟨-4329956595853647737129462741923159274168944826231, -4329956595853647737129462741923159274168942729078⟩, ⟨-4329956595853647737129462741923159252893732936140, -4329956595853647737129462741923159252893730838987⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771969770, 858384943750592238779991986336301839154815993317⟩
def wholeDExp : DyadicInterval precision := ⟨451492192509468156215846209344698067406060081150, 459125158042315647897421247370792079661750447941⟩
def wholeDLog : DyadicInterval precision := ⟨393443605556601543377574216062392475441823025558, 399263485746125009998379766489542017105011910291⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨451492192509468156215846209344698067955815895038, scale precision, 459125158042315647897421247370792079111994634053, scale precision,
    1, 128, 1, 128, ⟨-1716769887501184477559983972672603680089218674697, -1716769887501184477559983972672603680089216577544⟩, ⟨-1692268151626862819173455653290755287573544997795, -1692268151626862819173455653290755287573542900642⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨848259152079208575771423146945791430608399016703, 860951354494718761259480866113864817695925685821⟩
def wholeCExp : DyadicInterval precision := ⟨449909324518644720207484640644222061828918479068, 457791928359208882212008675321149406496252577594⟩
def wholeCLog : DyadicInterval precision := ⟨392233815056710800058435864486243578328229780719, 398248611863398573671141327189844445890484226065⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨449909324518644720207484640644222062378674292956, scale precision, 457791928359208882212008675321149405946496763706, scale precision,
    1, 128, 1, 128, ⟨-1721902708989437522518961732227729637177698986055, -1721902708989437522518961732227729637177696888902⟩, ⟨-1696518304158417151542846293891582859461702558089, -1696518304158417151542846293891582859461700460936⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2146579901747431857436991023294185168826235441510, 2183408037953517443303825322705842199936530386147⟩
def wholeBExp : DyadicInterval precision := ⟨73649908287009224811403069138762817173148058334, 77456815706180140722399949399194484426304623794⟩
def wholeBLog : DyadicInterval precision := ⟨71854256045198074259907423791595821390948113637, 75474038208423573864964984131385342988059529053⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73649908287009224811403069138762817722903872222, scale precision, 77456815706180140722399949399194483876548809906, scale precision,
    4, 128, 4, 128, ⟨-4366816075907034886607650645411684410782362875238, -4366816075907034886607650645411684410782360778085⟩, ⟨-4293159803494863714873982046588370327279349633649, -4293159803494863714873982046588370327279347536496⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0349StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0350StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0350StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029348165, 864539270161105163740168296694370154034029348166⟩
def centerDExp : DyadicInterval precision := ⟨447705727508954974656542730347776284626226541037, 447705727508954974656542730347776286825249796590⟩
def centerDLog : DyadicInterval precision := ⟨390547930354595539952804600044570644160315185441, 390547930354595539952804600044570646359338440994⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨447705727508954974656542730347776285175982354925, scale precision, 447705727508954974656542730347776286275493982702, scale precision,
    1, 128, 1, 128, ⟨-1729078540322210327480336593388740309862696205336, -1729078540322210327480336593388740309862694108183⟩, ⟨-1729078540322210327480336593388740306273423284479, -1729078540322210327480336593388740306273421187326⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨866469822731549546084651138112966665410371363747, 866469822731549546084651138112966665410371363748⟩
def centerCExp : DyadicInterval precision := ⟨446524505793370471590402477675594244674607718712, 446524505793370471590402477675594246873630974265⟩
def centerCLog : DyadicInterval precision := ⟨389643423191028670175649326245591335383255137181, 389643423191028670175649326245591337582278392734⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨446524505793370471590402477675594245224363532600, scale precision, 446524505793370471590402477675594246323875160377, scale precision,
    1, 128, 1, 128, ⟨-1732939645463099092169302276225933332620127710672, -1732939645463099092169302276225933332620125613519⟩, ⟨-1732939645463099092169302276225933329021359841470, -1732939645463099092169302276225933329021357744317⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2200604897378175500274030877968229063096880051218, 2200604897378175500274030877968229063096880051219⟩
def centerBExp : DyadicInterval precision := ⟨71936929808804842837202995779915448466665903064, 71936929808804842837202995779915450665689158617⟩
def centerBLog : DyadicInterval precision := ⟨70222548310594166793476569861478049828285656406, 70222548310594166793476569861478052027308911959⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71936929808804842837202995779915449016421716952, scale precision, 71936929808804842837202995779915450115933344729, scale precision,
    4, 128, 4, 128, ⟨-4401209794756351000548061755936458137362836954860, -4401209794756351000548061755936458137362834857707⟩, ⟨-4401209794756351000548061755936458115024685347175, -4401209794756351000548061755936458115024683250022⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 870712988176454679833831807012927217752922944019⟩
def wholeDExp : DyadicInterval precision := ⟨443939237141351316813290285207320724478560656031, 451492192509468156215846209344698069605083336703⟩
def wholeDLog : DyadicInterval precision := ⟨387661827478115861734404726101104695617766958964, 393443605556601543377574216062392477640846281111⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725028316469919, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1741425976352909359667663614025854437315709536964, -1741425976352909359667663614025854437315707439811⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨860095510318109513278476642346114951551390422737, 872864931448654105458585332578425361540623574322⟩
def wholeCExp : DyadicInterval precision := ⟨442633830755694006340905910612713211959639611441, 450436560119714483532603399343668928801342230957⟩
def wholeCLog : DyadicInterval precision := ⟨386660218126766518954162596311182923429748854054, 392636893963188684257943818274546422928618447699⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨442633830755694006340905910612713212509395425329, scale precision, 450436560119714483532603399343668928251586417069, scale precision,
    1, 128, 1, 128, ⟨-1745729862897308210917170665156850724896448406291, -1745729862897308210917170665156850724896446309138⟩, ⟨-1720191020636219026556953284692229901319025660064, -1720191020636219026556953284692229901319023562911⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2182146908269555204328257309661848741942720768589, 2219092207387209491851983050978891559944552902744⟩
def wholeBExp : DyadicInterval precision := ⟨70139821416104031847238006738641123098254965624, 73777123032802564323973120756498289740773595894⟩
def wholeBLog : DyadicInterval precision := ⟨68508741729900121249203007750362587432308196434, 71975362561775755035883330367833516631461641036⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨70139821416104031847238006738641123648010779512, scale precision, 73777123032802564323973120756498289191017782006, scale precision,
    4, 128, 4, 128, ⟨-4438184414774418983703966101957783131344354471017, -4438184414774418983703966101957783131344352373864⟩, ⟨-4364293816539110408656514619323697472994952565255, -4364293816539110408656514619323697472994950468102⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0350StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0351StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0351StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133789484, 852249911794452062012049136358764955095133789485⟩
def centerDExp : DyadicInterval precision := ⟨455298659801689467951201474539649436055069582612, 455298659801689467951201474539649438254092838165⟩
def centerDLog : DyadicInterval precision := ⟨396348806111750593903736846609666706637987139797, 396348806111750593903736846609666708837010395350⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649436604825396500, scale precision, 455298659801689467951201474539649437704337024277, scale precision,
    1, 128, 1, 128, ⟨-1704499823588904124024098272717529911954976264684, -1704499823588904124024098272717529911954974167531⟩, ⟨-1704499823588904124024098272717529908425560990410, -1704499823588904124024098272717529908425558893257⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨854168374855825397879120891067389071859059257565, 854168374855825397879120891067389071859059257566⟩
def centerCExp : DyadicInterval precision := ⟨454104917609061906237905344073941074793151398691, 454104917609061906237905344073941076992174654244⟩
def centerCLog : DyadicInterval precision := ⟨395438330636237341426991368612853631556448110402, 395438330636237341426991368612853633755471365955⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨454104917609061906237905344073941075342907212579, scale precision, 454104917609061906237905344073941076442418840356, scale precision,
    1, 128, 1, 128, ⟨-1708336749711650795758241782134778145487466230027, -1708336749711650795758241782134778145487464132874⟩, ⟨-1708336749711650795758241782134778141948772897391, -1708336749711650795758241782134778141948770800238⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2164348769377616234169993975779096492606612441423, 2164348769377616234169993975779096492606612441424⟩
def centerBExp : DyadicInterval precision := ⟨75596097324691436065952183078706705893300973542, 75596097324691436065952183078706708092324229095⟩
def centerBLog : DyadicInterval precision := ⟨73705901915122210753356052051528647858532670033, 73705901915122210753356052051528650057555925586⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75596097324691436065952183078706706443056787430, scale precision, 75596097324691436065952183078706707542568415207, scale precision,
    4, 128, 4, 128, ⟨-4328697538755232468339987951558192995841671718510, -4328697538755232468339987951558192995841669621357⟩, ⟨-4328697538755232468339987951558192974584780144352, -4328697538755232468339987951558192974584778047199⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771969770, 858384943750592238779991986336301839154815993317⟩
def wholeDExp : DyadicInterval precision := ⟨451492192509468156215846209344698067406060081150, 459125158042315647897421247370792079661750447941⟩
def wholeDLog : DyadicInterval precision := ⟨393443605556601543377574216062392475441823025558, 399263485746125009998379766489542017105011910291⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨451492192509468156215846209344698067955815895038, scale precision, 459125158042315647897421247370792079111994634053, scale precision,
    1, 128, 1, 128, ⟨-1716769887501184477559983972672603680089218674697, -1716769887501184477559983972672603680089216577544⟩, ⟨-1692268151626862819173455653290755287573544997795, -1692268151626862819173455653290755287573542900642⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨847833951797256865352882508148884612834709538611, 860523385637997187597699194182143622845389347404⟩
def wholeCExp : DyadicInterval precision := ⟨450172893944187176112303678503271102296432560819, 458058380197845239380428857768220097893223342059⟩
def wholeCLog : DyadicInterval precision := ⟨392435331422632358563970480015087040428290536155, 398451495245439782137559776694878944749300761041⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨450172893944187176112303678503271102846188374707, scale precision, 458058380197845239380428857768220097343467528171, scale precision,
    1, 128, 1, 128, ⟨-1721046771275994375195398388364287247475580723049, -1721046771275994375195398388364287247475578625896⟩, ⟨-1695667903594513730705765016297769223915344538790, -1695667903594513730705765016297769223915342441637⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2145951463721412560569586097096829855802851297000, 2182777455391751358345891469798536797800420068857⟩
def wholeBExp : DyadicInterval precision := ⟨73713490003967344269135003468799472626683038064, 77523456404888232369674435678912814772221222132⟩
def wholeBLog : DyadicInterval precision := ⟨71914786133848703389180051559349801232055605974, 75537323465677196484443442972211083729299475475⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73713490003967344269135003468799473176438851952, scale precision, 77523456404888232369674435678912814222465408244, scale precision,
    4, 128, 4, 128, ⟨-4365554910783502716691782939597073606500732401418, -4365554910783502716691782939597073606500730304265⟩, ⟨-4291902927442825121139172194193659701241498286028, -4291902927442825121139172194193659701241496188875⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0351StableWitnesses

end


