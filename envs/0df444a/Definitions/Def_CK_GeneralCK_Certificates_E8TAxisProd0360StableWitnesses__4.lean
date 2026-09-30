-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0360StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0360StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:50:52.867585+00:00
-- url     : https://prove2.me/theorems/3ac9c19b-7200-4f75-ab26-68ac43146e80
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0360StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0361StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0360StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0361StableWitnesses, GeneralCK.Certificates.E8TAxisProd0362StableWitnesses, GeneralCK.Certificates.E8TAxisProd0363StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0360StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0361StableWitnesses, GeneralCK.Certificates.E8TAxisProd0362StableWitnesses, GeneralCK.Certificates.E8TAxisProd0363StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0360StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0361StableWitnesses, GeneralCK.Certificates.E8TAxisProd0362StableWitnesses, GeneralCK.Certificates.E8TAxisProd0363StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0360StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0361StableWitnesses, GeneralCK/Certificates/E8TAxisProd0362StableWitnesses, GeneralCK/Certificates/E8TAxisProd0363StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0360StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0360StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808718837, 840037336037815392922282998599371946229808718838⟩
def centerDExp : DyadicInterval precision := ⟨462971716911096059979186904937436744746229273838, 462971716911096059979186904937436746945252529391⟩
def centerDLog : DyadicInterval precision := ⟨402187598898660414610829051743418455419293862475, 402187598898660414610829051743418457618317118028⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745295985087726, scale precision, 462971716911096059979186904937436746395496715503, scale precision,
    1, 128, 1, 128, ⟨-1680074672075630785844565997198743894195078759054, -1680074672075630785844565997198743894195076661901⟩, ⟨-1680074672075630785844565997198743890724158213450, -1680074672075630785844565997198743890724156116297⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨842367752650739667160339426098975995952391016309, 842367752650739667160339426098975995952391016310⟩
def centerCExp : DyadicInterval precision := ⟨461497618752696694286927509009400725778501500973, 461497618752696694286927509009400727977524756526⟩
def centerCLog : DyadicInterval precision := ⟨401067696461033575700638006848395485043583246004, 401067696461033575700638006848395487242606501557⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨461497618752696694286927509009400726328257314861, scale precision, 461497618752696694286927509009400727427768942638, scale precision,
    1, 128, 1, 128, ⟨-1684735505301479334320678852197951993645786695259, -1684735505301479334320678852197951993645784598106⟩, ⟨-1684735505301479334320678852197951990163779467132, -1684735505301479334320678852197951990163777369979⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2128841276811191065447546137699495564748185215113, 2128841276811191065447546137699495564748185215114⟩
def centerBExp : DyadicInterval precision := ⟨79360049266839177839900480089643603319824381456, 79360049266839177839900480089643605518847637009⟩
def centerBLog : DyadicInterval precision := ⟨77280364028176152205153630711384759979771207769, 77280364028176152205153630711384762178794463322⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨79360049266839177839900480089643603869580195344, scale precision, 79360049266839177839900480089643604969091823121, scale precision,
    4, 128, 4, 128, ⟨-4257682553622382130895092275398991139620722831323, -4257682553622382130895092275398991139620720734170⟩, ⟨-4257682553622382130895092275398991119372020126297, -4257682553622382130895092275398991119372018029144⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871334898, 846134075813431409586727826645377644661771969771⟩
def wholeDExp : DyadicInterval precision := ⟨459125158042315647897421247370792077462727192388, 466838367135635595432846250236128804162502981146⟩
def wholeDLog : DyadicInterval precision := ⟨399263485746125009998379766489542014905988654738, 405121100734994108525530084726425877554191840093⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078012483006276, scale precision, 466838367135635595432846250236128803612747167258, scale precision,
    1, 128, 1, 128, ⟨-1692268151626862819173455653290755291073544978437, -1692268151626862819173455653290755291073542881284⟩, ⟨-1667919182890941556768167636068781992468657623715, -1667919182890941556768167636068781992468655526562⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨836071441462393785116710345027261493919776976649, 848684444942940137950734061958399522548509135973⟩
def wholeCExp : DyadicInterval precision := ⟨457525573549416586297719953383741049917241490074, 465491164562179826958837533347876239127442771960⟩
def wholeCLog : DyadicInterval precision := ⟨398045774209170478380685603013215132338932029198, 404099690161144398945313792480534186082342258678⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨457525573549416586297719953383741050466997303962, scale precision, 465491164562179826958837533347876238577686958072, scale precision,
    1, 128, 1, 128, ⟨-1697368889885880275901468123916799046853137598014, -1697368889885880275901468123916799046853135500861⟩, ⟨-1672142882924787570233420690054522986113487821016, -1672142882924787570233420690054522986113485723863⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2110507658231659998199062601393666866215128957760, 2147208377666739535822500886478367097466154716868⟩
def wholeBExp : DyadicInterval precision := ⟨77390228280044607516669534156043608983158050463, 81376279632619547840531729731432640307465527080⟩
def wholeBLog : DyadicInterval precision := ⟨75410800804220849067664855997253273310464522573, 79191501010895897489945208840241322129044394899⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨77390228280044607516669534156043609532913864351, scale precision, 81376279632619547840531729731432639757709713192, scale precision,
    4, 128, 4, 128, ⟨-4294416755333479071645001772956734205314357931797, -4294416755333479071645001772956734205314355834644⟩, ⟨-4221015316463319996398125202787333722556754968116, -4221015316463319996398125202787333722556752870963⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0360StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0361StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0361StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005680170, 827900739799584217789378743685278152778005680171⟩
def centerDExp : DyadicInterval precision := ⟨470725140515848859951996893419642374006683999039, 470725140515848859951996893419642376205707254592⟩
def centerDLog : DyadicInterval precision := ⟨408063947160780491089293755661542510045178856930, 408063947160780491089293755661542512244202112483⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642374556439812927, scale precision, 470725140515848859951996893419642375655951440704, scale precision,
    1, 128, 1, 128, ⟨-1655801479599168435578757487370556307262887510703, -1655801479599168435578757487370556307262885413550⟩, ⟨-1655801479599168435578757487370556303849137307135, -1655801479599168435578757487370556303849135209982⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨830216684245410539759080100354856763643502198479, 830216684245410539759080100354856763643502198480⟩
def centerCExp : DyadicInterval precision := ⟨469235648413544900713505332148472750088893654971, 469235648413544900713505332148472752287916910524⟩
def centerCLog : DyadicInterval precision := ⟨406936887618752275382872845022164717679488812432, 406936887618752275382872845022164719878512067985⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨469235648413544900713505332148472750638649468859, scale precision, 469235648413544900713505332148472751738161096636, scale precision,
    1, 128, 1, 128, ⟨-1660433368490821079518160200709713528999298671439, -1660433368490821079518160200709713528999296574286⟩, ⟨-1660433368490821079518160200709713525574712219636, -1660433368490821079518160200709713525574710122483⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2092833663645277134719109490011306518038238526746, 2092833663645277134719109490011306518038238526747⟩
def centerBExp : DyadicInterval precision := ⟨83368446728927546584266638254553596493681525001, 83368446728927546584266638254553598692704780554⟩
def centerBLog : DyadicInterval precision := ⟨81077377627845847823629217290285721803728797554, 81077377627845847823629217290285724002752053107⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨83368446728927546584266638254553597043437338889, scale precision, 83368446728927546584266638254553598142948966666, scale precision,
    4, 128, 4, 128, ⟨-4185667327290554269438218980022613045714045475050, -4185667327290554269438218980022613045714043377897⟩, ⟨-4185667327290554269438218980022613026438910729102, -4185667327290554269438218980022613026438908631949⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 833959591445470778384083818034390997094871334899⟩
def wholeDExp : DyadicInterval precision := ⟨466838367135635595432846250236128801963479725593, 474632069948069015840646238761706424600391594793⟩
def wholeDLog : DyadicInterval precision := ⟨405121100734994108525530084726425875355168584540, 411016094834480306545789264008568525844426144161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128802513235539481, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1667919182890941556768167636068781995910829813032, -1667919182890941556768167636068781995910827715879⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨823959444225399528213594891142050812609083954478, 836494086134394973614340827838498053694494352150⟩
def wholeCExp : DyadicInterval precision := ⟨465222016074115009417679513239332272553121471020, 473270849740013274045065979419457373956047924073⟩
def wholeCLog : DyadicInterval precision := ⟨403895543872129983636156690568345480853894369186, 409988208574797875699408007543785421785496111330⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨465222016074115009417679513239332273102877284908, scale precision, 473270849740013274045065979419457373406292110185, scale precision,
    1, 128, 1, 128, ⟨-1672988172268789947228681655676996109116055528719, -1672988172268789947228681655676996109116053431566⟩, ⟨-1647918888450799056427189782284101623520475083991, -1647918888450799056427189782284101623520472986838⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2074569141575912069928451621905706530805239124170, 2111133883794670418956754162681229452744112211720⟩
def wholeBExp : DyadicInterval precision := ⟨81306573138810685320129523596731976711938294552, 85478432054745895219212239942834848819200572364⟩
def wholeBLog : DyadicInterval precision := ⟨79125469567227112931100377069106752239806390749, 83072136321897740599605438132793357587250347503⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨81306573138810685320129523596731977261694108440, scale precision, 85478432054745895219212239942834848269444758476, scale precision,
    4, 128, 4, 128, ⟨-4222267767589340837913508325362458915370194310604, -4222267767589340837913508325362458915370192213451⟩, ⟨-4149138283151824139856903243811413052210809663105, -4149138283151824139856903243811413052210807565952⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0361StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0362StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0362StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808718837, 840037336037815392922282998599371946229808718838⟩
def centerDExp : DyadicInterval precision := ⟨462971716911096059979186904937436744746229273838, 462971716911096059979186904937436746945252529391⟩
def centerDLog : DyadicInterval precision := ⟨402187598898660414610829051743418455419293862475, 402187598898660414610829051743418457618317118028⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745295985087726, scale precision, 462971716911096059979186904937436746395496715503, scale precision,
    1, 128, 1, 128, ⟨-1680074672075630785844565997198743894195078759054, -1680074672075630785844565997198743894195076661901⟩, ⟨-1680074672075630785844565997198743890724158213450, -1680074672075630785844565997198743890724156116297⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨841943833453514544764169321793978044656952163602, 841943833453514544764169321793978044656952163603⟩
def centerCExp : DyadicInterval precision := ⟨461765417915118681065051504876326270630700429731, 461765417915118681065051504876326272829723685284⟩
def centerCLog : DyadicInterval precision := ⟨401271212745818718132068593502079293696993906056, 401271212745818718132068593502079295896017161609⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨461765417915118681065051504876326271180456243619, scale precision, 461765417915118681065051504876326272279967871396, scale precision,
    1, 128, 1, 128, ⟨-1683887666907029089528338643587956091053899301178, -1683887666907029089528338643587956091053897204025⟩, ⟨-1683887666907029089528338643587956087573911450386, -1683887666907029089528338643587956087573909353233⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2128213927347368688651741415953170072841308500524, 2128213927347368688651741415953170072841308500525⟩
def centerBExp : DyadicInterval precision := ⟨79428209110175231997435600303074993836883875458, 79428209110175231997435600303074996035907131011⟩
def centerBLog : DyadicInterval precision := ⟨77345011958825683796374774534379426656941902751, 77345011958825683796374774534379428855965158304⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨79428209110175231997435600303074994386639689346, scale precision, 79428209110175231997435600303074995486151317123, scale precision,
    4, 128, 4, 128, ⟨-4256427854694737377303482831906340155798281377940, -4256427854694737377303482831906340155798279280787⟩, ⟨-4256427854694737377303482831906340135566954721293, -4256427854694737377303482831906340135566952624140⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871334898, 846134075813431409586727826645377644661771969771⟩
def wholeDExp : DyadicInterval precision := ⟨459125158042315647897421247370792077462727192388, 466838367135635595432846250236128804162502981146⟩
def wholeDLog : DyadicInterval precision := ⟨399263485746125009998379766489542014905988654738, 405121100734994108525530084726425877554191840093⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078012483006276, scale precision, 466838367135635595432846250236128803612747167258, scale precision,
    1, 128, 1, 128, ⟨-1692268151626862819173455653290755291073544978437, -1692268151626862819173455653290755291073542881284⟩, ⟨-1667919182890941556768167636068781992468657623715, -1667919182890941556768167636068781992468655526562⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨835648888392618532375592412211267316411063767077, 848259152079208575771423146945791430608399016704⟩
def wholeCExp : DyadicInterval precision := ⟨457791928359208882212008675321149404297229322041, 465760410378064186411882013764974820168013482321⟩
def wholeCLog : DyadicInterval precision := ⟨398248611863398573671141327189844443691460970512, 404303881745123444696486139378090380270043585562⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨457791928359208882212008675321149404846985135929, scale precision, 465760410378064186411882013764974819618257668433, scale precision,
    1, 128, 1, 128, ⟨-1696518304158417151542846293891582862971895605878, -1696518304158417151542846293891582862971893508725⟩, ⟨-1671297776785237064751184824422534631097059203223, -1671297776785237064751184824422534631097057106070⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2109881473107979785617291156840548478271919502132, 2146579901747431857436991023294185168826235441511⟩
def wholeBExp : DyadicInterval precision := ⟨77456815706180140722399949399194482227281368241, 81446041380659038603020170126134943708005629682⟩
def wholeBLog : DyadicInterval precision := ⟨75474038208423573864964984131385340789036273500, 79257581808944269435646995257710554956255008079⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨77456815706180140722399949399194482777037182129, scale precision, 81446041380659038603020170126134943158249815794, scale precision,
    4, 128, 4, 128, ⟨-4293159803494863714873982046588370348025594229556, -4293159803494863714873982046588370348025592132403⟩, ⟨-4219762946215959571234582313681096946678793102619, -4219762946215959571234582313681096946678791005466⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0362StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0363StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0363StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005680170, 827900739799584217789378743685278152778005680171⟩
def centerDExp : DyadicInterval precision := ⟨470725140515848859951996893419642374006683999039, 470725140515848859951996893419642376205707254592⟩
def centerDLog : DyadicInterval precision := ⟨408063947160780491089293755661542510045178856930, 408063947160780491089293755661542512244202112483⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642374556439812927, scale precision, 470725140515848859951996893419642375655951440704, scale precision,
    1, 128, 1, 128, ⟨-1655801479599168435578757487370556307262887510703, -1655801479599168435578757487370556307262885413550⟩, ⟨-1655801479599168435578757487370556303849137307135, -1655801479599168435578757487370556303849135209982⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨829795398584615555605671300841179250340519819954, 829795398584615555605671300841179250340519819955⟩
def centerCExp : DyadicInterval precision := ⟨469506245775979767987991532579203186448803219374, 469506245775979767987991532579203188647826474927⟩
def centerCLog : DyadicInterval precision := ⟨407141706151105553765739676696255505810520325945, 407141706151105553765739676696255508009543581498⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨469506245775979767987991532579203186998559033262, scale precision, 469506245775979767987991532579203188098070661039, scale precision,
    1, 128, 1, 128, ⟨-1659590797169231111211342601682358502392347043532, -1659590797169231111211342601682358502392344946379⟩, ⟨-1659590797169231111211342601682358498969734333440, -1659590797169231111211342601682358498969732236287⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2092208639654515695117460176866379112258592460588, 2092208639654515695117460176866379112258592460589⟩
def centerBExp : DyadicInterval precision := ⟨83439783727034363427333408316875609539931640140, 83439783727034363427333408316875611738954895693⟩
def centerBLog : DyadicInterval precision := ⟨81144863388308077398995230886649293670527575261, 81144863388308077398995230886649295869550830814⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨83439783727034363427333408316875610089687454028, scale precision, 83439783727034363427333408316875611189199081805, scale precision,
    4, 128, 4, 128, ⟨-4184417279309031390234920353732758234146513686599, -4184417279309031390234920353732758234146511589446⟩, ⟨-4184417279309031390234920353732758214887858252910, -4184417279309031390234920353732758214887856155757⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 833959591445470778384083818034390997094871334899⟩
def wholeDExp : DyadicInterval precision := ⟨466838367135635595432846250236128801963479725593, 474632069948069015840646238761706424600391594793⟩
def wholeDLog : DyadicInterval precision := ⟨405121100734994108525530084726425875355168584540, 411016094834480306545789264008568525844426144161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128802513235539481, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1667919182890941556768167636068781995910829813032, -1667919182890941556768167636068781995910827715879⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨823539509859430523244296081108954404821923089897, 836071441462393785116710345027261493919776976650⟩
def wholeCExp : DyadicInterval precision := ⟨465491164562179826958837533347876236928419516407, 473542898439744410988485104098145146438168171878⟩
def wholeCLog : DyadicInterval precision := ⟨404099690161144398945313792480534183883319003125, 410193696130617163810602601810729209144395691598⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨465491164562179826958837533347876237478175330295, scale precision, 473542898439744410988485104098145145888412357990, scale precision,
    1, 128, 1, 128, ⟨-1672142882924787570233420690054522989565622182733, -1672142882924787570233420690054522989565620085580⟩, ⟨-1647079019718861046488592162217908807947128673879, -1647079019718861046488592162217908807947126576726⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2073945358355583370179844590123450346530242728894, 2110507658231659998199062601393666866215128957761⟩
def wholeBExp : DyadicInterval precision := ⟨81376279632619547840531729731432638108442271527, 85551429271079398229205787359921126104233307164⟩
def wholeBLog : DyadicInterval precision := ⟨79191501010895897489945208840241319930021139346, 83141098447720451170806673649633560311965502671⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨81376279632619547840531729731432638658198085415, scale precision, 85551429271079398229205787359921125554477493276, scale precision,
    4, 128, 4, 128, ⟨-4221015316463319996398125202787333742303762960065, -4221015316463319996398125202787333742303760862912⟩, ⟨-4147890716711166740359689180246900683668837191145, -4147890716711166740359689180246900683668835093992⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0363StableWitnesses

end


