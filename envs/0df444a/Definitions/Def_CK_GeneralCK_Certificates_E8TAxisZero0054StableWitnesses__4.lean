-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:39:57.525834+00:00
-- url     : https://prove2.me/theorems/108c0ea8-e545-4d27-bb5f-2876d671dc04
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0055StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0055StableWitnesses, GeneralCK.Certificates.E8TAxisZero0056StableWitnesses, GeneralCK.Certificates.E8TAxisZero0057StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0055StableWitnesses, GeneralCK.Certificates.E8TAxisZero0056StableWitnesses, GeneralCK.Certificates.E8TAxisZero0057StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0055StableWitnesses, GeneralCK.Certificates.E8TAxisZero0056StableWitnesses, GeneralCK.Certificates.E8TAxisZero0057StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisZero0055StableWitnesses, GeneralCK/Certificates/E8TAxisZero0056StableWitnesses, GeneralCK/Certificates/E8TAxisZero0057StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0054StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0054StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨852462981405285549387058583896780795777578571508, 852462981405285549387058583896780795777578571509⟩
def centerCExp : DyadicInterval precision := ⟨455165924860857228347636676448316248880897800147, 455165924860857228347636676448316251079921055700⟩
def centerCLog : DyadicInterval precision := ⟨396247596272224741565612833007079879166081251667, 396247596272224741565612833007079881365104507220⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨455165924860857228347636676448316249430653614035, scale precision, 455165924860857228347636676448316250530165241812, scale precision,
    1, 128, 1, 128, ⟨-1704925962810571098774117167793561593320380450654, -1704925962810571098774117167793561593320378353501⟩, ⟨-1704925962810571098774117167793561589789935932534, -1704925962810571098774117167793561589789933835381⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2161831022368146643392260577941081767660368163864, 2161831022368146643392260577941081767660368163865⟩
def centerBExp : DyadicInterval precision := ⟨75857007209467699670786625005704561834585093657, 75857007209467699670786625005704564033608349210⟩
def centerBLog : DyadicInterval precision := ⟨73953958922723310047967461309952002174413606905, 73953958922723310047967461309952004373436862458⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75857007209467699670786625005704562384340907545, scale precision, 75857007209467699670786625005704563483852535322, scale precision,
    4, 128, 4, 128, ⟨-4323662044736293286784521155882163545912626664937, -4323662044736293286784521155882163545912624567784⟩, ⟨-4323662044736293286784521155882163524728848087657, -4323662044736293286784521155882163524728845990504⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771969770, 858812445251375397578851393656460285506887289656⟩
def wholeCExp : DyadicInterval precision := ⟨451228139240045381581552915086248873212287226831, 459125158042315647897421247370792079661750447941⟩
def wholeCLog : DyadicInterval precision := ⟨393241858475045499848582768855671031121976540031, 399263485746125009998379766489542017105011910291⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨451228139240045381581552915086248873762043040719, scale precision, 459125158042315647897421247370792079111994634053, scale precision,
    1, 128, 1, 128, ⟨-1717624890502750795157702787312920572794402659446, -1717624890502750795157702787312920572794400562293⟩, ⟨-1692268151626862819173455653290755287573544997795, -1692268151626862819173455653290755287573542900642⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2143438091420645379159908740123291916485712358207, 2180255479959191032916878577759762122612913492448⟩
def wholeBExp : DyadicInterval precision := ⟨73968330329506928068097021765167102184939544593, 77790552611549477616722994034945112628552706159⟩
def wholeBLog : DyadicInterval precision := ⟨72157370145147136290993061142388450071734350371, 75790943549876871789636664824308866758637162279⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73968330329506928068097021765167102734695358481, scale precision, 77790552611549477616722994034945112078796892271, scale precision,
    4, 128, 4, 128, ⟨-4360510959918382065833757155519524256088166260538, -4360510959918382065833757155519524256088164163385⟩, ⟨-4286876182841290758319817480246583822642806219859, -4286876182841290758319817480246583822642804122706⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0054StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0055StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0055StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨840249077102780541471889978262527100080586201086, 840249077102780541471889978262527100080586201087⟩
def centerCExp : DyadicInterval precision := ⟨462837586478754670543573783851119661772645661169, 462837586478754670543573783851119663971668916722⟩
def centerCLog : DyadicInterval precision := ⟨402085732755486751135426535363361060118710047019, 402085732755486751135426535363361062317733302572⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨462837586478754670543573783851119662322401475057, scale precision, 462837586478754670543573783851119663421913102834, scale precision,
    1, 128, 1, 128, ⟨-1680498154205561082943779956525054201897136660313, -1680498154205561082943779956525054201897134563160⟩, ⟨-1680498154205561082943779956525054198425210241186, -1680498154205561082943779956525054198425208144033⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2125704921706727598143250444605333805784705474480, 2125704921706727598143250444605333805784705474481⟩
def centerBExp : DyadicInterval precision := ⟨79701391611912706154252071087807997183223863256, 79701391611912706154252071087807999382247118809⟩
def centerBLog : DyadicInterval precision := ⟨77604090130187952127185934389566886734476207506, 77604090130187952127185934389566888933499463059⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨79701391611912706154252071087807997732979677144, scale precision, 79701391611912706154252071087807998832491304921, scale precision,
    4, 128, 4, 128, ⟨-4251409843413455196286500889210667621650403130579, -4251409843413455196286500889210667621650401033426⟩, ⟨-4251409843413455196286500889210667601488420864509, -4251409843413455196286500889210667601488418767356⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871334898, 846558906105246096241254902365722108228378969844⟩
def wholeCExp : DyadicInterval precision := ⟨458858317987499830828034589092883410180984914561, 466838367135635595432846250236128804162502981146⟩
def wholeCLog : DyadicInterval precision := ⟨399060419605594343747619764800622438619791789508, 405121100734994108525530084726425877554191840093⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨458858317987499830828034589092883410730740728449, scale precision, 466838367135635595432846250236128803612747167258, scale precision,
    1, 128, 1, 128, ⟨-1693117812210492192482509804731444218207776656754, -1693117812210492192482509804731444218207774559601⟩, ⟨-1667919182890941556768167636068781992468657623715, -1667919182890941556768167636068781992468655526562⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2107377137908424767296032998711315641015545222180, 2144066377438228262201980441661415519049642859987⟩
def wholeBExp : DyadicInterval precision := ⟨77723698479483751154188684458002789101640107566, 81725641607503649950122630243962611751535119525⟩
def wholeBLog : DyadicInterval precision := ⟨75727466618091101770600248616159122951795133133, 79522399063997544627745901596049332300897746916⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨77723698479483751154188684458002789651395921454, scale precision, 81725641607503649950122630243962611201779305637, scale precision,
    4, 128, 4, 128, ⟨-4288132754876456524403960883322831048436790488121, -4288132754876456524403960883322831048436788390968⟩, ⟨-4214754275816849534592065997422631272199794897079, -4214754275816849534592065997422631272199792799926⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0055StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0056StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0056StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨828111166455057851428312994106305707957915827793, 828111166455057851428312994106305707957915827794⟩
def centerCExp : DyadicInterval precision := ⟨470589610244570117397433420085616217274618212877, 470589610244570117397433420085616219473641468430⟩
def centerCLog : DyadicInterval precision := ⟨407961430901942629435402392650758734823503795102, 407961430901942629435402392650758737022527050655⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨470589610244570117397433420085616217824374026765, scale precision, 470589610244570117397433420085616218923885654542, scale precision,
    1, 128, 1, 128, ⟨-1656222332910115702856625988212611417623199387658, -1656222332910115702856625988212611417623197290505⟩, ⟨-1656222332910115702856625988212611414208466020670, -1656222332910115702856625988212611414208463923517⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2089708961836601552715229851863876864315310503266, 2089708961836601552715229851863876864315310503267⟩
def centerBExp : DyadicInterval precision := ⟨83725694751933551945584007868802199192666574870, 83725694751933551945584007868802201391689830423⟩
def centerBLog : DyadicInterval precision := ⟨81415307798043808102508102272081986535410319096, 81415307798043808102508102272081988734433574649⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨83725694751933551945584007868802199742422388758, scale precision, 83725694751933551945584007868802200841934016535, scale precision,
    4, 128, 4, 128, ⟨-4179417923673203105430459703727753738227067023533, -4179417923673203105430459703727753738227064926380⟩, ⟨-4179417923673203105430459703727753719034177086679, -4179417923673203105430459703727753719034174989526⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 834381778451564747097746049111687847015425241705⟩
def wholeCExp : DyadicInterval precision := ⟨466568731900489908864567195721057951657343327923, 474632069948069015840646238761706424600391594793⟩
def wholeCLog : DyadicInterval precision := ⟨404916728118958536875464286448801445677159965992, 411016094834480306545789264008568525844426144161⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨466568731900489908864567195721057952207099141811, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1668763556903129494195492098223375695752932261353, -1668763556903129494195492098223375695752930164200⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2071450657142232716142500205119195264585536842835, 2108003160823785576510405236660930442051201404350⟩
def wholeBExp : DyadicInterval precision := ⟨81655658496340074886431598560592939065626547727, 85843991343933567659107373077405475871011461648⟩
def wholeBLog : DyadicInterval precision := ⟨79456120588913880911705812005533638415970477018, 83417455822369014920276818117713570012469207921⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨81655658496340074886431598560592939615382361615, scale precision, 85843991343933567659107373077405475321255647760, scale precision,
    4, 128, 4, 128, ⟨-4216006321647571153020810473321860893942126381420, -4216006321647571153020810473321860893942124284267⟩, ⟨-4142901314284465432285000410238390519811432788998, -4142901314284465432285000410238390519811430691845⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0056StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0057StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0057StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨816048427260826356741020123173861709342043745346, 816048427260826356741020123173861709342043745347⟩
def centerCExp : DyadicInterval precision := ⟨478422254686227980476844283326297539028934201667, 478422254686227980476844283326297541227957457220⟩
def centerCLog : DyadicInterval precision := ⟨413874340783744681547561195285871416945391266404, 413874340783744681547561195285871419144414521957⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨478422254686227980476844283326297539578690015555, scale precision, 478422254686227980476844283326297540678201643332, scale precision,
    1, 128, 1, 128, ⟨-1632096854521652713482040246347723420363502517736, -1632096854521652713482040246347723420363500420583⟩, ⟨-1632096854521652713482040246347723417004674560800, -1632096854521652713482040246347723417004672463647⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2053851729919731661891122160470191123854156280525, 2053851729919731661891122160470191123854156280526⟩
def centerBExp : DyadicInterval precision := ⟨87936498323453739023942818534544663908754592911, 87936498323453739023942818534544666107777848464⟩
def centerBLog : DyadicInterval precision := ⟨85392539053787661974621155986781908125412373205, 85392539053787661974621155986781910324435628758⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨87936498323453739023942818534544664458510406799, scale precision, 87936498323453739023942818534544665558022034576, scale precision,
    4, 128, 4, 128, ⟨-4107703459839463323782244320940382256845236701279, -4107703459839463323782244320940382256845234604126⟩, ⟨-4107703459839463323782244320940382238571390517983, -4107703459839463323782244320940382238571388420830⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 822280250006480243024645253100433907067419710190⟩
def wholeCExp : DyadicInterval precision := ⟨474359630541427216902466151616827439334094788034, 482506534178222248007502303634473308617104830159⟩
def wholeCLog : DyadicInterval precision := ⟨410810427914924467030468118471729206140025238384, 416948124396604742320674577430730287178108048617⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨474359630541427216902466151616827439883850601922, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1644560500012960486049290506200867815828637686087, -1644560500012960486049290506200867815828635588934⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2035667381927356861675842006603351527460080068513, 2072074267602144435651804304621012994419385361522⟩
def wholeBExp : DyadicInterval precision := ⟨85770764774929215372249378512379603808772263721, 90152205635118743298799537426527510641302293017⟩
def wholeBLog : DyadicInterval precision := ⟨83348290096937652597862155508503778468524393515, 87481003657361805674317820684111610700972495337⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨85770764774929215372249378512379604358528077609, scale precision, 90152205635118743298799537426527510091546479129, scale precision,
    4, 128, 4, 128, ⟨-4144148535204288871303608609242025998206404487015, -4144148535204288871303608609242025998206402389862⟩, ⟨-4071334763854713723351684013206703046007799957500, -4071334763854713723351684013206703046007797860347⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0057StableWitnesses

end


