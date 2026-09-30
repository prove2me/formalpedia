-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0379StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0379StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:40:06.868868+00:00
-- url     : https://prove2.me/theorems/185fc6c9-b988-439b-94f7-0e9f1b09f17a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0379StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0380StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0379StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0380StableWitnesses, GeneralCK.Certificates.E8TAxisProd0381StableWitnesses, GeneralCK.Certificates.E8TAxisProd0382StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0379StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0380StableWitnesses, GeneralCK.Certificates.E8TAxisProd0381StableWitnesses, GeneralCK.Certificates.E8TAxisProd0382StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0379StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0380StableWitnesses, GeneralCK.Certificates.E8TAxisProd0381StableWitnesses, GeneralCK.Certificates.E8TAxisProd0382StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0379StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0380StableWitnesses, GeneralCK/Certificates/E8TAxisProd0381StableWitnesses, GeneralCK/Certificates/E8TAxisProd0382StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0379StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0379StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨852889190315615448449543963183516741664994110143, 852889190315615448449543963183516741664994110144⟩
def centerCExp : DyadicInterval precision := ⟨454900527676098478217529110501183679734182518927, 454900527676098478217529110501183681933205774480⟩
def centerCLog : DyadicInterval precision := ⟨396045211004909909007098608182418250525549544810, 396045211004909909007098608182418252724572800363⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨454900527676098478217529110501183680283938332815, scale precision, 454900527676098478217529110501183681383449960592, scale precision,
    1, 128, 1, 128, ⟨-1705778380631230896899087926367033485096241390475, -1705778380631230896899087926367033485096239293322⟩, ⟨-1705778380631230896899087926367033481563737147251, -1705778380631230896899087926367033481563735050098⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2162460403956945114740085698081954186080072761207, 2162460403956945114740085698081954186080072761208⟩
def centerBExp : DyadicInterval precision := ⟨75791701159392643626263249765371986432029376060, 75791701159392643626263249765371988631052631613⟩
def centerBLog : DyadicInterval precision := ⟨73891873913002904555626416440481021067086328882, 73891873913002904555626416440481023266109584435⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75791701159392643626263249765371986981785189948, scale precision, 75791701159392643626263249765371988081296817725, scale precision,
    4, 128, 4, 128, ⟨-4324920807913890229480171396163908382761162379304, -4324920807913890229480171396163908382761160282151⟩, ⟨-4324920807913890229480171396163908361559130762663, -4324920807913890229480171396163908361559128665510⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨846558906105246096241254902365722108228378969843, 859240040157637410861761408854896893440292851031⟩
def wholeCExp : DyadicInterval precision := ⟨450964182758236377261556233941462382357357378255, 458858317987499830828034589092883412380008170114⟩
def wholeCLog : DyadicInterval precision := ⟨393040157505141058248379606078548682767759420784, 399060419605594343747619764800622440818815045061⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨450964182758236377261556233941462382907113192143, scale precision, 458858317987499830828034589092883411830252356226, scale precision,
    1, 128, 1, 128, ⟨-1718480080315274821723522817709793788662256011412, -1718480080315274821723522817709793788662253914259⟩, ⟨-1693117812210492192482509804731444214705741319772, -1693117812210492192482509804731444214705739222619⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2144066377438228262201980441661415519049642859986, 2180885920511365729513263014102073693126633211211⟩
def wholeBExp : DyadicInterval precision := ⟨73904543161670848326548192425889476625031351377, 77723698479483751154188684458002791300663363119⟩
def wholeBLog : DyadicInterval precision := ⟨72096654541033560638799194100711442562740236103, 75727466618091101770600248616159125150818388686⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73904543161670848326548192425889477174787165265, scale precision, 77723698479483751154188684458002790750907549231, scale precision,
    4, 128, 4, 128, ⟨-4361771841022731459026526028204147397124981005216, -4361771841022731459026526028204147397124978908063⟩, ⟨-4288132754876456524403960883322831027761783048986, -4288132754876456524403960883322831027761780951833⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0379StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0380StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0380StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨841520006334222668922736871815753431210942454653, 841520006334222668922736871815753431210942454654⟩
def centerCExp : DyadicInterval precision := ⟨462033314258500265465663771191994575847606707962, 462033314258500265465663771191994578046629963515⟩
def centerCLog : DyadicInterval precision := ⟨401474774532687080666571513712928063193146813549, 401474774532687080666571513712928065392170069102⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨462033314258500265465663771191994576397362521850, scale precision, 462033314258500265465663771191994577496874149627, scale precision,
    1, 128, 1, 128, ⟨-1683040012668445337845473743631506864160870999295, -1683040012668445337845473743631506864160868902142⟩, ⟨-1683040012668445337845473743631506860682900916468, -1683040012668445337845473743631506860682898819315⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2127586617060688187326425150762527372696551112732, 2127586617060688187326425150762527372696551112733⟩
def centerBExp : DyadicInterval precision := ⟨79496423231874609064542751640969040675824581799, 79496423231874609064542751640969042874847837352⟩
def centerBLog : DyadicInterval precision := ⟨77409708508243628628222708827007954838453876569, 77409708508243628628222708827007957037477132122⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨79496423231874609064542751640969041225580395687, scale precision, 79496423231874609064542751640969042325092023464, scale precision,
    4, 128, 4, 128, ⟨-4255173234121376374652850301525054755500086575494, -4255173234121376374652850301525054755500084478341⟩, ⟨-4255173234121376374652850301525054735286119972577, -4255173234121376374652850301525054735286117875424⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨835226426890574751213532654125372779347916601828, 847833951797256865352882508148884612834709538612⟩
def wholeCExp : DyadicInterval precision := ⟨458058380197845239380428857768220095694200086506, 466029753532540862090271280350588481785820143420⟩
def wholeCLog : DyadicInterval precision := ⟨398451495245439782137559776694878942550277505488, 404508118609269361109892836107281647158522428556⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨458058380197845239380428857768220096243955900394, scale precision, 466029753532540862090271280350588481236064329532, scale precision,
    1, 128, 1, 128, ⟨-1695667903594513730705765016297769227423495712809, -1695667903594513730705765016297769227423493615656⟩, ⟨-1670452853781149502427065308250745556971761881232, -1670452853781149502427065308250745556971759784079⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2109255328468702952723541225435170056881228666918, 2145951463721412560569586097096829855802851297001⟩
def wholeBExp : DyadicInterval precision := ⟨77523456404888232369674435678912812573197966579, 81515858417544749862430306575135639066263337470⟩
def wholeBLog : DyadicInterval precision := ⟨75537323465677196484443442972211081530276219922, 79323711987329917054760310596488849380129536062⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨77523456404888232369674435678912813122953780467, scale precision, 81515858417544749862430306575135638516507523582, scale precision,
    4, 128, 4, 128, ⟨-4291902927442825121139172194193659721969908999139, -4291902927442825121139172194193659721969906901986⟩, ⟨-4218510656937405905447082450870340103905860688074, -4218510656937405905447082450870340103905858590921⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0380StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0381StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0381StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨829374204010098155172276587256893404574946736203, 829374204010098155172276587256893404574946736204⟩
def centerCExp : DyadicInterval precision := ⟨469776940629130233117467768828415107660488760270, 469776940629130233117467768828415109859512015823⟩
def centerCLog : DyadicInterval precision := ⟨407346569760126904971981485650448100264388171306, 407346569760126904971981485650448102463411426859⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨469776940629130233117467768828415108210244574158, scale precision, 469776940629130233117467768828415109309756201935, scale precision,
    1, 128, 1, 128, ⟨-1658748408020196310344553174513786810860214787136, -1658748408020196310344553174513786810860212689983⟩, ⟨-1658748408020196310344553174513786807439574254827, -1658748408020196310344553174513786807439572157674⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2091583657432410851683213410529555641509825067805, 2091583657432410851683213410529555641509825067806⟩
def centerBExp : DyadicInterval precision := ⟨83511176993650259439211135768441270472189109419, 83511176993650259439211135768441272671212364972⟩
def centerBLog : DyadicInterval precision := ⟨81212399259795950725882483949631599016700476170, 81212399259795950725882483949631601215723731723⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨83511176993650259439211135768441271021944923307, scale precision, 83511176993650259439211135768441272121456551084, scale precision,
    4, 128, 4, 128, ⟨-4183167314864821703366426821059111292640746839345, -4183167314864821703366426821059111292640744742192⟩, ⟨-4183167314864821703366426821059111273398555529042, -4183167314864821703366426821059111273398553431889⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨823119666057822658831317205669290242800543416657, 835648888392618532375592412211267316411063767078⟩
def wholeCExp : DyadicInterval precision := ⟨465760410378064186411882013764974817968990226768, 473815044798853576550160006882288802980284305368⟩
def wholeCLog : DyadicInterval precision := ⟨404303881745123444696486139378090378071020330009, 410399228548753046178086963627619344196553169127⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨465760410378064186411882013764974818518746040656, scale precision, 473815044798853576550160006882288802430528491480, scale precision,
    1, 128, 1, 128, ⟨-1671297776785237064751184824422534634547197962239, -1671297776785237064751184824422534634547195865086⟩, ⟨-1646239332115645317662634411338580483905343875976, -1646239332115645317662634411338580483905341778823⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2073321618255447963217864367100428326243128250290, 2109881473107979785617291156840548478271919502133⟩
def wholeBExp : DyadicInterval precision := ⟨81446041380659038603020170126134941508982374129, 85624483773334840911141550550571819610072040947⟩
def wholeBLog : DyadicInterval precision := ⟨79257581808944269435646995257710552757231752526, 83210111435141980110766583593979202151199860608⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨81446041380659038603020170126134942058738188017, scale precision, 85624483773334840911141550550571819060316227059, scale precision,
    4, 128, 4, 128, ⟨-4219762946215959571234582313681096966408887003070, -4219762946215959571234582313681096966408884905917⟩, ⟨-4146643236510895926435728734200856643102621155421, -4146643236510895926435728734200856643102619058268⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0381StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0382StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0382StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052157038226, 791434261379870553054051158387221052157038227⟩
def centerAExp : DyadicInterval precision := ⟨1459919625655795613670423245226319210257330755284, 1459919625655795613670423245226319212456354010837⟩
def centerALog : DyadicInterval precision := ⟨1012244519327522357560934184367326742088532965455, 1012244519327522357560934184367326744287556221008⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459919625655795613670423245226319210807086569172, scale precision, 1459919625655795613670423245226319211906598196949, scale precision,
    0, 128, 0, 128, ⟨-1582868522759741106108102316774442654666670423, -1582868522759741106108102316774442654664573270⟩, ⟨-1582868522759741106108102316774441553963579636, -1582868522759741106108102316774441553961482483⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨841096271258761765509910648898646608857789437772, 841096271258761765509910648898646608857789437773⟩
def centerCExp : DyadicInterval precision := ⟨462301307793264162590517764236672060160213589753, 462301307793264162590517764236672062359236845306⟩
def centerCLog : DyadicInterval precision := ⟨401678381806599558516425610580699658180546128465, 401678381806599558516425610580699660379569384018⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨462301307793264162590517764236672060709969403641, scale precision, 462301307793264162590517764236672061809481031418, scale precision,
    1, 128, 1, 128, ⟨-1682192542517523531019821297797293219453556885436, -1682192542517523531019821297797293219453554788283⟩, ⟨-1682192542517523531019821297797293215977602962807, -1682192542517523531019821297797293215977600865654⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2126959345995458857088005295176423766779614118977, 2126959345995458857088005295176423766779614118978⟩
def centerBExp : DyadicInterval precision := ⟨79564691666410586253016751704187380870101572459, 79564691666410586253016751704187383069124828012⟩
def centerBLog : DyadicInterval precision := ⟨77474453702540433535801437645122737246863814795, 77474453702540433535801437645122739445887070348⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨79564691666410586253016751704187381419857386347, scale precision, 79564691666410586253016751704187382519369014124, scale precision,
    4, 128, 4, 128, ⟨-4253918691990917714176010590352847543657540551261, -4253918691990917714176010590352847543657538454108⟩, ⟨-4253918691990917714176010590352847523460918021788, -4253918691990917714176010590352847523460915924635⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 949721161203312387564849132921065893757597831⟩
def wholeAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨834804056921740165325769711375307561820974986758, 847408844063416313893716486071623707147098706302⟩
def wholeCExp : DyadicInterval precision := ⟨458324929075381578872203088156420457561627329180, 466299194036408150378552440494066729537586970175⟩
def wholeCLog : DyadicInterval precision := ⟨398654424340000861397377527043933161832778105402, 404712400738801938296969454599746220983655269897⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨458324929075381578872203088156420458111383143068, scale precision, 466299194036408150378552440494066728987831156287, scale precision,
    1, 128, 1, 128, ⟨-1694817688126832627787432972143247416047253927203, -1694817688126832627787432972143247416047251830050⟩, ⟨-1669608113843480330651539422750615121918874867544, -1669608113843480330651539422750615121918872770391⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2108629224358929368807456045086711453668238740636, 2145323063632182011460624595069210509308471568884⟩
def wholeBExp : DyadicInterval precision := ⟨77590150410469312295714421037103730436078844784, 81585730777896854616537478837310275944719819013⟩
def wholeBLog : DyadicInterval precision := ⟨75600656602218380359029815099798422519338145178, 79389891572004554158206565816201238049157313751⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨77590150410469312295714421037103730985834658672, scale precision, 81585730777896854616537478837310275394964005125, scale precision,
    4, 128, 4, 128, ⟨-4290646127264364022921249190138421028972240804283, -4290646127264364022921249190138421028972238707130⟩, ⟨-4217258448717858737614912090173422897488322308548, -4217258448717858737614912090173422897488320211395⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0382StableWitnesses

end


