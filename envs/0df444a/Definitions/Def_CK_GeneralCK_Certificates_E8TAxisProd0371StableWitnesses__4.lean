-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0371StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0371StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:46:49.943718+00:00
-- url     : https://prove2.me/theorems/4eef0475-af53-4aa9-8717-67ffca41da99
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0371StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0372StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0371StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0372StableWitnesses, GeneralCK.Certificates.E8TAxisProd0373StableWitnesses, GeneralCK.Certificates.E8TAxisProd0374StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0371StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0372StableWitnesses, GeneralCK.Certificates.E8TAxisProd0373StableWitnesses, GeneralCK.Certificates.E8TAxisProd0374StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0371StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0372StableWitnesses, GeneralCK.Certificates.E8TAxisProd0373StableWitnesses, GeneralCK.Certificates.E8TAxisProd0374StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0371StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0372StableWitnesses, GeneralCK/Certificates/E8TAxisProd0373StableWitnesses, GeneralCK/Certificates/E8TAxisProd0374StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0371StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0371StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103956064712, 876906193579724784222253173988686333103956064713⟩
def centerDExp : DyadicInterval precision := ⟨440192694720248252032582341812381160071591754974, 440192694720248252032582341812381162270615010527⟩
def centerDLog : DyadicInterval precision := ⟨384785344583078380142629370287541215891742295997, 384785344583078380142629370287541218090765551550⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨440192694720248252032582341812381160621347568862, scale precision, 440192694720248252032582341812381161720859196639, scale precision,
    1, 128, 1, 128, ⟨-1753812387159449568444506347977372668033179775489, -1753812387159449568444506347977372668033177678336⟩, ⟨-1753812387159449568444506347977372664382646580517, -1753812387159449568444506347977372664382644483364⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨877985269044036004613849530214564711171290058433, 877985269044036004613849530214564711171290058434⟩
def centerCExp : DyadicInterval precision := ⟨439543156481385356709266484546141183369760277650, 439543156481385356709266484546141185568783533203⟩
def centerCLog : DyadicInterval precision := ⟨384286072254675532627379896467729563965527378948, 384286072254675532627379896467729566164550634501⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨439543156481385356709266484546141183919516091538, scale precision, 439543156481385356709266484546141185019027719315, scale precision,
    1, 128, 1, 128, ⟨-1755970538088072009227699060429129424170545064512, -1755970538088072009227699060429129424170542967359⟩, ⟨-1755970538088072009227699060429129420514617266377, -1755970538088072009227699060429129420514615169224⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2235707511266571263602811989954015911090043316376, 2235707511266571263602811989954015911090043316377⟩
def centerBExp : DyadicInterval precision := ⟨68563024920942514345660158009948557073650326045, 68563024920942514345660158009948559272673581598⟩
def centerBLog : DyadicInterval precision := ⟨67003377875837478146061536490128803728786059344, 67003377875837478146061536490128805927809314897⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨68563024920942514345660158009948557623406139933, scale precision, 68563024920942514345660158009948558722917767710, scale precision,
    4, 128, 4, 128, ⟨-4471415022533142527205623979908031833898780417778, -4471415022533142527205623979908031833898778320625⟩, ⟨-4471415022533142527205623979908031810461394944874, -4471415022533142527205623979908031810461392847721⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922944018, 883118980747789020882084464779538700246874405267⟩
def wholeDExp : DyadicInterval precision := ⟨436466074505762269046786189274013976057524048245, 443939237141351316813290285207320726677583911584⟩
def wholeDLog : DyadicInterval precision := ⟨381918529993447746751868483809797874470397239949, 387661827478115861734404726101104697816790214517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013976607279862133, scale precision, 443939237141351316813290285207320726127828097696, scale precision,
    1, 128, 1, 128, ⟨-1766237961495578041764168929559077402334600887543, -1766237961495578041764168929559077402334598790390⟩, ⟨-1741425976352909359667663614025854433695984336263, -1741425976352909359667663614025854433695982239110⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨871573482342784998286909426230622712841626420520, 884418040819471962986432007479179994034843217291⟩
def wholeCExp : DyadicInterval precision := ⟨435690855432030702140972411073033892313902165475, 443416785046317111978847023567809093440530598421⟩
def wholeCLog : DyadicInterval precision := ⟨381321462201720095726327811723155516796746957739, 387261043962642226056881661844812496940540216643⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨435690855432030702140972411073033892863657979363, scale precision, 443416785046317111978847023567809092890774784533, scale precision,
    1, 128, 1, 128, ⟨-1768836081638943925972864014958359989913813913890, -1768836081638943925972864014958359989913811816737⟩, ⟨-1743146964685569996573818852461245423871258833892, -1743146964685569996573818852461245423871256736739⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2217194753359098092659874061683458584647200920936, 2254247680487392150548432768341741895440974344368⟩
def wholeBExp : DyadicInterval precision := ⟨66845367016060047209118565490127957231237479679, 70322181830423103994716874248344498492351929437⟩
def wholeBLog : DyadicInterval precision := ⟨65361767538216464821377468356758717842814342832, 68682740793214751951302055564529042240349002730⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66845367016060047209118565490127957780993293567, scale precision, 70322181830423103994716874248344497942596115549, scale precision,
    4, 128, 4, 128, ⟨-4508495360974784301096865536683483802901765889067, -4508495360974784301096865536683483802901763791914⟩, ⟨-4434389506718196185319748123366917157868861173494, -4434389506718196185319748123366917157868859076341⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0371StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0372StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0372StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨866040646673123429325711732787629329102574016236, 866040646673123429325711732787629329102574016237⟩
def centerCExp : DyadicInterval precision := ⟨446786830389797493647509863163408643044630787391, 446786830389797493647509863163408645243654042944⟩
def centerCLog : DyadicInterval precision := ⟨389844343642767419132083173552920776826296463484, 389844343642767419132083173552920779025319719037⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨446786830389797493647509863163408643594386601279, scale precision, 446786830389797493647509863163408644693898229056, scale precision,
    1, 128, 1, 128, ⟨-1732081293346246858651423465575258660003476532709, -1732081293346246858651423465575258660003474435556⟩, ⟨-1732081293346246858651423465575258656406821629388, -1732081293346246858651423465575258656406819532235⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2199973365094012093526255090073266749657963091800, 2199973365094012093526255090073266749657963091801⟩
def centerBExp : DyadicInterval precision := ⟨71999126291041128678196642869660613753050933498, 71999126291041128678196642869660615952074189051⟩
def centerBLog : DyadicInterval precision := ⟨70281825818776528598330303487726892376465604136, 70281825818776528598330303487726894575488859689⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71999126291041128678196642869660614302806747386, scale precision, 71999126291041128678196642869660615402318375163, scale precision,
    4, 128, 4, 128, ⟨-4399946730188024187052510180146533510475354624140, -4399946730188024187052510180146533510475352526987⟩, ⟨-4399946730188024187052510180146533488156499840198, -4399946730188024187052510180146533488156497743045⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨859667728502263967555650964721109420572533249826, 872434353989953295608084315149513908246795190780⟩
def wholeCExp : DyadicInterval precision := ⟨442894719017326792836216594358679816188094097536, 450700323054599022110638227202814442411692892641⟩
def wholeCLog : DyadicInterval precision := ⟨386860446792147146091213466396632173214521225912, 392838502662609566530874442060077281580258196192⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨442894719017326792836216594358679816737849911424, scale precision, 450700323054599022110638227202814441861937078753, scale precision,
    1, 128, 1, 128, ⟨-1744868707979906591216168630299027818307722390906, -1744868707979906591216168630299027818307720293753⟩, ⟨-1719335457004527935111301929442218839362355220256, -1719335457004527935111301929442218839362353123103⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2181516396628795029617879208831763354977444254034, 2218459689576389178421868795077660563662849924439⟩
def wholeBExp : DyadicInterval precision := ⟨70200558798980498934392486525296303998055377488, 73840807407404543411929476541507582543841961561⟩
def wholeBLog : DyadicInterval precision := ⟨68566696562614670217960819287482860138881924788, 72035985355373274026922761528943413355547967034⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨70200558798980498934392486525296304547811191376, scale precision, 73840807407404543411929476541507581994086147673, scale precision,
    4, 128, 4, 128, ⟨-4436919379152778356843737590155321138771037457103, -4436919379152778356843737590155321138771035359950⟩, ⟨-4363032793257590059235758417663526699073792093867, -4363032793257590059235758417663526699073789996714⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0372StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0373StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0373StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨853741887007587829040784011798955937251135376214, 853741887007587829040784011798955937251135376215⟩
def centerCExp : DyadicInterval precision := ⟨454370024059958384808147134928989592281003881871, 454370024059958384808147134928989594480027137424⟩
def centerCLog : DyadicInterval precision := ⟨395640578171415311801968457943702980687579013085, 395640578171415311801968457943702982886602268638⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨454370024059958384808147134928989592830759695759, scale precision, 454370024059958384808147134928989593930271323536, scale precision,
    1, 128, 1, 128, ⟨-1707483774015175658081568023597911876270586125419, -1707483774015175658081568023597911876270584028266⟩, ⟨-1707483774015175658081568023597911872733957476589, -1707483774015175658081568023597911872733955379436⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2163719277504426508991730451778428615015575466832, 2163719277504426508991730451778428615015575466833⟩
def centerBExp : DyadicInterval precision := ⟨75661246251125170999351979901327994107016324011, 75661246251125170999351979901327996306039579564⟩
def centerBLog : DyadicInterval precision := ⟨73767845435526861080180851538724960424511598122, 73767845435526861080180851538724962623534853675⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75661246251125170999351979901327994656772137899, scale precision, 75661246251125170999351979901327995756283765676, scale precision,
    4, 128, 4, 128, ⟨-4327438555008853017983460903556857240650446032238, -4327438555008853017983460903556857240650443935085⟩, ⟨-4327438555008853017983460903556857219411857932237, -4327438555008853017983460903556857219411855835084⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨847408844063416313893716486071623707147098706301, 860095510318109513278476642346114951551390422738⟩
def wholeCExp : DyadicInterval precision := ⟨450436560119714483532603399343668926602318975404, 458324929075381578872203088156420459760650584733⟩
def wholeCLog : DyadicInterval precision := ⟨392636893963188684257943818274546420729595192146, 398654424340000861397377527043933164031801360955⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨450436560119714483532603399343668927152074789292, scale precision, 458324929075381578872203088156420459210894770845, scale precision,
    1, 128, 1, 128, ⟨-1720191020636219026556953284692229904886538128042, -1720191020636219026556953284692229904886536030889⟩, ⟨-1694817688126832627787432972143247412541142995157, -1694817688126832627787432972143247412541140898004⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2145323063632182011460624595069210509308471568883, 2182146908269555204328257309661848741942720768590⟩
def wholeBExp : DyadicInterval precision := ⟨73777123032802564323973120756498287541750340341, 77590150410469312295714421037103732635102100337⟩
def wholeBLog : DyadicInterval precision := ⟨71975362561775755035883330367833514432438385483, 75600656602218380359029815099798424718361400731⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73777123032802564323973120756498288091506154229, scale precision, 77590150410469312295714421037103732085346286449, scale precision,
    4, 128, 4, 128, ⟨-4364293816539110408656514619323697494775932606262, -4364293816539110408656514619323697494775930509109⟩, ⟨-4290646127264364022921249190138421008261647568423, -4290646127264364022921249190138421008261645471270⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0373StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0374StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0374StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨865611564570895537007758695020559867412669907260, 865611564570895537007758695020559867412669907261⟩
def centerCExp : DyadicInterval precision := ⟨447049251617594316663809094293666517058576667313, 447049251617594316663809094293666519257599922866⟩
def centerCLog : DyadicInterval precision := ⟨390045310473624274151603472303557378678535206788, 390045310473624274151603472303557380877558462341⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨447049251617594316663809094293666517608332481201, scale precision, 447049251617594316663809094293666518707844108978, scale precision,
    1, 128, 1, 128, ⟨-1731223129141791074015517390041119736622612683198, -1731223129141791074015517390041119736622610586045⟩, ⟨-1731223129141791074015517390041119733028069042993, -1731223129141791074015517390041119733028066945840⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2199341867119719677018401877544318851491463946390, 2199341867119719677018401877544318851491463946391⟩
def centerBExp : DyadicInterval precision := ⟨72061373164802036169138866037452937447746199423, 72061373164802036169138866037452939646769454976⟩
def centerBLog : DyadicInterval precision := ⟨70341148946453558319196739969399857395555106862, 70341148946453558319196739969399859594578362415⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨72061373164802036169138866037452937997502013311, scale precision, 72061373164802036169138866037452939097013641088, scale precision,
    4, 128, 4, 128, ⟨-4398683734239439354036803755088637714132716779739, -4398683734239439354036803755088637714132714682586⟩, ⟨-4398683734239439354036803755088637691833141102969, -4398683734239439354036803755088637691833139005816⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨859240040157637410861761408854896893440292851030, 872003870965295638521799561608577658915321878150⟩
def wholeCExp : DyadicInterval precision := ⟨443155703777952795787930073976711168218404704505, 450964182758236377261556233941462384556380633808⟩
def wholeCLog : DyadicInterval precision := ⟨387060722076176269483932963550171795120262618242, 393040157505141058248379606078548684966782676337⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨443155703777952795787930073976711168768160518393, scale precision, 450964182758236377261556233941462384006624819920, scale precision,
    1, 128, 1, 128, ⟨-1744007741930591277043599123217155319643707381485, -1744007741930591277043599123217155319643705284332⟩, ⟨-1718480080315274821723522817709793785098917489864, -1718480080315274821723522817709793785098915392711⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2180885920511365729513263014102073693126633211210, 2217827204886946277479732780045701216393150824227⟩
def wholeBExp : DyadicInterval precision := ⟨70261345592619548552722966815155622512273160024, 73904543161670848326548192425889478824054606930⟩
def wholeBLog : DyadicInterval precision := ⟨68624696241573435016080378020054358064825319939, 72096654541033560638799194100711444761763491656⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨70261345592619548552722966815155623062028973912, scale precision, 73904543161670848326548192425889478274298793042, scale precision,
    4, 128, 4, 128, ⟨-4435654409773892554959465560091402444221737292719, -4435654409773892554959465560091402444221735195566⟩, ⟨-4361771841022731459026526028204147375381553936800, -4361771841022731459026526028204147375381551839647⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0374StableWitnesses

end


