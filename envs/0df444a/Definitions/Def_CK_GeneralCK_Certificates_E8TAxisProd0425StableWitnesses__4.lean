-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0425StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0425StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:12:45.463438+00:00
-- url     : https://prove2.me/theorems/c4738758-d031-4a18-9608-535b0d7c7585
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0425StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0426StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0425StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0426StableWitnesses, GeneralCK.Certificates.E8TAxisProd0427StableWitnesses, GeneralCK.Certificates.E8TAxisProd0428StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0425StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0426StableWitnesses, GeneralCK.Certificates.E8TAxisProd0427StableWitnesses, GeneralCK.Certificates.E8TAxisProd0428StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0425StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0426StableWitnesses, GeneralCK.Certificates.E8TAxisProd0427StableWitnesses, GeneralCK.Certificates.E8TAxisProd0428StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0425StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0426StableWitnesses, GeneralCK/Certificates/E8TAxisProd0427StableWitnesses, GeneralCK/Certificates/E8TAxisProd0428StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0425StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0425StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    1, 128, 1, 128, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨781535104821849587713952985425176800294058430937, 781535104821849587713952985425176800294058430938⟩
def centerCExp : DyadicInterval precision := ⟨501560213779684405899947480130392083266259897299, 501560213779684405899947480130392085465283152852⟩
def centerCLog : DyadicInterval precision := ⟨431202900754593535769776230428197764804754038161, 431202900754593535769776230428197767003777293714⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨501560213779684405899947480130392083816015711187, scale precision, 501560213779684405899947480130392084915527338964, scale precision,
    1, 128, 1, 128, ⟨-1563070209643699175427905970850353602190057219146, -1563070209643699175427905970850353602190055121993⟩, ⟨-1563070209643699175427905970850353598986178601760, -1563070209643699175427905970850353598986176504607⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1949044391042119150500386730910980259891042679192, 1949044391042119150500386730910980259891042679193⟩
def centerBExp : DyadicInterval precision := ⟨101498003330490795434455654511186000178597465184, 101498003330490795434455654511186002377620720737⟩
def centerBLog : DyadicInterval precision := ⟨98128721190119442839233936859568690319899427997, 98128721190119442839233936859568692518922683550⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨101498003330490795434455654511186000728353279072, scale precision, 101498003330490795434455654511186001827864906849, scale precision,
    3, 128, 3, 128, ⟨-3898088782084238301000773461821960527698193086553, -3898088782084238301000773461821960527698190989400⟩, ⟨-3898088782084238301000773461821960511865979727360, -3898088782084238301000773461821960511865977630207⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    1, 128, 1, 128, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨775432328552213371123651796916866265092182828968, 787657103042136116951144363382437172691785123230⟩
def wholeCExp : DyadicInterval precision := ⟨497375853732928756720080388260302031244973453141, 505766472266583410881082158744458423896447560107⟩
def wholeCLog : DyadicInterval precision := ⟨428084315357742611686558468171745791416596621213, 434331114453733428112135098152781596452885943290⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨497375853732928756720080388260302031794729267029, scale precision, 505766472266583410881082158744458423346691746219, scale precision,
    1, 128, 1, 128, ⟨-1575314206084272233902288726764874346998987516189, -1575314206084272233902288726764874346998985419036⟩, ⟨-1550864657104426742247303593833732528595750089579, -1550864657104426742247303593833732528595747992426⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1931105360713592607389313087065962976094733376268, 1967028749262024872130813294475568417897470547204⟩
def wholeBExp : DyadicInterval precision := ⟨99030544433443841396784624849365208614845691500, 104020489270316520549155326343058439590902157925⟩
def wholeBLog : DyadicInterval precision := ⟨95819670939810456650269690282069555127616331274, 100485500784025608312231058662312084980132605591⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨99030544433443841396784624849365209164601505388, scale precision, 104020489270316520549155326343058439041146344037, scale precision,
    3, 128, 3, 128, ⟨-3934057498524049744261626588951136843908287643874, -3934057498524049744261626588951136843908285546721⟩, ⟨-3862210721427185214778626174131925944465325877097, -3862210721427185214778626174131925944465323779944⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0425StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0426StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0426StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨792971589581574524571428138506212753632800822272, 792971589581574524571428138506212753632800822273⟩
def centerCExp : DyadicInterval precision := ⟨493771740540620584203231643089298982719173940599, 493771740540620584203231643089298984918197196152⟩
def centerCLog : DyadicInterval precision := ⟨425392840758662088907725153316287117948643039924, 425392840758662088907725153316287120147666295477⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨493771740540620584203231643089298983268929754487, scale precision, 493771740540620584203231643089298984368441382264, scale precision,
    1, 128, 1, 128, ⟨-1585943179163149049142856277012425508892810076944, -1585943179163149049142856277012425508892807979791⟩, ⟨-1585943179163149049142856277012425505638395309301, -1585943179163149049142856277012425505638393212148⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1983823078679455189822857677238263111105167116696, 1983823078679455189822857677238263111105167116697⟩
def centerBExp : DyadicInterval precision := ⟨96780549501409276054900388572520375617679821528, 96780549501409276054900388572520377816703077081⟩
def centerBLog : DyadicInterval precision := ⟨93710938928857999088506259595398203344858501980, 93710938928857999088506259595398205543881757533⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96780549501409276054900388572520376167435635416, scale precision, 96780549501409276054900388572520377266947263193, scale precision,
    3, 128, 3, 128, ⟨-3967646157358910379645715354476526230512303252491, -3967646157358910379645715354476526230512301155338⟩, ⟨-3967646157358910379645715354476526213908367311447, -3967646157358910379645715354476526213908365214294⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨786832854271741777908334690340732380993538781502, 799129776074145010927973484050916306597305645700⟩
def wholeCExp : DyadicInterval precision := ⟨489628109307077895065295537232838888885296782683, 497937184243805888763818549503254931938948063843⟩
def wholeCLog : DyadicInterval precision := ⟨422292328133333896884740329317328097846908611462, 428503059226733886998689685215175847365470334513⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨489628109307077895065295537232838889435052596571, scale precision, 497937184243805888763818549503254931389192249955, scale precision,
    1, 128, 1, 128, ⟨-1598259552148290021855946968101832614835590475946, -1598259552148290021855946968101832614835588378793⟩, ⟨-1573665708543483555816669380681464760373483468351, -1573665708543483555816669380681464760373481371198⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1965797631890294377150791266202628045162862188277, 2001891418568329185984063018994951661508980170850⟩
def wholeBExp : DyadicInterval precision := ⟨94416922374013343216834104402173947153676428896, 99197524719707794724808724212287812562703421308⟩
def wholeBLog : DyadicInterval precision := ⟨91492427110769098957899019788050943459700244712, 95976046379582433705471703141351812577000331088⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨94416922374013343216834104402173947703432242784, scale precision, 99197524719707794724808724212287812012947607420, scale precision,
    3, 128, 3, 128, ⟨-4003782837136658371968126037989903331527760289969, -4003782837136658371968126037989903331527758192816⟩, ⟨-3931595263780588754301582532405256082226037208111, -3931595263780588754301582532405256082226035110958⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0426StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0427StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0427StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    1, 128, 1, 128, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨781124232849980692344778674741273356314991136516, 781124232849980692344778674741273356314991136517⟩
def centerCExp : DyadicInterval precision := ⟨501842300332418782112917332575501373089673331348, 501842300332418782112917332575501375288696586901⟩
def centerCLog : DyadicInterval precision := ⟨431412899405562501268372715863852931088956951355, 431412899405562501268372715863852933287980206908⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨501842300332418782112917332575501373639429145236, scale precision, 501842300332418782112917332575501374738940773013, scale precision,
    1, 128, 1, 128, ⟨-1562248465699961384689557349482546714231022177039, -1562248465699961384689557349482546714231020079886⟩, ⟨-1562248465699961384689557349482546711028944466180, -1562248465699961384689557349482546711028942369027⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1948430335268744930280462926188162987057797156795, 1948430335268744930280462926188162987057797156796⟩
def centerBExp : DyadicInterval precision := ⟨101583328761480673954814287677959045760862703898, 101583328761480673954814287677959047959885959451⟩
def centerBLog : DyadicInterval precision := ⟨98208503584274242157692559318388990638317780041, 98208503584274242157692559318388992837341035594⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨101583328761480673954814287677959046310618517786, scale precision, 101583328761480673954814287677959047410130145563, scale precision,
    3, 128, 3, 128, ⟨-3896860670537489860560925852376325982025052867898, -3896860670537489860560925852376325982025050770745⟩, ⟨-3896860670537489860560925852376325966206137856424, -3896860670537489860560925852376325966206135759271⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    1, 128, 1, 128, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨775022744363554043756785782405543814624154464308, 787244934960362713248492454397955357972175880984⟩
def wholeCExp : DyadicInterval precision := ⟨497656469602704994474302344624992112905200865934, 506050032695680427064707716814256868738864576958⟩
def wholeCLog : DyadicInterval precision := ⟨428293665448410436788381560004412425121659701891, 434541758933193955152354548617875082426296374617⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨497656469602704994474302344624992113454956679822, scale precision, 506050032695680427064707716814256868189108763070, scale precision,
    1, 128, 1, 128, ⟨-1574489869920725426496984908795910717558858139436, -1574489869920725426496984908795910717558856042283⟩, ⟨-1550045488727108087513571564811087627660583526807, -1550045488727108087513571564811087627660581429654⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1930492877153593559344635681284615444553683103916, 1966413164801763508313912999584903235670242461289⟩
def wholeBExp : DyadicInterval precision := ⟨99114002907865010828061597352454783481949735779, 104107711268899147405751493812832773763600025245⟩
def wholeBLog : DyadicInterval precision := ⟨95897831093703115009974444514581910537592974359, 100566925083696430313465737769915716737519500395⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨99114002907865010828061597352454784031705549667, scale precision, 104107711268899147405751493812832773213844211357, scale precision,
    3, 128, 3, 128, ⟨-3932826329603527016627825999169806479446999668086, -3932826329603527016627825999169806479446997570933⟩, ⟨-3860985754307187118689271362569230881389696659903, -3860985754307187118689271362569230881389694562750⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0427StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0428StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0428StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219489900939, 768328048611850508777866556237345596219489900940⟩
def centerDExp : DyadicInterval precision := ⟨510707457819051547382306257729904114775482130573, 510707457819051547382306257729904116974505386126⟩
def centerDLog : DyadicInterval precision := ⟨437997216266833750200638020923159195569100090572, 437997216266833750200638020923159197768123346125⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115325237944461, scale precision, 510707457819051547382306257729904116424749572238, scale precision,
    1, 128, 1, 128, ⟨-1536656097223701017555733112474691194012227940995, -1536656097223701017555733112474691194012225843842⟩, ⟨-1536656097223701017555733112474691190865733759918, -1536656097223701017555733112474691190865731662765⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨769757040459667063908025967258042238680118921913, 769757040459667063908025967258042238680118921914⟩
def centerCExp : DyadicInterval precision := ⟨509709739202802483786341500315427661853934745272, 509709739202802483786341500315427664052958000825⟩
def centerCLog : DyadicInterval precision := ⟨437257671786183946078315424658774700692349684588, 437257671786183946078315424658774702891372940141⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨509709739202802483786341500315427662403690559160, scale precision, 509709739202802483786341500315427663503202186937, scale precision,
    1, 128, 1, 128, ⟨-1539514080919334127816051934516084478936565496222, -1539514080919334127816051934516084478936563399069⟩, ⟨-1539514080919334127816051934516084475783912288587, -1539514080919334127816051934516084475783910191434⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1913823860515916632277285572466255083850964575529, 1913823860515916632277285572466255083850964575530⟩
def centerBExp : DyadicInterval precision := ⟨106509784747321832162111567489582728402216628263, 106509784747321832162111567489582730601239883816⟩
def centerBLog : DyadicInterval precision := ⟨102807550396221067730542765162913686876212927866, 102807550396221067730542765162913689075236183419⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨106509784747321832162111567489582728951972442151, scale precision, 106509784747321832162111567489582730051484069928, scale precision,
    3, 128, 3, 128, ⟨-3827647721031833264554571144932510175245547192544, -3827647721031833264554571144932510175245545095391⟩, ⟨-3827647721031833264554571144932510160158313206740, -3827647721031833264554571144932510160158311109587⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774203834768265108571628471566363912561698867071⟩
def wholeDExp : DyadicInterval precision := ⟨506617451172271417683927781753795729433033108588, 514818014850194000087183801285808387115302195067⟩
def wholeDLog : DyadicInterval precision := ⟨434963177842048586751554818318029031715400615655, 441040166381185817721359138930122618351494322418⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795729982788922476, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    1, 128, 1, 128, ⟨-1548407669536530217143256943132727826709346957757, -1548407669536530217143256943132727826709344860604⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨763691062682720100476354894974204402380994667847, 775841999052126928446482771428197232230962975208⟩
def wholeCExp : DyadicInterval precision := ⟨505483011023759798317113236082214217217594743390, 513958460336090730144921946111590589511696472804⟩
def wholeCLog : DyadicInterval precision := ⟨434120513306978910637193019627830675175319972622, 440404381783323710599121272173282037345417169975⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨505483011023759798317113236082214217767350557278, scale precision, 513958460336090730144921946111590588961940658916, scale precision,
    1, 128, 1, 128, ⟨-1551683998104253856892965542856394466051434469287, -1551683998104253856892965542856394466051432372134⟩, ⟨-1527382125365440200952709789948408803198694740486, -1527382125365440200952709789948408803198692643333⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1895977674554158830518905568418500625844830299331, 1931717898747472958507222928566380194917449049785⟩
def wholeBExp : DyadicInterval precision := ⟨103933332599072551870778748156191279613519605647, 109142958457645244299677340508551939545549576648⟩
def wholeBLog : DyadicInterval precision := ⟨100404132937815643758072345072837902452464158154, 105259802933603921945267516744924859896970819012⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103933332599072551870778748156191280163275419535, scale precision, 109142958457645244299677340508551938995793762760, scale precision,
    3, 128, 3, 128, ⟨-3863435797494945917014445857132760397565518402219, -3863435797494945917014445857132760397565516305066⟩, ⟨-3791955349108317661037811136837001244328041314747, -3791955349108317661037811136837001244328039217594⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0428StableWitnesses

end


