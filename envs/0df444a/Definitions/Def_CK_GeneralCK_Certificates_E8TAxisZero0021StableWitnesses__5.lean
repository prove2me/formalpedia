-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0021StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0021StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:46:49.55848+00:00
-- url     : https://prove2.me/theorems/67aa0f85-a5e5-43dd-a066-1912170940d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0021StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0022StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0021StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0022StableWitnesses, GeneralCK.Certificates.E8TAxisZero0023StableWitnesses, GeneralCK.Certificates.E8TAxisZero0024StableWitnesses, GeneralCK.Certificates.E8TAxisZero0025StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0021StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0022StableWitnesses, GeneralCK.Certificates.E8TAxisZero0023StableWitnesses, GeneralCK.Certificates.E8TAxisZero0024StableWitnesses, GeneralCK.Certificates.E8TAxisZero0025StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0021StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0022StableWitnesses, GeneralCK.Certificates.E8TAxisZero0023StableWitnesses, GeneralCK.Certificates.E8TAxisZero0024StableWitnesses, GeneralCK.Certificates.E8TAxisZero0025StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0021StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0022StableWitnesses, GeneralCK/Certificates/E8TAxisZero0023StableWitnesses, GeneralCK/Certificates/E8TAxisZero0024StableWitnesses, GeneralCK/Certificates/E8TAxisZero0025StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0021StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0021StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨91152031099581959275053171704673662682537650095, 91152031099581959275053171704673662682537650096⟩
def centerDExp : DyadicInterval precision := ⟨1290109275795961219083538977138292162718810472007, 1290109275795961219083538977138292164917833727560⟩
def centerDLog : DyadicInterval precision := ⟨924724386421826679470683559697340152094656101669, 924724386421826679470683559697340154293679357222⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1290109275795961219083538977138292163268566285895, scale precision, 1290109275795961219083538977138292164368077913672, scale precision,
    0, 128, 0, 128, ⟨-182304062199163918550106343409347325987867795357, -182304062199163918550106343409347325987865698204⟩, ⟨-182304062199163918550106343409347324742284902180, -182304062199163918550106343409347324742282805027⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨91788061675318353547613482588790824723680618640, 91788061675318353547613482588790824723680618641⟩
def centerCExp : DyadicInterval precision := ⟨1288986879578861633638027890388778894374181342090, 1288986879578861633638027890388778896573204597643⟩
def centerCLog : DyadicInterval precision := ⟨924128110780996160607417679005101766176754985837, 924128110780996160607417679005101768375778241390⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1288986879578861633638027890388778894923937155978, scale precision, 1288986879578861633638027890388778896023448783755, scale precision,
    0, 128, 0, 128, ⟨-183576123350636707095226965177581650070696033361, -183576123350636707095226965177581650070693936208⟩, ⟨-183576123350636707095226965177581648824028538355, -183576123350636707095226965177581648824026441202⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨183774783948819465474550779147620767677048104908, 183774783948819465474550779147620767677048104909⟩
def centerBExp : DyadicInterval precision := ⟨1136526642042149742250331323084048518896921023046, 1136526642042149742250331323084048521095944278599⟩
def centerBLog : DyadicInterval precision := ⟨840784905459560157136219384057041625482494978223, 840784905459560157136219384057041627681518233776⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1136526642042149742250331323084048519446676836934, scale precision, 1136526642042149742250331323084048520546188464711, scale precision,
    0, 128, 0, 128, ⟨-367549567897638930949101558295241536061048589235, -367549567897638930949101558295241536061046492082⟩, ⟨-367549567897638930949101558295241534647145927549, -367549567897638930949101558295241534647143830396⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨87177733031446937316788780256552774640368349422, 95127887983717436574352739463518235552733806995⟩
def wholeDExp : DyadicInterval precision := ⟨1283109131137421329953040259475754029680231733945, 1297144843488804201115883427901752815058870064878⟩
def wholeDLog : DyadicInterval precision := ⟨921001564088758741914731412563984559982408490529, 928456516721811008488201258314450140012001202708⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1283109131137421329953040259475754030229987547833, scale precision, 1297144843488804201115883427901752814509114250990, scale precision,
    0, 128, 0, 128, ⟨-190255775967434873148705478927036471731657817199, -190255775967434873148705478927036471731655720046⟩, ⟨-174355466062893874633577560513105548661324251571, -174355466062893874633577560513105548661322154418⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨87177733031446937316788780256552774640368349422, 96400502557886147002287983842112166506463198113⟩
def wholeCExp : DyadicInterval precision := ⟨1280876520102510064005287526572790115465191378476, 1297144843488804201115883427901752815058870064878⟩
def wholeCLog : DyadicInterval precision := ⟨919812217834489480032069487694193338787674377978, 928456516721811008488201258314450140012001202708⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1280876520102510064005287526572790116014947192364, scale precision, 1297144843488804201115883427901752814509114250990, scale precision,
    0, 128, 0, 128, ⟨-192801005115772294004575967684224333640208068282, -192801005115772294004575967684224333640205971129⟩, ⟨-174355466062893874633577560513105548661324251571, -174355466062893874633577560513105548661322154418⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨175078047236001450214222015517899197240067851934, 192486267482474676822962020884762084766255799608⟩
def wholeBExp : DyadicInterval precision := ⟨1123058232017299231234434758861740122068523594703, 1150133363234016597447468800724884781224161812840⟩
def wholeBLog : DyadicInterval precision := ⟨833188643880544430188545489483369906970376730420, 848419291580521843596292009329506550515087162287⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1123058232017299231234434758861740122618279408591, scale precision, 1150133363234016597447468800724884780674405998952, scale precision,
    0, 128, 0, 128, ⟨-384972534964949353645924041769524170247942176933, -384972534964949353645924041769524170247940079780⟩, ⟨-350156094472002900428444031035798393781549051388, -350156094472002900428444031035798393781546954235⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0021StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0022StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨83204925566128923103386656610767262849242461462, 83204925566128923103386656610767262849242461463⟩
def centerDExp : DyadicInterval precision := ⟨1304216119040613274645831231453751221172217307273, 1304216119040613274645831231453751223371240562826⟩
def centerDLog : DyadicInterval precision := ⟨932198010221342921271619522959115051456047294407, 932198010221342921271619522959115053655070549960⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1304216119040613274645831231453751221721973121161, scale precision, 1304216119040613274645831231453751222821484748938, scale precision,
    0, 128, 0, 128, ⟨-166409851132257846206773313221534526314541094883, -166409851132257846206773313221534526314538997730⟩, ⟨-166409851132257846206773313221534525082430848122, -166409851132257846206773313221534525082428750969⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨83840477401825880878169979660152749767472045879, 83840477401825880878169979660152749767472045880⟩
def centerCExp : DyadicInterval precision := ⟨1303082303551182435034660341949611080697122590103, 1303082303551182435034660341949611082896145845656⟩
def centerCLog : DyadicInterval precision := ⟨931598739762635647687850170938252582397349444661, 931598739762635647687850170938252584596372700214⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1303082303551182435034660341949611081246878403991, scale precision, 1303082303551182435034660341949611082346390031768, scale precision,
    0, 128, 0, 128, ⟨-167680954803651761756339959320305500151536294969, -167680954803651761756339959320305500151534197816⟩, ⟨-167680954803651761756339959320305498918353985700, -167680954803651761756339959320305498918351888547⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨167680817176903094497100275096363859604686988375, 167680817176903094497100275096363859604686988376⟩
def centerBExp : DyadicInterval precision := ⟨1161835037508704920972156174832617139686325084795, 1161835037508704920972156174832617141885348340348⟩
def centerBLog : DyadicInterval precision := ⟨854953059346986941317017404658810989773707707048, 854953059346986941317017404658810991972730962601⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1161835037508704920972156174832617140236080898683, scale precision, 1161835037508704920972156174832617141335592526460, scale precision,
    0, 128, 0, 128, ⟨-335361634353806188994200550192727719900926748413, -335361634353806188994200550192727719900924651260⟩, ⟨-335361634353806188994200550192727718517823302242, -335361634353806188994200550192727718517821205089⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096871869275, 87177733031446937316788780256552774640368349423⟩
def wholeDExp : DyadicInterval precision := ⟨1297144843488804201115883427901752812859846809325, 1311323390486212533981803318339124544384464892381⟩
def wholeDLog : DyadicInterval precision := ⟨928456516721811008488201258314450137812977947155, 935948922676490622602857379124864312093157411787⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1297144843488804201115883427901752813409602623213, scale precision, 1311323390486212533981803318339124543834709078493, scale precision,
    0, 128, 0, 128, ⟨-174355466062893874633577560513105549900151243272, -174355466062893874633577560513105549900149146119⟩, ⟨-158467081097196404323724233909852887581028634911, -158467081097196404323724233909852887581026537758⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096871869275, 88449342971355302470485152083509965479350191859⟩
def wholeCExp : DyadicInterval precision := ⟨1294889590511360688191276887190755562697257383357, 1311323390486212533981803318339124544384464892381⟩
def wholeCLog : DyadicInterval precision := ⟨927261218964308206823929778080634459182431623851, 935948922676490622602857379124864312093157411787⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1294889590511360688191276887190755563247013197245, scale precision, 1311323390486212533981803318339124543834709078493, scale precision,
    0, 128, 0, 128, ⟨-176898685942710604940970304167019931579193733737, -176898685942710604940970304167019931579191636584⟩, ⟨-158467081097196404323724233909852887581028634911, -158467081097196404323724233909852887581026537758⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨159009523631476834293416684122073812609720086984, 176365549723902348143424292968104815592821027152⟩
def wholeBExp : DyadicInterval precision := ⟨1148108738982243371695955789645787235187714244801, 1175703819620526499056916402241341507477966942436⟩
def wholeBLog : DyadicInterval precision := ⟨847285848658893358182028839792376452210620336745, 862659221266056220624571274243273532289421478776⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1148108738982243371695955789645787235737470058689, scale precision, 1175703819620526499056916402241341506928211128548, scale precision,
    0, 128, 0, 128, ⟨-352731099447804696286848585936209631885462723486, -352731099447804696286848585936209631885460626333⟩, ⟨-318019047262953668586833368244147624536047149377, -318019047262953668586833368244147624536045052224⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0022StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0023StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨75898626579489180817964566504327908828195201183, 75898626579489180817964566504327908828195201184⟩
def centerCExp : DyadicInterval precision := ⟨1317321529129083856165674421815972834051728098327, 1317321529129083856165674421815972836250751353880⟩
def centerCLog : DyadicInterval precision := ⟨939107009266901255643844175276290453998031162549, 939107009266901255643844175276290456197054418102⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1317321529129083856165674421815972834601483912215, scale precision, 1317321529129083856165674421815972835700995539992, scale precision,
    0, 128, 0, 128, ⟨-151797253158978361635929133008655818266317732694, -151797253158978361635929133008655818266315635541⟩, ⟨-151797253158978361635929133008655817046465169195, -151797253158978361635929133008655817046463072042⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨151632939129008056697517373665649318183483033498, 151632939129008056697517373665649318183483033499⟩
def centerBExp : DyadicInterval precision := ⟨1187632098471748154820948330413552637007407916362, 1187632098471748154820948330413552639206431171915⟩
def centerBLog : DyadicInterval precision := ⟨869254798289420289309708762878379527657599146636, 869254798289420289309708762878379529856622402189⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1187632098471748154820948330413552637557163730250, scale precision, 1187632098471748154820948330413552638656675358027, scale precision,
    0, 128, 0, 128, ⟨-303265878258016113395034747331298637043497350117, -303265878258016113395034747331298637043495252964⟩, ⟨-303265878258016113395034747331298635690436881031, -303265878258016113395034747331298635690434783878⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159908214514, 80504233142141611642933172006386671113699818849⟩
def wholeCExp : DyadicInterval precision := ⟨1309045129588817403044812046386576903929543094186, 1325647089475606555897615027767584925570467038145⟩
def wholeCLog : DyadicInterval precision := ⟨934747602489940959407298357260346040404373450625, 943479230106772831249544853595316780957610367733⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1309045129588817403044812046386576904479298908074, scale precision, 1325647089475606555897615027767584925020711224257, scale precision,
    0, 128, 0, 128, ⟨-161008466284283223285866344012773342841183209099, -161008466284283223285866344012773342841181111946⟩, ⟨-142589531024244066774107942510231079713721761400, -142589531024244066774107942510231079713719664247⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 160293339111948018245674211080042528839685011783⟩
def wholeBExp : DyadicInterval precision := ⟨1173640104298104188087122023740267535234930412036, 1201770939647839765988959733979548166667559706770⟩
def wholeBLog : DyadicInterval precision := ⟨861515091957746564471801711065111145687970794257, 877034319321159546816789449956018118197948476500⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1173640104298104188087122023740267535784686225924, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-320586678223896036491348422160085058363966817624, -320586678223896036491348422160085058363964720471⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0023StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0024StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨67961964551488262188828254855795778736014617692, 67961964551488262188828254855795778736014617693⟩
def centerCExp : DyadicInterval precision := ⟨1331706895592994339422554366030765224790648439236, 1331706895592994339422554366030765226989671694789⟩
def centerCLog : DyadicInterval precision := ⟨946653370983950457516442070999313412297977171613, 946653370983950457516442070999313414497000427166⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1331706895592994339422554366030765225340404253124, scale precision, 1331706895592994339422554366030765226439915880901, scale precision,
    0, 128, 0, 128, ⟨-135923929102976524377656509711591558075368019005, -135923929102976524377656509711591558075365921852⟩, ⟨-135923929102976524377656509711591556868692548916, -135923929102976524377656509711591556868690451763⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨135626692008785377142630029624202994261554904099, 135626692008785377142630029624202994261554904100⟩
def centerBExp : DyadicInterval precision := ⟨1213932790367752907470564320597495059540259597038, 1213932790367752907470564320597495061739282852591⟩
def centerBLog : DyadicInterval precision := ⟨883693083502000011870295132974730813598893353803, 883693083502000011870295132974730815797916609356⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1213932790367752907470564320597495060090015410926, scale precision, 1213932790367752907470564320597495061189527038703, scale precision,
    0, 128, 0, 128, ⟨-271253384017570754285260059248405989184983596771, -271253384017570754285260059248405989184981499618⟩, ⟨-271253384017570754285260059248405987861238116781, -271253384017570754285260059248405987861236019628⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨63360863746962342702697993485127651995684952633, 72564627903854707163651962613527732691556708916⟩
def wholeCExp : DyadicInterval precision := ⟨1323345446381383724377914098789029238266403564725, 1340118310385255731396483422015350660826016558551⟩
def wholeCLog : DyadicInterval precision := ⟨942271815221164981759971436449019771296366796919, 951047895604627342379828868169897142552033311172⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1323345446381383724377914098789029238816159378613, scale precision, 1340118310385255731396483422015350660276260744663, scale precision,
    0, 128, 0, 128, ⟨-145129255807709414327303925227055465990264341240, -145129255807709414327303925227055465990262244087⟩, ⟨-126721727493924685405395986970255303391820141124, -126721727493924685405395986970255303391818043971⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 144265163383122164482546534975845208150899296287⟩
def wholeBExp : DyadicInterval precision := ⟨1199666936116860123325924274283438621574934428979, 1228350054579566692017908102915209767793957734212⟩
def wholeBLog : DyadicInterval precision := ⟨875879266733045019226793172335071307114073904507, 891547615580027951955449639520829064234092557127⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1199666936116860123325924274283438622124690242867, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-288530326766244328965093069951690416971543049041, -288530326766244328965093069951690416971540951888⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0024StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0025StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨248701695666007263736444087294378506122795166187, 248701695666007263736444087294378506122795166188⟩
def centerCExp : DyadicInterval precision := ⟨1039902766188338484594708114472613156400684641510, 1039902766188338484594708114472613158599707897063⟩
def centerCLog : DyadicInterval precision := ⟨785393309873193213427749859756639256284439874973, 785393309873193213427749859756639258483463130526⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1039902766188338484594708114472613156950440455398, scale precision, 1039902766188338484594708114472613158049952083175, scale precision,
    0, 128, 0, 128, ⟨-497403391332014527472888174588757013018229985497, -497403391332014527472888174588757013018227888344⟩, ⟨-497403391332014527472888174588757011472952776407, -497403391332014527472888174588757011472950679254⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨513476891620287433729744816122965384439477635574, 513476891620287433729744816122965384439477635575⟩
def centerBExp : DyadicInterval precision := ⟨723824827532911875227338360353220504128867257720, 723824827532911875227338360353220506327890513273⟩
def centerBLog : DyadicInterval precision := ⟨587963282790660940513969362008894092405499604698, 587963282790660940513969362008894094604522860251⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨723824827532911875227338360353220504678623071608, scale precision, 723824827532911875227338360353220505778134699385, scale precision,
    0, 128, 0, 128, ⟨-1026953783240574867459489632245930769988988735813, -1026953783240574867459489632245930769988986638660⟩, ⟨-1026953783240574867459489632245930767768923903638, -1026953783240574867459489632245930767768921806485⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542248751090, 257544697616875877678682630457661034482241905781⟩
def wholeCExp : DyadicInterval precision := ⟨1027394473369725711169456262584538343569053044456, 1052534436295863801714746685306812133363569214732⟩
def wholeCLog : DyadicInterval precision := ⟨778066725565575372226855198307689506486498465002, 792755074273575496363197836249071888393767558659⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1027394473369725711169456262584538344118808858344, scale precision, 1052534436295863801714746685306812132813813400844, scale precision,
    0, 128, 0, 128, ⟨-515089395233751755357365260915322069746530163043, -515089395233751755357365260915322069746528065890⟩, ⟨-479757527657573259465926780178734588321132532104, -479757527657573259465926780178734588321130434951⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨494828875109284674194281948410566590218630888609, 532282228172866116854382691727110279060616762141⟩
def wholeBExp : DyadicInterval precision := ⟨705435360866505781316672671624606262796841225806, 742533801492811413004049823802046285637355489138⟩
def wholeBLog : DyadicInterval precision := ⟨575612745737157315624533178384052510356302283242, 600422206098217740957049834384989022236361477122⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨705435360866505781316672671624606263346597039694, scale precision, 742533801492811413004049823802046285087599675250, scale precision,
    0, 128, 0, 128, ⟨-1064564456345732233708765383454220559260203593553, -1064564456345732233708765383454220559260201496400⟩, ⟨-989657750218569348388563896821133179355198924442, -989657750218569348388563896821133179355196827289⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0025StableWitnesses

end


