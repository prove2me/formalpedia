-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0368StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0368StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:56:21.674525+00:00
-- url     : https://prove2.me/theorems/a5e3f97b-a164-4d3b-96e0-41f78317f36c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0368StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0369StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0368StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0369StableWitnesses, GeneralCK.Certificates.E8TAxisProd0370StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0368StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0369StableWitnesses, GeneralCK.Certificates.E8TAxisProd0370StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0368StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0369StableWitnesses, GeneralCK.Certificates.E8TAxisProd0370StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0368StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0369StableWitnesses, GeneralCK/Certificates/E8TAxisProd0370StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0368StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0368StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303356852, 889351442612263296687940979624415955523303356853⟩
def centerDExp : DyadicInterval precision := ⟨432759351678313928226043309926168445711221586154, 432759351678313928226043309926168447910244841707⟩
def centerDLog : DyadicInterval precision := ⟨379061432685197727184727484874290046165241739981, 379061432685197727184727484874290048364264995534⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446260977400042, scale precision, 432759351678313928226043309926168447360489027819, scale precision,
    1, 128, 1, 128, ⟨-1778702885224526593375881959248831912903226270963, -1778702885224526593375881959248831912903224173810⟩, ⟨-1778702885224526593375881959248831909189989253603, -1778702885224526593375881959248831909189987156450⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨890871900327442887789058569502401235544797306978, 890871900327442887789058569502401235544797306979⟩
def centerCExp : DyadicInterval precision := ⟨431859854589148670534968772441948673295356648920, 431859854589148670534968772441948675494379904473⟩
def centerCLog : DyadicInterval precision := ⟨378367268206069951923232593713204488620416850020, 378367268206069951923232593713204490819440105573⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨431859854589148670534968772441948673845112462808, scale precision, 431859854589148670534968772441948674944624090585, scale precision,
    1, 128, 1, 128, ⟨-1781743800654885775578117139004802472950081219578, -1781743800654885775578117139004802472950079122425⟩, ⟨-1781743800654885775578117139004802469229110105491, -1781743800654885775578117139004802469229108008338⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2272814285998317554338008206454187605894024786224, 2272814285998317554338008206454187605894024786225⟩
def centerBExp : DyadicInterval precision := ⟨65168382671123856359139875709188565359982715259, 65168382671123856359139875709188567559005970812⟩
def centerBLog : DyadicInterval precision := ⟨63757249073972306918894963171149630794210853712, 63757249073972306918894963171149632993234109265⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨65168382671123856359139875709188565909738529147, scale precision, 65168382671123856359139875709188567009250156924, scale precision,
    4, 128, 4, 128, ⟨-4545628571996635108676016412908375224117173873706, -4545628571996635108676016412908375224117171776553⟩, ⟨-4545628571996635108676016412908375199458927368342, -4545628571996635108676016412908375199458925271189⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 895603670620266646532188138393358736598408063638⟩
def wholeDExp : DyadicInterval precision := ⟨429072502312048699316189665111836193246265566837, 436466074505762269046786189274013978256547303798⟩
def wholeDLog : DyadicInterval precision := ⟨376214102269711135965559641860188009991436493933, 381918529993447746751868483809797876669420495502⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836193796021380725, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1791207341240533293064376276786717475069388868982, -1791207341240533293064376276786717475069386771829⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨884418040819471962986432007479179994034843217290, 897346948514818745380395337607593298799534862490⟩
def wholeCExp : DyadicInterval precision := ⟨428050127661926778048988905758272835847209979839, 435690855432030702140972411073033894512925421028⟩
def wholeCLog : DyadicInterval precision := ⟨375423545394492010756300279718552279104909974474, 381321462201720095726327811723155518995770213292⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨428050127661926778048988905758272836396965793727, scale precision, 435690855432030702140972411073033893963169607140, scale precision,
    1, 128, 1, 128, ⟨-1794693897029637490760790675215186599476115003210, -1794693897029637490760790675215186599476112906057⟩, ⟨-1768836081638943925972864014958359986225561052427, -1768836081638943925972864014958359986225558955274⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2254247680487392150548432768341741895440974344367, 2291406374594804801699055867006919163856665671490⟩
def wholeBExp : DyadicInterval precision := ⟨63531254170697087532571850441743682609390262012, 66845367016060047209118565490127959430260735232⟩
def wholeBLog : DyadicInterval precision := ⟨62189163134540406258395431277714911526371133506, 65361767538216464821377468356758720041837598385⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨63531254170697087532571850441743683159146075900, scale precision, 66845367016060047209118565490127958880504921344, scale precision,
    4, 128, 4, 128, ⟨-4582812749189609603398111734013838340360163193469, -4582812749189609603398111734013838340360161096316⟩, ⟨-4508495360974784301096865536683483778862133585539, -4508495360974784301096865536683483778862131488386⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0368StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0369StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0369StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨878417065175234535766228633951194257038020812507, 878417065175234535766228633951194257038020812508⟩
def centerCExp : DyadicInterval precision := ⟨439283509872861808159205444126111155684873824809, 439283509872861808159205444126111157883897080362⟩
def centerCLog : DyadicInterval precision := ⟨384086445259274917243641249515212494587316235192, 384086445259274917243641249515212496786339490745⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨439283509872861808159205444126111156234629638697, scale precision, 439283509872861808159205444126111157334141266474, scale precision,
    1, 128, 1, 128, ⟨-1756834130350469071532457267902388515905087024386, -1756834130350469071532457267902388515905084927233⟩, ⟨-1756834130350469071532457267902388512246998322797, -1756834130350469071532457267902388512246996225644⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2236340916265819381484003779994606485119483948575, 2236340916265819381484003779994606485119483948576⟩
def centerBExp : DyadicInterval precision := ⟨68503621160313902382799566428431305818634381036, 68503621160313902382799566428431308017657636589⟩
def centerBLog : DyadicInterval precision := ⟨66946634928335054129373721798457691853772283694, 66946634928335054129373721798457694052795539247⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨68503621160313902382799566428431306368390194924, scale precision, 68503621160313902382799566428431307467901822701, scale precision,
    4, 128, 4, 128, ⟨-4472681832531638762968007559989212981967823691232, -4472681832531638762968007559989212981967821594079⟩, ⟨-4472681832531638762968007559989212958510114200228, -4472681832531638762968007559989212958510112103075⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨872003870965295638521799561608577658915321878149, 884851251413478951659207837173796053828323154671⟩
def wholeCExp : DyadicInterval precision := ⟨435432641614873493398314282370211385693913871440, 443155703777952795787930073976711170417427960058⟩
def wholeCLog : DyadicInterval precision := ⟨381122533731562838756189208815731355980242082578, 387060722076176269483932963550171797319285873795⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨435432641614873493398314282370211386243669685328, scale precision, 443155703777952795787930073976711169867672146170, scale precision,
    1, 128, 1, 128, ⟨-1769702502826957903318415674347592109501867365197, -1769702502826957903318415674347592109501865268044⟩, ⟨-1744007741930591277043599123217155316017582228269, -1744007741930591277043599123217155316017580131116⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2217827204886946277479732780045701216393150824226, 2254882005264758054897921034005770686504743864307⟩
def wholeBExp : DyadicInterval precision := ⟨66787367389502829361667521198510841985060393797, 70261345592619548552722966815155624711296415577⟩
def wholeBLog : DyadicInterval precision := ⟨65306303590964209612974337707924174193109045290, 68624696241573435016080378020054360263848575492⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66787367389502829361667521198510842534816207685, scale precision, 70261345592619548552722966815155624161540601689, scale precision,
    4, 128, 4, 128, ⟨-4509764010529516109795842068011541385039743203077, -4509764010529516109795842068011541385039741105924⟩, ⟨-4435654409773892554959465560091402421350868101320, -4435654409773892554959465560091402421350866004167⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0369StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0370StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0370StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303356852, 889351442612263296687940979624415955523303356853⟩
def centerDExp : DyadicInterval precision := ⟨432759351678313928226043309926168445711221586154, 432759351678313928226043309926168447910244841707⟩
def centerDLog : DyadicInterval precision := ⟨379061432685197727184727484874290046165241739981, 379061432685197727184727484874290048364264995534⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446260977400042, scale precision, 432759351678313928226043309926168447360489027819, scale precision,
    1, 128, 1, 128, ⟨-1778702885224526593375881959248831912903226270963, -1778702885224526593375881959248831912903224173810⟩, ⟨-1778702885224526593375881959248831909189989253603, -1778702885224526593375881959248831909189987156450⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨890437364192039962805983563859612299580840821211, 890437364192039962805983563859612299580840821212⟩
def centerCExp : DyadicInterval precision := ⟨432116733560092517811497599057442467700177963593, 432116733560092517811497599057442469899201219146⟩
def centerCLog : DyadicInterval precision := ⟨378565541791252124018640680701806441304690630517, 378565541791252124018640680701806443503713886070⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨432116733560092517811497599057442468249933777481, scale precision, 432116733560092517811497599057442469349445405258, scale precision,
    1, 128, 1, 128, ⟨-1780874728384079925611967127719224601021062251497, -1780874728384079925611967127719224601021060154344⟩, ⟨-1780874728384079925611967127719224597302303130504, -1780874728384079925611967127719224597302301033351⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2272179104174789024264049982992992854235275445847, 2272179104174789024264049982992992854235275445848⟩
def centerBExp : DyadicInterval precision := ⟨65225052833380020844198613912144430201881165808, 65225052833380020844198613912144432400904421361⟩
def centerBLog : DyadicInterval precision := ⟨63811499171680829732743768238255681372826393624, 63811499171680829732743768238255683571849649177⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨65225052833380020844198613912144430751636979696, scale precision, 65225052833380020844198613912144431851148607473, scale precision,
    4, 128, 4, 128, ⟨-4544358208349578048528099965985985720788963152329, -4544358208349578048528099965985985720788961055176⟩, ⟨-4544358208349578048528099965985985696152140728199, -4544358208349578048528099965985985696152138631046⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 895603670620266646532188138393358736598408063638⟩
def wholeDExp : DyadicInterval precision := ⟨429072502312048699316189665111836193246265566837, 436466074505762269046786189274013978256547303798⟩
def wholeDLog : DyadicInterval precision := ⟨376214102269711135965559641860188009991436493933, 381918529993447746751868483809797876669420495502⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836193796021380725, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1791207341240533293064376276786717475069388868982, -1791207341240533293064376276786717475069386771829⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨883984925531161516812957497582224991376607169133, 896910984800584647324265506680046400576443277800⟩
def wholeCExp : DyadicInterval precision := ⟨428305577257885294553077076892280643548247580789, 435949165514127363684919163029145907942102845596⟩
def wholeCLog : DyadicInterval precision := ⟨375621113291764766884334952502888279325268106669, 381520437746506309354292351379883669689940375098⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨428305577257885294553077076892280644098003394677, scale precision, 435949165514127363684919163029145907392347031708, scale precision,
    1, 128, 1, 128, ⟨-1793821969601169294648531013360092803028812328936, -1793821969601169294648531013360092803028810231783⟩, ⟨-1767969851062323033625914995164449980910181644175, -1767969851062323033625914995164449980910179547022⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2253613386607212014265448009956055049263997468083, 2290770337055073476941082054148223152539229214506⟩
def wholeBExp : DyadicInterval precision := ⟨63586575153068648648273232006831231649086773871, 66903414182003646647157117170098191311725196863⟩
def wholeBLog : DyadicInterval precision := ⟨62242178541842108441643395601396753620717635627, 65417274839122047986417651531529793243449999557⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨63586575153068648648273232006831232198842587759, scale precision, 66903414182003646647157117170098190761969382975, scale precision,
    4, 128, 4, 128, ⟨-4581540674110146953882164108296446317714287405034, -4581540674110146953882164108296446317714285307881⟩, ⟨-4507226773214424028530896019912110086518608542351, -4507226773214424028530896019912110086518606445198⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0370StableWitnesses

end


