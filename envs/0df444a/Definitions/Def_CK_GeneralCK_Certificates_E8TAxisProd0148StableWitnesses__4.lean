-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0148StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0148StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:04:11.428309+00:00
-- url     : https://prove2.me/theorems/72389526-be15-4afd-8ce6-d1a37c263cec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0148StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0149StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0148StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0149StableWitnesses, GeneralCK.Certificates.E8TAxisProd0150StableWitnesses, GeneralCK.Certificates.E8TAxisProd0151StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0148StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0149StableWitnesses, GeneralCK.Certificates.E8TAxisProd0150StableWitnesses, GeneralCK.Certificates.E8TAxisProd0151StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0148StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0149StableWitnesses, GeneralCK.Certificates.E8TAxisProd0150StableWitnesses, GeneralCK.Certificates.E8TAxisProd0151StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0148StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0149StableWitnesses, GeneralCK/Certificates/E8TAxisProd0150StableWitnesses, GeneralCK/Certificates/E8TAxisProd0151StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0148StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0148StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨450610413097730743244362126978975884668402912586, 450610413097730743244362126978975884668402912587⟩
def centerDExp : DyadicInterval precision := ⟨788852527298295547523937279792077535251368933655, 788852527298295547523937279792077537450392189208⟩
def centerDLog : DyadicInterval precision := ⟨630817990789549768708034337561797068071575978800, 630817990789549768708034337561797070270599234353⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨788852527298295547523937279792077535801124747543, scale precision, 788852527298295547523937279792077536900636375320, scale precision,
    0, 128, 0, 128, ⟨-901220826195461486488724253957951770355335678976, -901220826195461486488724253957951770355333581823⟩, ⟨-901220826195461486488724253957951768318278068520, -901220826195461486488724253957951768318275971367⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨451662028835744665701265102428915605933039960633, 451662028835744665701265102428915605933039960634⟩
def centerCExp : DyadicInterval precision := ⟨787718114465295719529385899660334760692655814272, 787718114465295719529385899660334762891679069825⟩
def centerCLog : DyadicInterval precision := ⟨630081056013608504665051467404572245062385973284, 630081056013608504665051467404572247261409228837⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨787718114465295719529385899660334761242411628160, scale precision, 787718114465295719529385899660334762341923255937, scale precision,
    0, 128, 0, 128, ⟨-903324057671489331402530204857831212886076584234, -903324057671489331402530204857831212886074487081⟩, ⟨-903324057671489331402530204857831210846085355454, -903324057671489331402530204857831210846083258301⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨999771545878609141775103972464988602096985023666, 999771545878609141775103972464988602096985023667⟩
def centerBExp : DyadicInterval precision := ⟨372068063002705036812773377450998449827533510027, 372068063002705036812773377450998452026556765580⟩
def centerBLog : DyadicInterval precision := ⟨331469005175176301313551168184635740776393692352, 331469005175176301313551168184635742975416947905⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨372068063002705036812773377450998450377289323915, scale precision, 372068063002705036812773377450998451476800951692, scale precision,
    1, 128, 1, 128, ⟨-1999543091757218283550207944929977206353438951457, -1999543091757218283550207944929977206353436854304⟩, ⟨-1999543091757218283550207944929977202034503240362, -1999543091757218283550207944929977202034501143209⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨441864642833471825996809190961403572059602547859, 459387967798615484561738103898747303530785179430⟩
def wholeDExp : DyadicInterval precision := ⟨779433753649515438129873373659005447292625435663, 798350393094904597531547569261377275013063266071⟩
def wholeDLog : DyadicInterval precision := ⟨624688092853175616303270580088334958317423405482, 636973437495070745585836635514540158238274439736⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨779433753649515438129873373659005447842381249551, scale precision, 798350393094904597531547569261377274463307452183, scale precision,
    0, 128, 0, 128, ⟨-918775935597230969123476207797494608092408240415, -918775935597230969123476207797494608092406143262⟩, ⟨-883729285666943651993618381922807143112794637420, -883729285666943651993618381922807143112792540267⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨442563149837559596326653161341442316960877870587, 460795368920412028518162504643854518865778764228⟩
def wholeCExp : DyadicInterval precision := ⟨777934035523977631609093955857762633040195656609, 797587633904908293168880243258517547058018985319⟩
def wholeCLog : DyadicInterval precision := ⟨623709673634481061734914998481739642729657739711, 636480059183099424004489343384240020279304081011⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨777934035523977631609093955857762633589951470497, scale precision, 797587633904908293168880243258517546508263171431, scale precision,
    0, 128, 0, 128, ⟨-921590737840824057036325009287709038764382679643, -921590737840824057036325009287709038764380582490⟩, ⟨-885126299675119192653306322682884632914382818573, -885126299675119192653306322682884632914380721420⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨976507647850348019083025454535966685295704874315, 1023300595444368493082805525999753225833125465963⟩
def wholeBExp : DyadicInterval precision := ⟨360278860670989033437235515920200310327982829774, 384103640205485330181211104359839878774141728058⟩
def wholeBLog : DyadicInterval precision := ⟨322041728817379791829666077192241609877232340724, 341030974170464753292339171269603761751516175956⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨360278860670989033437235515920200310877738643662, scale precision, 384103640205485330181211104359839878224385914170, scale precision,
    2, 128, 1, 128, ⟨-2046601190888736986165611051999506453896382886973, -2046601190888736986165611051999506453896380789820⟩, ⟨-1953015295700696038166050909071933368499608122020, -1953015295700696038166050909071933368499606024867⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0148StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0149StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0149StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨433150018597706032584967812015361721770461165013, 433150018597706032584967812015361721770461165014⟩
def centerDExp : DyadicInterval precision := ⟨807928177963092639274651197161192176096781955567, 807928177963092639274651197161192178295805211120⟩
def centerDLog : DyadicInterval precision := ⟨643154536224866812603613452556143370937466856601, 643154536224866812603613452556143373136490112154⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨807928177963092639274651197161192176646537769455, scale precision, 807928177963092639274651197161192177746049397232, scale precision,
    0, 128, 0, 128, ⟨-866300037195412065169935624030723444535404130786, -866300037195412065169935624030723444535402033633⟩, ⟨-866300037195412065169935624030723442546442626421, -866300037195412065169935624030723442546440529268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨434194150064961422844578237149037849046270103910, 434194150064961422844578237149037849046270103911⟩
def centerCExp : DyadicInterval precision := ⟨806774596162822152067517242016890889332925323018, 806774596162822152067517242016890891531948578571⟩
def centerCLog : DyadicInterval precision := ⟨642411446342849771500350883774395176172113417527, 642411446342849771500350883774395178371136673080⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨806774596162822152067517242016890889882681136906, scale precision, 806774596162822152067517242016890890982192764683, scale precision,
    0, 128, 0, 128, ⟨-868388300129922845689156474298075699088443985551, -868388300129922845689156474298075699088441888398⟩, ⟨-868388300129922845689156474298075697096638527244, -868388300129922845689156474298075697096636430091⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨954403230523630223636654318549428035106916804113, 954403230523630223636654318549428035106916804114⟩
def centerBExp : DyadicInterval precision := ⟨395899869587171583251888818915598393776476661548, 395899869587171583251888818915598395975499917101⟩
def centerBLog : DyadicInterval precision := ⟨350342470409610186492926959572817826657036322006, 350342470409610186492926959572817828856059577559⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨395899869587171583251888818915598394326232475436, scale precision, 395899869587171583251888818915598395425744103213, scale precision,
    1, 128, 1, 128, ⟨-1908806461047260447273308637098856072243309996031, -1908806461047260447273308637098856072243307898878⟩, ⟨-1908806461047260447273308637098856068184359317578, -1908806461047260447273308637098856068184357220425⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 441864642833471825996809190961403572059602547860⟩
def wholeDExp : DyadicInterval precision := ⟨798350393094904597531547569261377272814040010518, 817586731060820878424464751762154419137555379748⟩
def wholeDLog : DyadicInterval precision := ⟨636973437495070745585836635514540156039251184183, 649361398245907818978439547465799274251803053932⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨798350393094904597531547569261377273363795824406, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-883729285666943651993618381922807145125617651173, -883729285666943651993618381922807145125615554020⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨425159525602201488178561662898618544842443951213, 443261856501343956161376671696244203127204536355⟩
def wholeCExp : DyadicInterval precision := ⟨796825385756610397812969454156942673726911654865, 816811054155852141841086964113502911671951597557⟩
def wholeCLog : DyadicInterval precision := ⟨635986844985079880340620748322159899561719625302, 648863898437265312597956440992327380678901642724⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨796825385756610397812969454156942674276667468753, scale precision, 816811054155852141841086964113502911122195783669, scale precision,
    0, 128, 0, 128, ⟨-886523713002687912322753343392488407262747752707, -886523713002687912322753343392488407262745655554⟩, ⟨-850319051204402976357123325797237088701223245156, -850319051204402976357123325797237088701221148003⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨931650845292789257750165249133704252352290883853, 977414995646579752871425924598711585174850155743⟩
def wholeBExp : DyadicInterval precision := ⟨383627008086480608895458465871208976566662371172, 408420365716217659689284988008205495049992741400⟩
def wholeBLog : DyadicInterval precision := ⟨340653489019411114531854089637731478358457212264, 360161201930874086265687859610653960796961822687⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨383627008086480608895458465871208977116418185060, scale precision, 408420365716217659689284988008205494500236927512, scale precision,
    1, 128, 1, 128, ⟨-1954829991293159505742851849197423172444102966816, -1954829991293159505742851849197423172444100869663⟩, ⟨-1863301690585578515500330498267408502737322881238, -1863301690585578515500330498267408502737320784085⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0149StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0150StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0150StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774887708, 415811666137855580659299169097621045230774887709⟩
def centerDExp : DyadicInterval precision := ⟨827326924127804017482711149170086570224978765524, 827326924127804017482711149170086572424002021077⟩
def centerDLog : DyadicInterval precision := ⟨655594142802634878792195049006890681368280371847, 655594142802634878792195049006890683567303627400⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨827326924127804017482711149170086570774734579412, scale precision, 827326924127804017482711149170086571874246207189, scale precision,
    0, 128, 0, 128, ⟨-831623332275711161318598338195242091432713491011, -831623332275711161318598338195242091432711393858⟩, ⟨-831623332275711161318598338195242089490388156978, -831623332275711161318598338195242089490386059825⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨416848618164844048394273024886443565284991686200, 416848618164844048394273024886443565284991686201⟩
def centerCExp : DyadicInterval precision := ⟨826153760980733771017534993974349242562734968900, 826153760980733771017534993974349244761758224453⟩
def centerCLog : DyadicInterval precision := ⟨654844842722954340394169212434355008331034307134, 654844842722954340394169212434355010530057562687⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨826153760980733771017534993974349243112490782788, scale precision, 826153760980733771017534993974349244212002410565, scale precision,
    0, 128, 0, 128, ⟨-833697236329688096788546049772887131542526168140, -833697236329688096788546049772887131542524070987⟩, ⟨-833697236329688096788546049772887129597442673812, -833697236329688096788546049772887129597440576659⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨910031867838125476792521977085541885982243811751, 910031867838125476792521977085541885982243811752⟩
def centerBExp : DyadicInterval precision := ⟨420683833153437731034410586928090770223231002504, 420683833153437731034410586928090772422254258057⟩
def centerBLog : DyadicInterval precision := ⟨369714841685197523003170777702770883427536411369, 369714841685197523003170777702770885626559666922⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨420683833153437731034410586928090770772986816392, scale precision, 420683833153437731034410586928090771872498444169, scale precision,
    1, 128, 1, 128, ⟨-1820063735676250953585043954171083773874400484253, -1820063735676250953585043954171083773874398387100⟩, ⟨-1820063735676250953585043954171083770054576859906, -1820063735676250953585043954171083770054574762753⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 424465904280623337412236094991656409259795096050⟩
def wholeDExp : DyadicInterval precision := ⟨817586731060820878424464751762154416938532124195, 837149651842014699656242248506338776332018800396⟩
def wholeDLog : DyadicInterval precision := ⟨649361398245907818978439547465799272052779798379, 661852897083560210399534374966476335226142823792⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨817586731060820878424464751762154417488287938083, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-848931808561246674824472189983312819502323703918, -848931808561246674824472189983312819502321606765⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨407875610928507622577018057544997525448495147745, 425853338453922988105921025000462397676821471069⟩
def wholeCExp : DyadicInterval precision := ⟨816035899282844599192681770600671260965702902819, 836360774879119121246522016681364387337084252487⟩
def wholeCLog : DyadicInterval precision := ⟨648366564209713227240650953399208860371951583755, 661351236451547867877716675701243492079641474613⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨816035899282844599192681770600671261515458716707, scale precision, 836360774879119121246522016681364386787328438599, scale precision,
    0, 128, 0, 128, ⟨-851706676907845976211842050000924796338244083475, -851706676907845976211842050000924796338241986322⟩, ⟨-815751221857015245154036115089995049936318574299, -815751221857015245154036115089995049936316477146⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨887777918117404525199500657508409260959899463986, 932538250269953775680376616181880825197150579199⟩
def wholeBExp : DyadicInterval precision := ⟨407924691568896865343428683474592036075413696360, 433692215660942257716924836353743910475567804082⟩
def wholeBLog : DyadicInterval precision := ⟨359773739454620754603506557408147122455584640716, 379780999125440289108059068466642841451341267819⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨407924691568896865343428683474592036625169510248, scale precision, 433692215660942257716924836353743909925811990194, scale precision,
    1, 128, 1, 128, ⟨-1865076500539907551360753232363761652363952582979, -1865076500539907551360753232363761652363950485826⟩, ⟨-1775555836234809050399001315016818520067175020150, -1775555836234809050399001315016818520067172922997⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0150StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0151StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0151StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292752073, 398590295572446657843406049747194007801292752074⟩
def centerDExp : DyadicInterval precision := ⟨847055832185589353041431034353733246155211165949, 847055832185589353041431034353733248354234421502⟩
def centerDLog : DyadicInterval precision := ⟨668137796188982437048462187236859676234037540057, 668137796188982437048462187236859678433060795610⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨847055832185589353041431034353733246704966979837, scale precision, 847055832185589353041431034353733247804478607614, scale precision,
    0, 128, 0, 128, ⟨-797180591144893315686812099494388016551129720247, -797180591144893315686812099494388016551127623094⟩, ⟨-797180591144893315686812099494388014654043385201, -797180591144893315686812099494388014654041288048⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨399620370667675382461426831138663831113248567362, 399620370667675382461426831138663831113248567363⟩
def centerCExp : DyadicInterval precision := ⟨845862653309242173295924916039070751612755213736, 845862653309242173295924916039070753811778469289⟩
def centerCLog : DyadicInterval precision := ⟨667382223191492655987061680563838882661768083398, 667382223191492655987061680563838884860791338951⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨845862653309242173295924916039070752162511027624, scale precision, 845862653309242173295924916039070753262022655401, scale precision,
    0, 128, 0, 128, ⟨-799240741335350764922853662277327663176379371444, -799240741335350764922853662277327663176377274291⟩, ⟨-799240741335350764922853662277327661276616995160, -799240741335350764922853662277327661276614898007⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨866630787983145416930003182432624605316573452006, 866630787983145416930003182432624605316573452007⟩
def centerBExp : DyadicInterval precision := ⟨446426158980636567110420055364772335963528282331, 446426158980636567110420055364772338162551537884⟩
def centerBLog : DyadicInterval precision := ⟨389568089982006785624196683358370108819225835433, 389568089982006785624196683358370111018249090986⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨446426158980636567110420055364772336513284096219, scale precision, 446426158980636567110420055364772337612795723996, scale precision,
    1, 128, 1, 128, ⟨-1733261575966290833860006364865249212432928287964, -1733261575966290833860006364865249212432926190811⟩, ⟨-1733261575966290833860006364865249208833367617215, -1733261575966290833860006364865249208833365520062⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407186672849656374487538180028229486749868035096⟩
def wholeDExp : DyadicInterval precision := ⟨837149651842014699656242248506338774132995544843, 857046406820575460675375243512252172179026178685⟩
def wholeDLog : DyadicInterval precision := ⟨661852897083560210399534374966476333027119568239, 674448983099953378325059509857368476506693482805⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨837149651842014699656242248506338774682751358731, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-814373345699312748975076360056458974459504611190, -814373345699312748975076360056458974459502514037⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨390706363676981650886126153257225525434129008563, 408564732469872611568202250363970390565957589812⟩
def wholeCExp : DyadicInterval precision := ⟨835572431524968186400871469418026143136316539721, 856244032549522621499608497599586134673041767268⟩
def wholeCLog : DyadicInterval precision := ⟨660849743071204938736063078205368166821127645142, 673943117253251576685034189064722456085793384554⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨835572431524968186400871469418026143686072353609, scale precision, 856244032549522621499608497599586134123285953380, scale precision,
    0, 128, 0, 128, ⟨-817129464939745223136404500727940782093495370614, -817129464939745223136404500727940782093493273461⟩, ⟨-781412727353963301772252306514451049929894543925, -781412727353963301772252306514451049929892446772⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨844860139281541704854309292623447308798632418102, 888645914209915849662997451096338762038134360288⟩
def wholeBExp : DyadicInterval precision := ⟨433177375779549308458726172553366254184349752644, 459926260723707810888944766332148444878022834806⟩
def wholeBLog : DyadicInterval precision := ⟨379383920193860483998336416513768193916943545023, 399872958015999257201378982219817426603655692784⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨433177375779549308458726172553366254734105566532, scale precision, 459926260723707810888944766332148444328267020918, scale precision,
    1, 128, 1, 128, ⟨-1777291828419831699325994902192677525931096606968, -1777291828419831699325994902192677525931094509815⟩, ⟨-1689720278563083409708618585246894615850314056317, -1689720278563083409708618585246894615850311959164⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0151StableWitnesses

end


