-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0040StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0040StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:07:49.045177+00:00
-- url     : https://prove2.me/theorems/5ff0afdc-41a8-4efb-b1cc-805a51f66da1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0040StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0041StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0040StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0041StableWitnesses, GeneralCK.Certificates.E8TAxisZero0042StableWitnesses, GeneralCK.Certificates.E8TAxisZero0043StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0040StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0041StableWitnesses, GeneralCK.Certificates.E8TAxisZero0042StableWitnesses, GeneralCK.Certificates.E8TAxisZero0043StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0040StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0041StableWitnesses, GeneralCK.Certificates.E8TAxisZero0042StableWitnesses, GeneralCK.Certificates.E8TAxisZero0043StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0040StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisZero0041StableWitnesses, GeneralCK/Certificates/E8TAxisZero0042StableWitnesses, GeneralCK/Certificates/E8TAxisZero0043StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0040StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0040StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨433498013550381786316156603640838092070050376933, 433498013550381786316156603640838092070050376934⟩
def centerCExp : DyadicInterval precision := ⟨807543521543534148310907090287518275204379204508, 807543521543534148310907090287518277403402460061⟩
def centerCLog : DyadicInterval precision := ⟨642906798387139203670701531451153536959925008351, 642906798387139203670701531451153539158948263904⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨807543521543534148310907090287518275754135018396, scale precision, 807543521543534148310907090287518276853646646173, scale precision,
    0, 128, 0, 128, ⟨-866996027100763572632313207281676185135056254675, -866996027100763572632313207281676185135054157522⟩, ⟨-866996027100763572632313207281676183145147350213, -866996027100763572632313207281676183145145253060⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨953506114970467960208142504054949999342044303635, 953506114970467960208142504054949999342044303636⟩
def centerBExp : DyadicInterval precision := ⟨396386199569820279015464607314873841686990788086, 396386199569820279015464607314873843886014043639⟩
def centerBLog : DyadicInterval precision := ⟨350725090444933319148515549577897415967209784040, 350725090444933319148515549577897418166233039593⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨396386199569820279015464607314873842236746601974, scale precision, 396386199569820279015464607314873843336258229751, scale precision,
    0, 128, 0, 128, ⟨-1907012229940935920416285008109900000711075012558, -1907012229940935920416285008109900000711072915405⟩, ⟨-1907012229940935920416285008109899996657104299137, -1907012229940935920416285008109899996657102201984⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 442563149837559596326653161341442316960877870588⟩
def wholeCExp : DyadicInterval precision := ⟨797587633904908293168880243258517544858995729766, 817586731060820878424464751762154419137555379748⟩
def wholeCLog : DyadicInterval precision := ⟨636480059183099424004489343384240018080280825458, 649361398245907818978439547465799274251803053932⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨797587633904908293168880243258517545408751543654, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-885126299675119192653306322682884634929130760931, -885126299675119192653306322682884634929128663778⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨930763834005472674647888532357987354044446598973, 976507647850348019083025454535966685295704874316⟩
def wholeBExp : DyadicInterval precision := ⟨384103640205485330181211104359839876575118472505, 408916421860518370173645006422216583320741674887⟩
def wholeBLog : DyadicInterval precision := ⟨341030974170464753292339171269603759552492920403, 360548860196855511595020065110482657972108447542⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨384103640205485330181211104359839877124874286393, scale precision, 408916421860518370173645006422216582770985860999, scale precision,
    0, 128, 0, 128, ⟨-1953015295700696038166050909071933372683213472391, -1953015295700696038166050909071933372683211375238⟩, ⟨-1861527668010945349295777064715974706124020792738, -1861527668010945349295777064715974706124018695585⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0040StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0041StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0041StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨416157269968306523760978026987772624878298387635, 416157269968306523760978026987772624878298387636⟩
def centerCExp : DyadicInterval precision := ⟨826935737770386406981033946968722248056736800242, 826935737770386406981033946968722250255760055795⟩
def centerCLog : DyadicInterval precision := ⟨655344334506073919704910602898604540136858712415, 655344334506073919704910602898604542335881967968⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨826935737770386406981033946968722248606492614130, scale precision, 826935737770386406981033946968722249706004241907, scale precision,
    0, 128, 0, 128, ⟨-832314539936613047521956053975545250728219904538, -832314539936613047521956053975545250728217807385⟩, ⟨-832314539936613047521956053975545248784975743156, -832314539936613047521956053975545248784973646003⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨909154433284861788270355878530965457776373467049, 909154433284861788270355878530965457776373467050⟩
def centerBExp : DyadicInterval precision := ⟨421189264305586285905852374902794404307692007511, 421189264305586285905852374902794406506715263064⟩
def centerBLog : DyadicInterval precision := ⟨370107252159193930863832073999224682689786801039, 370107252159193930863832073999224684888810056592⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨421189264305586285905852374902794404857447821399, scale precision, 421189264305586285905852374902794405956959449176, scale precision,
    0, 128, 0, 128, ⟨-1818308866569723576540711757061930917460367882378, -1818308866569723576540711757061930917460365785225⟩, ⟨-1818308866569723576540711757061930913645128082973, -1818308866569723576540711757061930913645125985820⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 425159525602201488178561662898618544842443951214⟩
def wholeCExp : DyadicInterval precision := ⟨816811054155852141841086964113502909472928342004, 837149651842014699656242248506338776332018800396⟩
def wholeCLog : DyadicInterval precision := ⟨648863898437265312597956440992327378479878387171, 661852897083560210399534374966476335226142823792⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨816811054155852141841086964113502910022684155892, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-850319051204402976357123325797237090668554656851, -850319051204402976357123325797237090668552559698⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨886910304202382396337043275171386421688004586342, 931650845292789257750165249133704252352290883854⟩
def wholeBExp : DyadicInterval precision := ⟨408420365716217659689284988008205492850969485847, 434207440352252752310386566426237243434270269263⟩
def wholeBLog : DyadicInterval precision := ⟨360161201930874086265687859610653958597938567134, 380178266873177601086795281052634175727260544110⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨408420365716217659689284988008205493400725299735, scale precision, 434207440352252752310386566426237242884514455375, scale precision,
    0, 128, 0, 128, ⟨-1863301690585578515500330498267408506671842751330, -1863301690585578515500330498267408506671840654177⟩, ⟨-1773820608404764792674086550342772841525583564641, -1773820608404764792674086550342772841525581467488⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0041StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0042StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0042StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨398933609101018627089783753162906041379850143151, 398933609101018627089783753162906041379850143152⟩
def centerCExp : DyadicInterval precision := ⟨846657970947122885737414221253538667448590331034, 846657970947122885737414221253538669647613586587⟩
def centerCLog : DyadicInterval precision := ⟨667885896476225290786642683037583339232974688593, 667885896476225290786642683037583341431997944146⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨846657970947122885737414221253538667998346144922, scale precision, 846657970947122885737414221253538669097857772699, scale precision,
    0, 128, 0, 128, ⟨-797867218202037254179567506325812083708690241501, -797867218202037254179567506325812083708688144348⟩, ⟨-797867218202037254179567506325812081810712428261, -797867218202037254179567506325812081810710331108⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨865772459350793830067481977756678238110679746870, 865772459350793830067481977756678238110679746871⟩
def centerBExp : DyadicInterval precision := ⟨446950832332606156508294772140717052185606542902, 446950832332606156508294772140717054384629798455⟩
def centerBLog : DyadicInterval precision := ⟨389969942478014590072358819515197379993751552734, 389969942478014590072358819515197382192774808287⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨446950832332606156508294772140717052735362356790, scale precision, 446950832332606156508294772140717053834873984567, scale precision,
    0, 128, 0, 128, ⟨-1731544918701587660134963955513356478019028124538, -1731544918701587660134963955513356478019026027385⟩, ⟨-1731544918701587660134963955513356474423692960100, -1731544918701587660134963955513356474423690862947⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407875610928507622577018057544997525448495147746⟩
def wholeCExp : DyadicInterval precision := ⟨836360774879119121246522016681364385138060996934, 857046406820575460675375243512252172179026178685⟩
def wholeCLog : DyadicInterval precision := ⟨661351236451547867877716675701243489880618219060, 674448983099953378325059509857368476506693482805⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨836360774879119121246522016681364385687816810822, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-815751221857015245154036115089995051857664113839, -815751221857015245154036115089995051857662016686⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨844011309874718822803123512312745035848509639053, 887777918117404525199500657508409260959899463987⟩
def wholeBExp : DyadicInterval precision := ⟨433692215660942257716924836353743908276544548529, 460460814710846265448342638323429499233232843805⟩
def wholeBLog : DyadicInterval precision := ⟨379780999125440289108059068466642839252318012266, 400279500917613519597980274111473277721473888491⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨433692215660942257716924836353743908826300362417, scale precision, 460460814710846265448342638323429498683477029917, scale precision,
    0, 128, 0, 128, ⟨-1775555836234809050399001315016818523772424932952, -1775555836234809050399001315016818523772422835799⟩, ⟨-1688022619749437645606247024625490069952096553668, -1688022619749437645606247024625490069952094456515⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0042StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0043StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0043StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨381480886315733598228818968652248949197699359262, 381480886315733598228818968652248949197699359263⟩
def centerDExp : DyadicInterval precision := ⟨867122341474961541277039570779760212192757729340, 867122341474961541277039570779760214391780984893⟩
def centerDLog : DyadicInterval precision := ⟨680786608648623470121619561851525432077092876199, 680786608648623470121619561851525434276116131752⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨867122341474961541277039570779760212742513543228, scale precision, 867122341474961541277039570779760213842025171005, scale precision,
    0, 128, 0, 128, ⟨-762961772631467196457637937304497899321992225512, -762961772631467196457637937304497899321990128359⟩, ⟨-762961772631467196457637937304497897468807308690, -762961772631467196457637937304497897468805211537⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨381822009557264254203882052411309874959161316549, 381822009557264254203882052411309874959161316550⟩
def centerCExp : DyadicInterval precision := ⟨866717652836025394340504941468182535862577879921, 866717652836025394340504941468182538061601135474⟩
def centerCLog : DyadicInterval precision := ⟨680532594040125069950577128065543917047883298834, 680532594040125069950577128065543919246906554387⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨866717652836025394340504941468182536412333693809, scale precision, 866717652836025394340504941468182537511845321586, scale precision,
    0, 128, 0, 128, ⟨-763644019114528508407764104822619750845348785526, -763644019114528508407764104822619750845346688373⟩, ⟨-763644019114528508407764104822619748991298577823, -763644019114528508407764104822619748991296480670⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨823329576640286839316704484669493368989246993347, 823329576640286839316704484669493368989246993348⟩
def centerBExp : DyadicInterval precision := ⟨473678959411155574919911230530261478283574963610, 473678959411155574919911230530261480482598219163⟩
def centerBLog : DyadicInterval precision := ⟨410296456732787647242525119497794168940280096376, 410296456732787647242525119497794171139303351929⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨473678959411155574919911230530261478833330777498, scale precision, 473678959411155574919911230530261479932842405275, scale precision,
    0, 128, 0, 128, ⟨-1646659153280573678633408969338986739674726219213, -1646659153280573678633408969338986739674724122060⟩, ⟨-1646659153280573678633408969338986736282263851330, -1646659153280573678633408969338986736282261754177⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨372966609392870424646531471060848444542040850580, 390021907983024779256146395473341757167804190698⟩
def wholeDExp : DyadicInterval precision := ⟨857046406820575460675375243512252169980002923132, 877284626339432933560204346302551152435952374342⟩
def wholeDLog : DyadicInterval precision := ⟨674448983099953378325059509857368474307670227252, 687150831490084437187371430673459277974101520863⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨857046406820575460675375243512252170529758737020, scale precision, 877284626339432933560204346302551151886196560454, scale precision,
    0, 128, 0, 128, ⟨-780043815966049558512292790946683515273095446757, -780043815966049558512292790946683515273093349604⟩, ⟨-745933218785740849293062942121696888168223747987, -745933218785740849293062942121696888168221650834⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨372966609392870424646531471060848444542040850580, 390706363676981650886126153257225525434129008564⟩
def wholeCExp : DyadicInterval precision := ⟨856244032549522621499608497599586132474018511715, 877284626339432933560204346302551152435952374342⟩
def wholeCLog : DyadicInterval precision := ⟨673943117253251576685034189064722453886770129001, 687150831490084437187371430673459277974101520863⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨856244032549522621499608497599586133023774325603, scale precision, 877284626339432933560204346302551151886196560454, scale precision,
    0, 128, 0, 128, ⟨-781412727353963301772252306514451051806623587485, -781412727353963301772252306514451051806621490332⟩, ⟨-745933218785740849293062942121696888168223747987, -745933218785740849293062942121696888168221650834⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨802034511325989184277795602978615452582503309185, 844860139281541704854309292623447308798632418103⟩
def wholeBExp : DyadicInterval precision := ⟨459926260723707810888944766332148442678999579253, 487685700168395757571706970810843595006431378285⟩
def wholeBLog : DyadicInterval precision := ⟨399872958015999257201378982219817424404632437231, 420836633988471038083924660832487717465912484113⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨459926260723707810888944766332148443228755393141, scale precision, 487685700168395757571706970810843594456675564397, scale precision,
    0, 128, 0, 128, ⟨-1689720278563083409708618585246894619344217713246, -1689720278563083409708618585246894619344215616093⟩, ⟨-1604069022651978368555591205957230903517493659765, -1604069022651978368555591205957230903517491562612⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0043StableWitnesses

end


