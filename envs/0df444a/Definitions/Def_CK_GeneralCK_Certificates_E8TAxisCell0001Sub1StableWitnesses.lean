-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Sub1StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisCell0001Sub1StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:47:03.259488+00:00
-- url     : https://prove2.me/theorems/50ed6409-8881-4855-8218-bccd5c97fc54
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCell0001Sub1StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨16620951598713310515991793134470960105966667927, 16620951598713310515991793134470960105966667928⟩
def centerDExp : DyadicInterval precision := ⟨1428634928244308711378823712010396600887434155037, 1428634928244308711378823712010396603086457410590⟩
def centerDLog : DyadicInterval precision := ⟨996509296687561598184276445757911818881532200755, 996509296687561598184276445757911821080555456308⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1428634928244308711378823712010396601437189968925, scale precision, 1428634928244308711378823712010396602536701596702, scale precision,
    0, 128, 0, 128, ⟨-33241903197426621031983586268941920774337701223, -33241903197426621031983586268941920774335604070⟩, ⟨-33241903197426621031983586268941919649531067638, -33241903197426621031983586268941919649528970485⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨20420548211204887704929367051507124926808008587, 20420548211204887704929367051507124926808008588⟩
def centerCExp : DyadicInterval precision := ⟨1421225906658576149906763925526343174248657825345, 1421225906658576149906763925526343176447681080898⟩
def centerCLog : DyadicInterval precision := ⟨992757847521803259027094313430325486751778068873, 992757847521803259027094313430325488950801324426⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1421225906658576149906763925526343174798413639233, scale precision, 1421225906658576149906763925526343175897925267010, scale precision,
    0, 128, 0, 128, ⟨-40841096422409775409858734103014250418952258675, -40841096422409775409858734103014250418950161522⟩, ⟨-40841096422409775409858734103014249288281872826, -40841096422409775409858734103014249288279775673⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨37048351445030086588231507537151102797380843185, 37048351445030086588231507537151102797380843186⟩
def centerBExp : DyadicInterval precision := ⟨1389251904980869037041849862281167635754058621644, 1389251904980869037041849862281167637953081877197⟩
def centerBLog : DyadicInterval precision := ⟨976456916362875742913614860948941752415143078588, 976456916362875742913614860948941754614166334141⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1389251904980869037041849862281167636303814435532, scale precision, 1389251904980869037041849862281167637403326063309, scale precision,
    0, 128, 0, 128, ⟨-74096702890060173176463015074302206173109267531, -74096702890060173176463015074302206173107170378⟩, ⟨-74096702890060173176463015074302205016416202364, -74096702890060173176463015074302205016414105211⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨16146021631622132505602154469507921559441792473, 17095885651040514825842973106213884464633028209⟩
def wholeDExp : DyadicInterval precision := ⟨1427706722737910795912950268245206059093886102271, 1429563729219877177794428923148060136729147575503⟩
def wholeDLog : DyadicInterval precision := ⟨996039840755618551298709894112357433764303697906, 996978902895462305330196666434672379232603104095⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1427706722737910795912950268245206059643641916159, scale precision, 1429563729219877177794428923148060136179391761615, scale precision,
    0, 128, 0, 128, ⟨-34191771302081029651685946212427769492036061204, -34191771302081029651685946212427769492033964051⟩, ⟨-32292043263244265011204308939015842556846715446, -32292043263244265011204308939015842556844618293⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18679030162303741504086552505207128636420699062, 22162133741881529770516429908069211989432986974⟩
def wholeCExp : DyadicInterval precision := ⟨1417842757137037989742285799922994927468086581895, 1424616997239092963457576464131988993526565778404⟩
def wholeCLog : DyadicInterval precision := ⟨991041631832012714857158240438297378656595154964, 994476071531667759156497176411557099145165494774⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1417842757137037989742285799922994928017842395783, scale precision, 1424616997239092963457576464131988992976809964516, scale precision,
    0, 128, 0, 128, ⟨-44324267483763059541032859816138424545551175676, -44324267483763059541032859816138424545549078523⟩, ⟨-37358060324607483008173105010414256708852950797, -37358060324607483008173105010414256708850853644⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨34830775707694518323356855819802492385993843109, 39266125544418722242795595750766364675185952125⟩
def wholeBExp : DyadicInterval precision := ⟨1385042020891040503047967298047435945660723448338, 1393474206903787201785230037422771621528978564036⟩
def wholeBLog : DyadicInterval precision := ⟨974297031282803688730573659191636826590663176144, 978619971033722696354607064598753115511294545328⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1385042020891040503047967298047435946210479262226, scale precision, 1393474206903787201785230037422771620979222750148, scale precision,
    0, 128, 0, 128, ⟨-78532251088837444485591191501532729930477390100, -78532251088837444485591191501532729930475292947⟩, ⟨-69661551415389036646713711639604984195394623365, -69661551415389036646713711639604984195392526212⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisCell0001Sub1StableWitnesses

end


