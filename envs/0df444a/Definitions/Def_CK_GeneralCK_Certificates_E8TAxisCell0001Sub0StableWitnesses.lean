-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Sub0StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisCell0001Sub0StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:25:39.436497+00:00
-- url     : https://prove2.me/theorems/8b1465c7-b25b-417a-b203-40b05373a5f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCell0001Sub0StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨15671095633019860897215209866369230294530182688, 15671095633019860897215209866369230294530182689⟩
def centerDExp : DyadicInterval precision := ⟨1430493126269901616989962472786282227563085586833, 1430493126269901616989962472786282229762108842386⟩
def centerDLog : DyadicInterval precision := ⟨997448659491958118410211053001204308338128746073, 997448659491958118410211053001204310537152001626⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1430493126269901616989962472786282228112841400721, scale precision, 1430493126269901616989962472786282229212353028498, scale precision,
    0, 128, 0, 128, ⟨-31342191266039721794430419732738461150734173770, -31342191266039721794430419732738461150732076617⟩, ⟨-31342191266039721794430419732738460027388654137, -31342191266039721794430419732738460027386556984⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨19470621277533306580496790195465518778776729458, 19470621277533306580496790195465518778776729459⟩
def centerCExp : DyadicInterval precision := ⟨1423074606116073762821803958238303813037920929367, 1423074606116073762821803958238303815236944184920⟩
def centerCLog : DyadicInterval precision := ⟨993694811301131722458321493889457649263275974100, 993694811301131722458321493889457651462299229653⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1423074606116073762821803958238303813587676743255, scale precision, 1423074606116073762821803958238303814687188371032, scale precision,
    0, 128, 0, 128, ⟨-38941242555066613160993580390931038122155280129, -38941242555066613160993580390931038122153182976⟩, ⟨-38941242555066613160993580390931036992953734860, -38941242555066613160993580390931036992951637707⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨35147560547285289813533577747055089042057399321, 35147560547285289813533577747055089042057399322⟩
def centerBExp : DyadicInterval precision := ⟨1392870258438640800857414402689503949944641751754, 1392870258438640800857414402689503952143665007307⟩
def centerBLog : DyadicInterval precision := ⟨978310768752074097249526093622470834630947155556, 978310768752074097249526093622470836829970411109⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1392870258438640800857414402689503950494397565642, scale precision, 1392870258438640800857414402689503951593909193419, scale precision,
    0, 128, 0, 128, ⟨-70295121094570579627067155494110178660959969823, -70295121094570579627067155494110178660957872670⟩, ⟨-70295121094570579627067155494110177507271724615, -70295121094570579627067155494110177507269627462⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨15196173486161644112312625263859972843392477663, 16146021631622132505602154469507921559441792474⟩
def wholeDExp : DyadicInterval precision := ⟨1429563729219877177794428923148060134530124319950, 1431423120000492259122295500270501609338356151294⟩
def wholeDLog : DyadicInterval precision := ⟨996978902895462305330196666434672377033579848542, 997918566589803370182164072894784146467964879609⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1429563729219877177794428923148060135079880133838, scale precision, 1431423120000492259122295500270501608788600337406, scale precision,
    0, 128, 0, 128, ⟨-32292043263244265011204308939015843680922551602, -32292043263244265011204308939015843680920454449⟩, ⟨-30392346972323288224625250527719945125478162145, -30392346972323288224625250527719945125476064992⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨17729137610744576247007092795803619488372747277, 21212169286380562279755397007799150063684601001⟩
def wholeCExp : DyadicInterval precision := ⟨1419687128764521553902635583704152235899907790562, 1426470040636792960830657899926339242936897915377⟩
def wholeCLog : DyadicInterval precision := ⟨991977500846351802001245084505971667354350771962, 995414133081165357888197725645466148699321652405⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1419687128764521553902635583704152236449663604450, scale precision, 1426470040636792960830657899926339242387142101489, scale precision,
    0, 128, 0, 128, ⟨-42424338572761124559510794015598300693318201961, -42424338572761124559510794015598300693316104808⟩, ⟨-35458275221489152494014185591607238413489692836, -35458275221489152494014185591607238413487595683⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨32930145378693397992756732486482221311222413252, 37365163894633166934139863628747988917988881051⟩
def wholeBExp : DyadicInterval precision := ⟨1388649734044654119234359722553860932945539022911, 1397103250502184060148022799141349111499322099208⟩
def wholeBLog : DyadicInterval precision := ⟨976148167549896511977221673672472961671603524501, 980476548939230474057457544883516015981752345564⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1388649734044654119234359722553860933495294836799, scale precision, 1397103250502184060148022799141349110949566285320, scale precision,
    0, 128, 0, 128, ⟨-74730327789266333868279727257495978414576136146, -74730327789266333868279727257495978414574038993⟩, ⟨-65860290757386795985513464972964442047349494880, -65860290757386795985513464972964442047347397727⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisCell0001Sub0StableWitnesses

end


