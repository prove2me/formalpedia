-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062CertifiedArithmetic__17
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0062CertifiedArithmetic__17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:10:27.108967+00:00
-- url     : https://prove2.me/theorems/c7c119a2-6ca4-4173-be3a-959b7adaa136
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0062CertifiedArithmetic (+16 modules: GeneralCK/Certificates/E8TAxisZero0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0073CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0074CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0078CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0044GraphCenterA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0049GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043Geometry__25
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064GraphCenterA__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0068Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0071GraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0073GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0073GraphWholeD__10

-- ===== source module GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0062GraphCenterA.qJetBox,
   E8TAxisZero0062GraphCenterB.qJetBox,
   E8TAxisZero0062GraphCenterC.qJetBox,
   E8TAxisZero0062GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0062GraphWholeA.qJetBox,
   E8TAxisZero0062GraphWholeB.qJetBox,
   E8TAxisZero0062GraphWholeC.qJetBox,
   E8TAxisZero0062GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29627184016210071614010115611785150180061494391, 29627184016210071614010115611785304149928666695⟩
  | 0, 2 => ⟨89165744514951680050120781770313929370604559383, 89165744514951680050120781770314542398810493843⟩
  | 1, 1 => ⟨89205062245685827699053533969417600445300909839, 89205062245685827699053533969418722505251762229⟩
  | 0, 3 => ⟨183235433452417298629691771280301264148612779557, 183235433452417298629691771280303282145870964355⟩
  | 1, 2 => ⟨246191359084349609957745502160259966451627098726, 246191359084349609957745502160263618493480663362⟩
  | 2, 1 => ⟨246286469770997076601557382220241610107781475557, 246286469770997076601557382220248276711710138632⟩
  | 0, 4 => ⟨311410839872874903796330507839141883956047434813, 311410839872874903796330507839148810221596455061⟩
  | 1, 3 => ⟨463645093448844957713214238793979692662885738904, 463645093448844957713214238793992365211806282975⟩
  | 2, 2 => ⟨615925804902703090308015103985621343381239080302, 615925804902703090308015103985644746513012359403⟩
  | 3, 1 => ⟨616133024683086544938041572673063603548045409519, 616133024683086544938041572673107126850095206223⟩
  | 0, 5 => ⟨-1422742015520527570033983126347388899553684889042598, 1430748352226361038112483289779047831688844159885006⟩
  | 1, 4 => ⟨-2785734281452918873859783296173560891462814078426689, 2797795863020878508562010512894990281623244875352128⟩
  | 2, 3 => ⟨-5459809342679161998917428166193183928835217521687255, 5477184402189393832950156311659204115584459861226213⟩
  | 3, 2 => ⟨-10707790583123629678929817593481724962593116402408442, 10730573184450922384349721710114243632244730350067998⟩
  | 4, 1 => ⟨-21010829295495506192998759145517470933670107588949907, 21034031879186545597822643651829500970542559622053571⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0062Geometry.ds, E8TAxisZero0062Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 27827306491821781072186294048150267657374413967 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0062CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0063GraphCenterA.qJetBox,
   E8TAxisZero0063GraphCenterB.qJetBox,
   E8TAxisZero0063GraphCenterC.qJetBox,
   E8TAxisZero0063GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0063GraphWholeA.qJetBox,
   E8TAxisZero0063GraphWholeB.qJetBox,
   E8TAxisZero0063GraphWholeC.qJetBox,
   E8TAxisZero0063GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨26575745877334675795165731116044468958355417548, 26575745877334675795165731116044608279991112276⟩
  | 0, 2 => ⟨80705450595048575985091002261140584351982150553, 80705450595048575985091002261141135023991380830⟩
  | 1, 1 => ⟨80741480949164145448822440569112931868630617209, 80741480949164145448822440569113937729708690289⟩
  | 0, 3 => ⟨167237429441671086579229256800312484331854089755, 167237429441671086579229256800314291931686284662⟩
  | 1, 2 => ⟨224929959567114005147545074709567573070302169479, 224929959567114005147545074709570838330894099460⟩
  | 2, 1 => ⟨225017884622912435196268078898996503940223879525, 225017884622912435196268078899002454486228229640⟩
  | 0, 4 => ⟨286400170504321636567051640941302555242191199767, 286400170504321636567051640941308738437175809641⟩
  | 1, 3 => ⟨427133334562177012856197907753467118507143307948, 427133334562177012856197907753478414947272571648⟩
  | 2, 2 => ⟨567909849413591903446876850166329834998004605790, 567909849413591903446876850166350669196212998357⟩
  | 3, 1 => ⟨568102695132916604524111596143507379601862473331, 568102695132916604524111596143546076256416371631⟩
  | 0, 5 => ⟨-1255561008760088439703551799533528690290793300941464, 1262746049739643665815544219758958106723674741602372⟩
  | 1, 4 => ⟨-2456873878637114903607331175651234286039936349566475, 2467689165084398998755774464262918660277859634710376⟩
  | 2, 3 => ⟨-4812405538569764837735683269671361172994535134988767, 4827978511103014908790580026917825035634583753444108⟩
  | 3, 2 => ⟨-9432570114280149966023704553353945089137940843445523, 9452989714615967108304954594637897607603333389178857⟩
  | 4, 1 => ⟨-18497778538125556778874561070580792611641708877657440, 18518589820314081515475048549338352148705867516002984⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0063Geometry.ds, E8TAxisZero0063Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 24948682032235793249739063544177792085449846742 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0063CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0064GraphCenterA.qJetBox,
   E8TAxisZero0064GraphCenterB.qJetBox,
   E8TAxisZero0064GraphCenterC.qJetBox,
   E8TAxisZero0064GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0064GraphWholeA.qJetBox,
   E8TAxisZero0064GraphWholeB.qJetBox,
   E8TAxisZero0064GraphWholeC.qJetBox,
   E8TAxisZero0064GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨23815098222398871851876786728041560803878371976, 23815098222398871851876786728041686923923669711⟩
  | 0, 2 => ⟨72978983622359738012070251924767676484763722003, 72978983622359738012070251924768171182320331281⟩
  | 1, 1 => ⟨73011975766360627219234388208620043181452709484, 73011975766360627219234388208620944883496146008⟩
  | 0, 3 => ⟨152503695727651746549899015489384452882841395308, 152503695727651746549899015489386071938211803369⟩
  | 1, 2 => ⟨205331746126078483164205321023564685319394732797, 205331746126078483164205321023567604461629641131⟩
  | 2, 1 => ⟨205412984282625671899936489533881891922634712656, 205412984282625671899936489533887202567722003114⟩
  | 0, 4 => ⟨263223724377144643656904790956461575340288305534, 263223724377144643656904790956467094399042275932⟩
  | 1, 3 => ⟨393254050319595600855732486538598599064949307275, 393254050319595600855732486538608666947979859745⟩
  | 2, 2 => ⟨523324829403421117480598760479637693374906388448, 523324829403421117480598760479656236518049850910⟩
  | 3, 1 => ⟨523504281592707086744097451954610813593964053642, 523504281592707086744097451954645210230293434908⟩
  | 0, 5 => ⟨-1108954240403111305875023342300330068540387622988925, 1115365316526644646191207131288719349273017121908577⟩
  | 1, 4 => ⟨-2168647022940885891043360554969494764987023452388765, 2178285216852673474036663457673619806415620252171841⟩
  | 2, 3 => ⟨-4245300383000802334780690392476451032286472532496580, 4259167747059938125527918168141356901290905932929917⟩
  | 3, 2 => ⟨-8316105998113903115618693161644180568796854829076809, 8334285346264725721417547895850542186393146234131302⟩
  | 4, 1 => ⟨-16298725590641979956951934175139910947117469290596284, 16317268959466041671111990556908564626580455131506780⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0064Geometry.ds, E8TAxisZero0064Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 22345444771845907659114756787927776930932238421 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0064CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0065GraphCenterA.qJetBox,
   E8TAxisZero0065GraphCenterB.qJetBox,
   E8TAxisZero0065GraphCenterC.qJetBox,
   E8TAxisZero0065GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0065GraphWholeA.qJetBox,
   E8TAxisZero0065GraphWholeB.qJetBox,
   E8TAxisZero0065GraphWholeC.qJetBox,
   E8TAxisZero0065GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21319908440587260432859814090976051060028890265, 21319908440587260432859814090976165282961131460⟩
  | 0, 2 => ⟨65928736313887142553047394236260661886899496359, 65928736313887142553047394236261106353089486513⟩
  | 1, 1 => ⟨65958922108926973782053595543354369432831502754, 65958922108926973782053595543355177789635663687⟩
  | 0, 3 => ⟨138942958682158860540291313023374232932733599693, 138942958682158860540291313023375683082610557435⟩
  | 1, 2 => ⟨187277739590953928166037713421545817256876899199, 187277739590953928166037713421548426745129486898⟩
  | 2, 1 => ⟨187352755617452340081565608409301338256379647709, 187352755617452340081565608409306077181586644883⟩
  | 0, 4 => ⟨241752729350260514413589167521636456669563607017, 241752729350260514413589167521641382323198028620⟩
  | 1, 3 => ⟨361824109037205767799899786691272029006075688704, 361824109037205767799899786691281000299518674995⟩
  | 2, 2 => ⟨481933238255818471443512209287984034212792519514, 481933238255818471443512209288000534462942425784⟩
  | 3, 1 => ⟨482100207247574599929131980322724098592494585915, 482100207247574599929131980322754664956865560103⟩
  | 0, 5 => ⟨-981045376050755357860748228242580213958720992698777, 986752354834246721105345815452662239673311850615021⟩
  | 1, 4 => ⟨-1917318082086697054129879699298988624394563168355475, 1925885012781023529149262724175652059638607234719764⟩
  | 2, 3 => ⟨-3751051455247733715786154463520775452576668889210294, 3763365255856728077250090522228594554278070556210430⟩
  | 3, 2 => ⟨-7343563609502685309647155235101310569251478086779604, 7359698743992010674617052938067748441448165113173407⟩
  | 4, 1 => ⟨-14384089459112107054884347587428791086651974189360098, 14400552199912472023369448540994153139599130440127102⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0065Geometry.ds, E8TAxisZero0065Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 19993491737854118453373489917612863926799266395 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0065CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0066GraphCenterA.qJetBox,
   E8TAxisZero0066GraphCenterB.qJetBox,
   E8TAxisZero0066GraphCenterC.qJetBox,
   E8TAxisZero0066GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0066GraphWholeA.qJetBox,
   E8TAxisZero0066GraphWholeB.qJetBox,
   E8TAxisZero0066GraphWholeC.qJetBox,
   E8TAxisZero0066GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19066839756168753752579413930808988837536347514, 19066839756168753752579413930809092334237744358⟩
  | 0, 2 => ⟨59501227533249075149285987539076936615762926812, 59501227533249075149285987539077335994762358697⟩
  | 1, 1 => ⟨59528822711322560256931402185913073400659784269, 59528822711322560256931402185913798094698955732⟩
  | 0, 3 => ⟨126470289521877566121885860502300038050968628815, 126470289521877566121885860502301336861539608273⟩
  | 1, 2 => ⟨170657188762406069615640153983124812834336464452, 170657188762406069615640153983127145271941583988⟩
  | 2, 1 => ⟨170726415905384456315825754227947744264835599742, 170726415905384456315825754227951972384546992951⟩
  | 0, 4 => ⟨221867522997906552445505613450031709405656373218, 221867522997906552445505613450036104758659334621⟩
  | 1, 3 => ⟨332673393563193157242615046303334798767819897063, 332673393563193157242615046303342791188422847490⟩
  | 2, 2 => ⟨443514489733876943381606315491845029055765511231, 443514489733876943381606315491859707674885767105⟩
  | 3, 1 => ⟨443669820247608041742428939535853299022080226413, 443669820247608041742428939535880453648971254147⟩
  | 0, 5 => ⟨-865850413554889873276829554272783248456997315317603, 870928624474777847830268655016847594142892568758664⟩
  | 1, 4 => ⟨-1691078586973360878360022805910438595927619979981512, 1698689891776370050055457316171290986681535696028435⟩
  | 2, 3 => ⟨-3306353480849167457690697597697936528634740883540922, 3317282195832251366943763945041773412304701782928006⟩
  | 3, 2 => ⟨-6468942403526532505140569259560161905978646817040528, 6483254585344993491386562070402619699926362434178500⟩
  | 4, 1 => ⟨-12663063816651108970238521009401828007902122039129409, 12677667145495013583832723586524799552737715773058711⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0066Geometry.ds, E8TAxisZero0066Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 17870923056557270566544836281460941208655915365 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0066CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0067GraphCenterA.qJetBox,
   E8TAxisZero0067GraphCenterB.qJetBox,
   E8TAxisZero0067GraphCenterC.qJetBox,
   E8TAxisZero0067GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0067GraphWholeA.qJetBox,
   E8TAxisZero0067GraphWholeB.qJetBox,
   E8TAxisZero0067GraphWholeC.qJetBox,
   E8TAxisZero0067GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17034408088878344593282954091839434919932060355, 17034408088878344593282954091839528742679445569⟩
  | 0, 2 => ⟨53646817283908490049945110688220081575448411924, 53646817283908490049945110688220440480216544067⟩
  | 1, 1 => ⟨53672022539281653709680548656276899349757355638, 53672022539281653709680548656277549057210211177⟩
  | 0, 3 => ⟨115006651923118241847454330572931891329322467023, 115006651923118241847454330572933054530792634166⟩
  | 1, 2 => ⟨155366982328419814231060268934290724140321178033, 155366982328419814231060268934292808699542535213⟩
  | 2, 1 => ⟨155430824590361454654116835907130113571317475529, 155430824590361454654116835907133885335436684009⟩
  | 0, 4 => ⟨203456964274218899299595163640548582091798921972, 203456964274218899299595163640552503509805418860⟩
  | 1, 3 => ⟨305643955135449609741215423140031161877123113662, 305643955135449609741215423140038280508866246269⟩
  | 2, 2 => ⟨407863813987490768531192554112737181533849314634, 407863813987490768531192554112750235899288733058⟩
  | 3, 1 => ⟨408008289513439184084795133154669857459922399047, 408008289513439184084795133154693973395666666038⟩
  | 0, 5 => ⟨-761148368081686381435408264988659492248838068798204, 765664148518072769693661351190362891007234527968995⟩
  | 1, 4 => ⟨-1485545920060814575723950958129315797819621127771165, 1492303376951397433635127355378385346864392599036539⟩
  | 2, 3 => ⟨-2902556296192189197640980293889327578373032424252214, 2912248474257104562794635056414196364253688137910860⟩
  | 3, 2 => ⟨-5675165621520835534754421403654857867003497095062960, 5687851227352531018897607667095495203049736779309873⟩
  | 4, 1 => ⟨-11101929713895898549581592364597432542912963399718533, 11114874542860319942991113898158317057822616802403992⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0067Geometry.ds, E8TAxisZero0067Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 15957353120260233695249703517910266438707076829 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0067CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0068GraphCenterA.qJetBox,
   E8TAxisZero0068GraphCenterB.qJetBox,
   E8TAxisZero0068GraphCenterC.qJetBox,
   E8TAxisZero0068GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0068GraphWholeA.qJetBox,
   E8TAxisZero0068GraphWholeB.qJetBox,
   E8TAxisZero0068GraphWholeC.qJetBox,
   E8TAxisZero0068GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15202848788359237481145306598114061544049195135, 15202848788359237481145306598114146639711725353⟩
  | 0, 2 => ⟨48319442134591914145446657344010889734376125618, 48319442134591914145446657344011212306193851926⟩
  | 1, 1 => ⟨48342444136135160086846332075037958691672637244, 48342444136135160086846332075038541192755734924⟩
  | 0, 3 => ⟨104478479348963577197982113240196053075454456631, 104478479348963577197982113240197094771407402446⟩
  | 1, 2 => ⟨141311099558868118812375741198740104734350843943, 141311099558868118812375741198741967538907728743⟩
  | 2, 1 => ⟨141369933822587836719164248149319940010062558527, 141369933822587836719164248149323304119278901171⟩
  | 0, 4 => ⟨186417872243974550013648626962601074496480355623, 186417872243974550013648626962604572407302972258⟩
  | 1, 3 => ⟨280589205258741023687186919050727744776359409160, 280589205258741023687186919050734083542513013441⟩
  | 2, 2 => ⟨374791202538655662778085524625290573424902841245, 374791202538655662778085524625302179786823114262⟩
  | 3, 1 => ⟨374925549541725499607718972805435136211828582062, 374925549541725499607718972805456546259182918458⟩
  | 0, 5 => ⟨-666447835961409748440076611813900087355204300364470, 670458724607369472685516163726265613149961577631869⟩
  | 1, 4 => ⟨-1299744566356481569170130950124122004614994340639523, 1305736444471174172797692818400175737004442299635609⟩
  | 2, 3 => ⟨-2537717809086492871193522971789544652627254382980921, 2546302250646159662346810281508439308374678546436710⟩
  | 3, 2 => ⟨-4958359159004037626929536215802352803740382287834838, 4969588366372071420268688017873584709128905146496502⟩
  | 4, 1 => ⟨-9692946726980820845174823839630649324179013155282945, 9704406834082352243062778424759563681246049116797700⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0068Geometry.ds, E8TAxisZero0068Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 14233926984194006532785216297165383817373237245 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0068CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0069GraphCenterA.qJetBox,
   E8TAxisZero0069GraphCenterB.qJetBox,
   E8TAxisZero0069GraphCenterC.qJetBox,
   E8TAxisZero0069GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0069GraphWholeA.qJetBox,
   E8TAxisZero0069GraphWholeB.qJetBox,
   E8TAxisZero0069GraphWholeC.qJetBox,
   E8TAxisZero0069GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13553992532856611774828254068692466183422638188, 13553992532856611774828254068692543404175274109⟩
  | 0, 2 => ⟨43476369713814300234696529413580481054266459122, 43476369713814300234696529413580771011166215689⟩
  | 1, 1 => ⟨43497342043669520852302361861510053547149462830, 43497342043669520852302361861510575818822531365⟩
  | 0, 3 => ⟨94817280793254442905374018833302130433444078323, 94817280793254442905374018833303063285071012673⟩
  | 1, 2 => ⟨128400098109912032848818347190717548825927609163, 128400098109912032848818347190719213293002628162⟩
  | 2, 1 => ⟨128454276114825367578444785116559679627626578455, 128454276114825367578444785116562679678228458375⟩
  | 0, 4 => ⟨170654489210475067008303743594891989797533361202, 170654489210475067008303743594895109511779844220⟩
  | 1, 3 => ⟨257373141813073855602669976593704421807849970221, 257373141813073855602669976593710064973464403416⟩
  | 2, 2 => ⟨344120397335793583068827233811150921590856772614, 344120397335793583068827233811161237885151913912⟩
  | 3, 1 => ⟨344245289296506134565083161628369429980155102334, 344245289296506134565083161628388432048865489465⟩
  | 0, 5 => ⟨-581226493790206539967840795171937223043490400451513, 584784350906713034128742811967679019500965482202814⟩
  | 1, 4 => ⟨-1132635395533321425944071006099398617659396965991986, 1137941133830330092367602625938712527283272944465949⟩
  | 2, 3 => ⟨-2209767970434750276432443671712691287383847989310202, 2217360461446485459872638032671597903410986985490493⟩
  | 3, 2 => ⟨-4314395148886580995266984153136260039481060028296040, 4324320836246431088323417034473076163723905982955618⟩
  | 4, 1 => ⟨-8427876518052322054929073641300832913924760571048775, 8438007961355604872979093001937861357061605531859496⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0069Geometry.ds, E8TAxisZero0069Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 12683324200262072784039055289204121856379673235 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0069CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0070GraphCenterA.qJetBox,
   E8TAxisZero0070GraphCenterB.qJetBox,
   E8TAxisZero0070GraphCenterC.qJetBox,
   E8TAxisZero0070GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0070GraphWholeA.qJetBox,
   E8TAxisZero0070GraphWholeB.qJetBox,
   E8TAxisZero0070GraphWholeC.qJetBox,
   E8TAxisZero0070GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12071149730306366573293585279293955982492292602, 12071149730306366573293585279294026095421640853⟩
  | 0, 2 => ⟨39077970967474672003037927829285850207570677657, 39077970967474672003037927829286110887721571688⟩
  | 1, 1 => ⟨39097074991276528142950170349922921368790534917, 39097074991276528142950170349923389667744331711⟩
  | 0, 3 => ⟨85959273765379088703388949901651580493622867317, 85959273765379088703388949901652415837315668666⟩
  | 1, 2 => ⟨116550637424225353395845428571205581436413443725, 116550637424225353395845428571207068508826375640⟩
  | 2, 1 => ⟨116600487600146481610896779855066037414135656268, 116600487600146481610896779855068712347754659130⟩
  | 0, 4 => ⟨156077966201318166807047108722933699472709000444, 156077966201318166807047108722936481296776691597⟩
  | 1, 3 => ⟨235869606541774724090136627851896773134116633623, 235869606541774724090136627851901795601814026100⟩
  | 2, 2 => ⟨315687920211995885426836938670037051738717410601, 315687920211995885426836938670046218227336197790⟩
  | 3, 1 => ⟨315803981515774168379949731059595157760550848592, 315803981515774168379949731059612016153046318575⟩
  | 0, 5 => ⟨-504925563357208224541476265122193406466230046137444, 508077150688087138094530559760269062024780485380641⟩
  | 1, 4 => ⟨-983107793798808803826301760812154001458635017971030, 987798924959111037429613203590458643912798284748421⟩
  | 2, 3 => ⟨-1916496785321705949373340532376240074311883897348521, 1923201480480988828622324579538494612907157666802772⟩
  | 3, 2 => ⟨-3738872082876946044957613523799317937993707857984958, 3747631684041720163247965067124934221169982473690853⟩
  | 4, 1 => ⟨-7297946264278390177879967547639150223961741008055604, 7306889288119413032152246047023354700989991544338221⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0070Geometry.ds, E8TAxisZero0070Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 11289647745664272035436079329060987455431422321 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0070CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0071GraphCenterA.qJetBox,
   E8TAxisZero0071GraphCenterB.qJetBox,
   E8TAxisZero0071GraphCenterC.qJetBox,
   E8TAxisZero0071GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0071GraphWholeA.qJetBox,
   E8TAxisZero0071GraphWholeB.qJetBox,
   E8TAxisZero0071GraphWholeC.qJetBox,
   E8TAxisZero0071GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10739002805953295849887922480633182110488231430, 10739002805953295849887922480633245806207112968⟩
  | 0, 2 => ⟨35087508925811429971524619070795092286656953882, 35087508925811429971524619070795326824085095103⟩
  | 1, 1 => ⟨35104894599486423041557785757051799362330415689, 35104894599486423041557785757052219572983275234⟩
  | 0, 3 => ⟨77845043424583600293761397327027341223466471971, 77845043424583600293761397327028090667205654655⟩
  | 1, 2 => ⟨105685036321202974109867722374675863322356706026, 105685036321202974109867722374677194544915429748⟩
  | 2, 1 => ⟨105730865485005200226191860231454136710510870809, 105730865485005200226191860231456526741805576177⟩
  | 0, 4 => ⟨142605869438343431537086683155335813203521391792, 142605869438343431537086683155338303943724826022⟩
  | 1, 3 => ⟨215961572059683423296125855355052578761823015327, 215961572059683423296125855355057068100888962972⟩
  | 2, 2 => ⟨289342140400259419084416551960055548649082605584, 289342140400259419084416551960063730089090198187⟩
  | 3, 1 => ⟨289449950080584241890762703636752203445450415274, 289449950080584241890762703636767229527275265849⟩
  | 0, 5 => ⟨-437241031168481163220307743453203804637470248964967, 440033940257035158322001680136363967225219828284294⟩
  | 1, 4 => ⟨-850556952330359690743943519031722659813366415521539, 854706506073395460638434477350646031020815328728070⟩
  | 2, 3 => ⟨-1656698491163784406646797076418810419347958365951081, 1662621905773787492778854340370802140703924845165658⟩
  | 3, 2 => ⟨-3229382271470098596787349228116526983531573721066160, 3237116232282270284774236882460189223204105868935488⟩
  | 4, 1 => ⟨-6298341684317302988633224539160054876706475330007356, 6306238686135788480248578204236336059954112829751039⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0071Geometry.ds, E8TAxisZero0071Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 10038299313348657820442660207011852521852664314 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0071CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0072GraphCenterA.qJetBox,
   E8TAxisZero0072GraphCenterB.qJetBox,
   E8TAxisZero0072GraphCenterC.qJetBox,
   E8TAxisZero0072GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0072GraphWholeA.qJetBox,
   E8TAxisZero0072GraphWholeB.qJetBox,
   E8TAxisZero0072GraphWholeC.qJetBox,
   E8TAxisZero0072GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9543505804803043674842919704048241126334566841, 9543505804803043674842919704048299026709401172⟩
  | 0, 2 => ⟨31470942775300496458816363318690770989009110824, 31470942775300496458816363318690982075584544804⟩
  | 1, 1 => ⟨31486749393278119299147766193238920413933056926, 31486749393278119299147766193239297569268125095⟩
  | 0, 3 => ⟨70419226821320500488539205206556656839818289122, 70419226821320500488539205206557329484081279997⟩
  | 1, 2 => ⟨95730863431684278419107440665136925768103612657, 95730863431684278419107440665138117902280491333⟩
  | 2, 1 => ⟨95772958352060110308512398831038566769437209381, 95772958352060110308512398831040702970347915030⟩
  | 0, 4 => ⟨130161707088916416972435508623008203796749750325, 130161707088916416972435508623010435491194147422⟩
  | 1, 3 => ⟨197540457522327785402649629999334795157270075395, 197540457522327785402649629999338810721778230932⟩
  | 2, 2 => ⟨264942379088876031241709338592017561602103485560, 264942379088876031241709338592024868811369658230⟩
  | 3, 1 => ⟨265042474424203608016888809394075291251709035944, 265042474424203608016888809394088693226748654596⟩
  | 0, 5 => ⟨-377324534813417962590751067757835497769031565088724, 379798092571045693261380273259676433419317629770678⟩
  | 1, 4 => ⟨-733299403927937675902056314521293796036843371893585, 736967433036364753326132006711335642327778595230768⟩
  | 2, 3 => ⟨-1427030326170379379785054270188331664726400437531537, 1432259784132654464937268914108377602615798802440703⟩
  | 3, 2 => ⟨-2779284982826216942122983879335276164161762756692905, 2786108419477770987219315028026206281822359020425510⟩
  | 4, 1 => ⟨-5415864813073144632661690138221547286207091676743937, 5422833154439929522081007918380193258061310839690530⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0072Geometry.ds, E8TAxisZero0072Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 8915940330211703190143463321079675995395426199 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0072CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0073GraphCenterA.qJetBox,
   E8TAxisZero0073GraphCenterB.qJetBox,
   E8TAxisZero0073GraphCenterC.qJetBox,
   E8TAxisZero0073GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0073GraphWholeA.qJetBox,
   E8TAxisZero0073GraphWholeB.qJetBox,
   E8TAxisZero0073GraphWholeC.qJetBox,
   E8TAxisZero0073GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8471790779639222199530143262244588066111721754, 8471790779639222199530143262244640731195828989⟩
  | 0, 2 => ⟨28196746079053872933035029443400615261694359517, 28196746079053872933035029443400805278300929375⟩
  | 1, 1 => ⟨28211102968534696370687450401591531367950043766, 28211102968534696370687450401591869908997816922⟩
  | 0, 3 => ⟨63630221216660015378548108848731279073979525062, 63630221216660015378548108848731882720335828733⟩
  | 1, 2 => ⟨86620559145178542584512517264061746270334855036, 86620559145178542584512517264062813614986248193⟩
  | 2, 1 => ⟨86659187980835704272729286698278096871374492623, 86659187980835704272729286698280005640493098789⟩
  | 0, 4 => ⟨118674476235659868410199467419783925393947400568, 118674476235659868410199467419785924174836724742⟩
  | 1, 3 => ⟨180505473050819951127727049430503602088473500553, 180505473050819951127727049430507191838186843583⟩
  | 2, 2 => ⟨242358051268049385360414960186594948914673203975, 242358051268049385360414960186601470857700106177⟩
  | 3, 1 => ⟨242450931227176718528354062482775967203462137722, 242450931227176718528354062482787911470587722229⟩
  | 0, 5 => ⟨-324544214756786885329099931784662211060752671230855, 326732057662580302729425058982539832160816449377396⟩
  | 1, 4 => ⟨-630081264775889458402913049847578035729072733782947, 633318935777989667109930615790633124513397611547593⟩
  | 2, 3 => ⟨-1225002029691327685020057244187768763335317787775094, 1229611744730750461406964481428775043813608200513358⟩
  | 3, 2 => ⟨-2383631416843884810762397110320627085722193747234585, 2389642099956877431192430392256651555191732541798375⟩
  | 4, 1 => ⟨-4640675835075100502190626289946671773562648203600565, 4646815475619324643897178736247340615671168556970246⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0073Geometry.ds, E8TAxisZero0073Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 7910346939099603450922826346616463541260085658 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0073CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0074GraphCenterA.qJetBox,
   E8TAxisZero0074GraphCenterB.qJetBox,
   E8TAxisZero0074GraphCenterC.qJetBox,
   E8TAxisZero0074GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0074GraphWholeA.qJetBox,
   E8TAxisZero0074GraphWholeB.qJetBox,
   E8TAxisZero0074GraphWholeC.qJetBox,
   E8TAxisZero0074GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7512080476039262441559492120942641112412713984, 7512080476039262441559492120942689046668799415⟩
  | 0, 2 => ⟨25235738037559583505911733111049487020342891135, 25235738037559583505911733111049658107033428174⟩
  | 1, 1 => ⟨25248765203288929582485357440134247507798653257, 25248765203288929582485357440134551421344117305⟩
  | 0, 3 => ⟨57429915431740248058008325841611080833727805978, 57429915431740248058008325841611622484264398187⟩
  | 1, 2 => ⟨78291087707775588986701099677803732031882929628, 78291087707775588986701099677804687425738311437⟩
  | 2, 1 => ⟨78326501324678310088209956912576940187982614064, 78326501324678310088209956912578645221346285149⟩
  | 0, 4 => ⟨108078230571711538190580433569660283750624741514, 108078230571711538190580433569662072922833079137⟩
  | 1, 3 => ⟨164762993855224432772811964629584292642549285491, 164762993855224432772811964629587499590491342996⟩
  | 2, 2 => ⟨221467846245068843023740427724419129505519898549, 221467846245068843023740427724424946204428885996⟩
  | 3, 1 => ⟨221553974771230104508280183204041338315116790782, 221553974771230104508280183204051974727626636772⟩
  | 0, 5 => ⟨-278208125259666163359625758169966069649742224961643, 280141054557572242021167516674480552432379295566694⟩
  | 1, 4 => ⟨-539534137649720128191999649285247746789716678180684, 542388273727775825321463815991136320138045752743772⟩
  | 2, 3 => ⟨-1047905550850665696173210142487564907750929580276888, 1051963391095552838234182987155879393964485327713385⟩
  | 3, 2 => ⟨-2037059434532466471304079692771014823334756878872241, 2042346693243663554454951204887153664049598965598937⟩
  | 4, 1 => ⟨-3962152232012750984464765835854669827418336915412352, 3967554297361324168106015964933848468099414261190576⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0074Geometry.ds, E8TAxisZero0074Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 7010345171681806483050744508235013353658536413 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0074CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0075GraphCenterA.qJetBox,
   E8TAxisZero0075GraphCenterB.qJetBox,
   E8TAxisZero0075GraphCenterC.qJetBox,
   E8TAxisZero0075GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0075GraphWholeA.qJetBox,
   E8TAxisZero0075GraphWholeB.qJetBox,
   E8TAxisZero0075GraphWholeC.qJetBox,
   E8TAxisZero0075GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6653606864762341641816090249394859203534357093, 6653606864762341641816090249394902861420633649⟩
  | 0, 2 => ⟨22560926731642594997491968141067158960559961423, 22560926731642594997491968141067313047681201670⟩
  | 1, 1 => ⟨22572735455429813958592346027014684272398061987, 22572735455429813958592346027014957150858027218⟩
  | 0, 3 => ⟨51773443132481746663603865215847260361741834604, 51773443132481746663603865215847746372767023460⟩
  | 1, 2 => ⟨70683618042358891312197334954676236236990102045, 70683618042358891312197334954677091324579546390⟩
  | 2, 1 => ⟨70716051216035732114735296138374664458396271559, 70716051216035732114735296138376187227698046190⟩
  | 0, 4 => ⟨98311669790585303533043767436959082011658197323, 98311669790585303533043767436960682922668429791⟩
  | 1, 3 => ⟨150225965683710534259358498171565328030389228153, 150225965683710534259358498171568191564450817554⟩
  | 2, 2 => ⟨202158949112783960149264904506135110279454165583, 202158949112783960149264904506140294978033814438⟩
  | 3, 1 => ⟨202238758233481655142281504721136247747957265120, 202238758233481655142281504721145713376360677723⟩
  | 0, 5 => ⟨-237731257377531493161672104187430661872854375927748, 239439204696383957443864203647704137847738273067794⟩
  | 1, 4 => ⟨-460500292218199505601050957749229056324406607662103, 463015339186552332096493007291522081191948650913543⟩
  | 2, 3 => ⟨-893448133419257658853275749282884859546994771562151, 897017600777984269503095463449907077004009130436280⟩
  | 3, 2 => ⟨-1735025958965508836556942381313230150479261105253936, 1739672719480672068788749709489621835770792158077513⟩
  | 4, 1 => ⟨-3371287456331210405080815999802078936742178159418587, 3376036511958558779323168278743915760602051391509689⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0075Geometry.ds, E8TAxisZero0075Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 6205721299887912643440442932839187467558018173 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0075CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0076GraphCenterA.qJetBox,
   E8TAxisZero0076GraphCenterB.qJetBox,
   E8TAxisZero0076GraphCenterC.qJetBox,
   E8TAxisZero0076GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0076GraphWholeA.qJetBox,
   E8TAxisZero0076GraphWholeB.qJetBox,
   E8TAxisZero0076GraphWholeC.qJetBox,
   E8TAxisZero0076GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5886535108975281810277629054046745231348595141, 5886535108975281810277629054046785022335109249⟩
  | 0, 2 => ⟨20147363342484859602343951063978246687907165585, 20147363342484859602343951063978385507654105023⟩
  | 1, 1 => ⟨20158056741482958278998079666972314784447913182, 20158056741482958278998079666972559846816882660⟩
  | 0, 3 => ⟨46618956887138345667688343639616299045634207642, 46618956887138345667688343639616735120706316028⟩
  | 1, 2 => ⟨63743231768514676791533199809007614052751986411, 63743231768514676791533199809008379269097922695⟩
  | 2, 1 => ⟨63772904277959755304957523482742057422532874894, 63772904277959755304957523482743417144571780189⟩
  | 0, 4 => ⟨89317751960901312824712620569512357552850192021, 89317751960901312824712620569513789401388613453⟩
  | 1, 3 => ⟨136813343696230680236171725177712403430235012545, 136813343696230680236171725177714958946457635595⟩
  | 2, 2 => ⟨184326306078143546426672290863235600847483108527, 184326306078143546426672290863240219317923029773⟩
  | 3, 1 => ⟨184400198825819276338959725835253628939754106473, 184400198825819276338959725835262046778392480987⟩
  | 0, 5 => ⟨-202690990039879910480269072281325151544560224850252, 204201890598936719786326719971452633643533796870943⟩
  | 1, 4 => ⟨-392141365271236672887224455435884896788986180739792, 394360821299306023147783636752070034819712303849587⟩
  | 2, 3 => ⟨-759966480028608353598079405465489311995909416341560, 763111558378945900012618560213679432602963064947290⟩
  | 3, 2 => ⟨-1474230066408240940251322485741017164966623464014139, 1478321036838453053929623226348269225050875662551410⟩
  | 4, 1 => ⟨-2861527926255407447446812800358348053469802790183416, 2865709686293915375279791598722551407568703864068159⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0076Geometry.ds, E8TAxisZero0076Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 5487144640140058828721148721517118102558022924 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0076CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0077GraphCenterA.qJetBox,
   E8TAxisZero0077GraphCenterB.qJetBox,
   E8TAxisZero0077GraphCenterC.qJetBox,
   E8TAxisZero0077GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0077GraphWholeA.qJetBox,
   E8TAxisZero0077GraphWholeB.qJetBox,
   E8TAxisZero0077GraphWholeC.qJetBox,
   E8TAxisZero0077GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5201892588907280107752207106402324793011009974, 5201892588907280107752207106402361086085670491⟩
  | 0, 2 => ⟨17972006400219258959144892741255237937430633677, 17972006400219258959144892741255363041707647167⟩
  | 1, 1 => ⟨17981679947735287891568240683188969008362403701, 17981679947735287891568240683189189133962465916⟩
  | 0, 3 => ⟨41927421754053162950747222167103404188403962333, 41927421754053162950747222167103795427234355986⟩
  | 1, 2 => ⟨57418656788834699874349962907789096914475541752, 57418656788834699874349962907789781576268071576⟩
  | 2, 1 => ⟨57445774409075678219837031421769040114518395071, 57445774409075678219837031421770253922823149152⟩
  | 0, 4 => ⟨81043330332876373706030628367154132452611747697, 81043330332876373706030628367155412409645989246⟩
  | 1, 3 => ⟨124449567083884019290448897852284788750926332753, 124449567083884019290448897852287067878408398113⟩
  | 2, 2 => ⟨167871936846164746046541828828696683348235269775, 167871936846164746046541828828700794315503439468⟩
  | 3, 1 => ⟨167940289974455103563652715388505525435887485930, 167940289974455103563652715388513005215159532820⟩
  | 0, 5 => ⟨-172352503032207874695223921421511550902063686609039, 173689137756909292653513268131526304853410560015909⟩
  | 1, 4 => ⟨-333008554886365305602058382371597009997978825423366, 334966929018008615874490134797949266504906826838029⟩
  | 2, 3 => ⟨-644600964229147449150446459448869585120485216854744, 647371530779307703955233713484347730061500142731200⟩
  | 3, 2 => ⟨-1249023488386616458462829410312022358430171421537776, 1252624211442235030790409897594011781046883361479691⟩
  | 4, 1 => ⟨-2421711611541034368968866861780545216804083073149791, 2425392912769379390428142837709129953368297269470316⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0077Geometry.ds, E8TAxisZero0077Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 4846132188527483976502750372710923024747783322 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0077CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0078GraphCenterA.qJetBox,
   E8TAxisZero0078GraphCenterB.qJetBox,
   E8TAxisZero0078GraphCenterC.qJetBox,
   E8TAxisZero0078GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0078GraphWholeA.qJetBox,
   E8TAxisZero0078GraphWholeB.qJetBox,
   E8TAxisZero0078GraphWholeC.qJetBox,
   E8TAxisZero0078GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4591502639540149665773832600037886226244534907, 4591502639540149665773832600037919353962017574⟩
  | 0, 2 => ⟨16013595173377154656612771802960441351159036510, 16013595173377154656612771802960554134431214846⟩
  | 1, 1 => ⟨16022337185719890419566063675850703451728934193, 16022337185719890419566063675850901224113194354⟩
  | 0, 3 => ⟨37662427073557494817281312391219274235325017908, 37662427073557494817281312391219625229463590291⟩
  | 1, 2 => ⟨51662024693622477886318245898495361613893736714, 51662024693622477886318245898495974099379583243⟩
  | 2, 1 => ⟨51686780094559627863610745957248457640093111261, 51686780094559627863610745957249540924032863329⟩
  | 0, 4 => ⟨73438816004000836119647398794149753276672544758, 73438816004000836119647398794150896874823346723⟩
  | 1, 3 => ⟨113064071711202470494295151344862291387320022166, 113064071711202470494295151344864322719017936495⟩
  | 2, 2 => ⟨152704297186718866313753433444564545161682767221, 152704297186718866313753433444568201678632112819⟩
  | 3, 1 => ⟨152767463668261165986291613485154288336335015186, 152767463668261165986291613485160929115705429528⟩
  | 0, 5 => ⟨-146199902287354122698302470896032989524947114800348, 147383986494225045102732405050337667939894772817379⟩
  | 1, 4 => ⟨-282082581128375339781714960701929097313825817999065, 283811602611922413052484802201259205416938260960044⟩
  | 2, 3 => ⟨-545336622298778534531402115533992937815004033722902, 547777304393528438503642594696929058210462030920394⟩
  | 3, 2 => ⟨-1055421186107810050966384982891330356394381064165457, 1058589450698908215050720500770372706595366200180984⟩
  | 4, 1 => ⟨-2043954077143330876876102282223285293524636032906789, 2047193862754043264976676108742915528303553467328332⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0078Geometry.ds, E8TAxisZero0078Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 4274947857378464038966522954361639760996761544 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0078CertifiedArithmetic

end


