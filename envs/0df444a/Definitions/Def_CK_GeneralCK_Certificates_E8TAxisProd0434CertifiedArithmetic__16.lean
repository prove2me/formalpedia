-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0434CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0434CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:56:16.55688+00:00
-- url     : https://prove2.me/theorems/3baeb5fb-7a08-4beb-a847-6e4c11ad3218
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0434CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0435CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0436CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0437CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0438CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0439CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0440CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0441CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0442CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0443CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0444CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0445CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0446CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0447CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0448CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0449CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0433GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0418GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0422GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0430GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0431GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0419GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0429GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0431GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0419Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0435GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0435GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0438GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0444GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0446GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0446GraphWholeA__10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0434GraphCenterA.qJetBox,
   E8TAxisProd0434GraphCenterB.qJetBox,
   E8TAxisProd0434GraphCenterC.qJetBox,
   E8TAxisProd0434GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0434GraphWholeA.qJetBox,
   E8TAxisProd0434GraphWholeB.qJetBox,
   E8TAxisProd0434GraphWholeC.qJetBox,
   E8TAxisProd0434GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33120079066302710467738483771083290215905780699, 33120079066302710467738483771083467185532670544⟩
  | 0, 2 => ⟨98672914973627063353822085032091526025408480034, 98672914973627063353822085032092220189996937480⟩
  | 1, 1 => ⟨98801726460869882364152302610529427255526436014, 98801726460869882364152302610530688080159376121⟩
  | 0, 3 => ⟨201019195753538704454953874965081163569102081815, 201019195753538704454953874965083443251362908921⟩
  | 1, 2 => ⟨269873122949186878699308720924894052644645144072, 269873122949186878699308720924898156839980151143⟩
  | 2, 1 => ⟨270182035561238700068245536321113466320129302283, 270182035561238700068245536321120958207650614835⟩
  | 0, 4 => ⟨339023505166797484616851103077866077786656199011, 339023505166797484616851103077873904413121596478⟩
  | 1, 3 => ⟨503961765208695431728124776576148424692507282327, 503961765208695431728124776576162694623715388665⟩
  | 2, 2 => ⟨669049578056167078906103906526617105836266792619, 669049578056167078906103906526643462734037933394⟩
  | 3, 1 => ⟨669718360703055441360273912035892639618388473259, 669718360703055441360273912035941702637064728370⟩
  | 0, 5 => ⟨-1610637653155836257271900046367706221393542385505640, 1619484946526247754608361436669585898756834247293902⟩
  | 1, 4 => ⟨-3155330408197033811464785590147987485148857705939836, 3168679055301463864431824951987269232000024924326269⟩
  | 2, 3 => ⟨-6187489334207711789443101915550414533891241112517345, 6206740001000227387963971506211215840206409889558827⟩
  | 3, 2 => ⟨-12141386958543106701491580501866308991093845305534238, 12166647550435953424038759499171120391514864028154046⟩
  | 4, 1 => ⟨-23836602021210228209199825940036547152768314434012922, 23862338703121341850750629349916660355308489070028526⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0434Geometry.ds, E8TAxisProd0434Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31124458617802063263666345331386793531109537516 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0434CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0435GraphCenterA.qJetBox,
   E8TAxisProd0435GraphCenterB.qJetBox,
   E8TAxisProd0435GraphCenterC.qJetBox,
   E8TAxisProd0435GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0435GraphWholeA.qJetBox,
   E8TAxisProd0435GraphWholeB.qJetBox,
   E8TAxisProd0435GraphWholeC.qJetBox,
   E8TAxisProd0435GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29738784450954224856349172838746660874732924946, 29738784450954224856349172838746821329132851994⟩
  | 0, 2 => ⟨89395032248059764363258452274831574918226089076, 89395032248059764363258452274832199084855726995⟩
  | 1, 1 => ⟨89513163902636625728644767431600489072472444625, 89513163902636625728644767431601619733023257978⟩
  | 0, 3 => ⟨183625060830989433728733333592887356962008624863, 183625060830989433728733333592889400527657370719⟩
  | 1, 2 => ⟨246771480411814112018139544197216182897161354014, 246771480411814112018139544197219853492221986254⟩
  | 2, 1 => ⟨247057201273685201043245495076973899259713981723, 247057201273685201043245495076980587845814630598⟩
  | 0, 4 => ⟨311993130163462548073240177833969764388207363144, 311993130163462548073240177833976755816941540156⟩
  | 1, 3 => ⟨464549292948738450890742255527673292916673914136, 464549292948738450890742255527686017076901409392⟩
  | 2, 2 => ⟨617244997336824527671950173794140737424418992641, 617244997336824527671950173794164206889084122292⟩
  | 3, 1 => ⟨617867434015929467441951749454693880919470019482, 617867434015929467441951749454737513852716051294⟩
  | 0, 5 => ⟨-1426557918951990280956159301427904307084317194893428, 1434534673561887188407055995285962745503771614081476⟩
  | 1, 4 => ⟨-2793069148436747177528697892420335531180132742752164, 2805100881509434516513324675643744911986274719565045⟩
  | 2, 3 => ⟨-5474008933555799610911526358985443216001570026451075, 5491359202023245436125553891535241131508576147375740⟩
  | 3, 2 => ⟨-10735362227103274314802714767658463865602931348705576, 10758132809432993985602544328086780601333229802667261⟩
  | 4, 1 => ⟨-21064468445611624697625841328500634002385205822147662, 21087682174070120614703651495471962536249545409032947⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0435Geometry.ds, E8TAxisProd0435Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 27932844441492197378400489290562630083915633288 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0435CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0436GraphCenterA.qJetBox,
   E8TAxisProd0436GraphCenterB.qJetBox,
   E8TAxisProd0436GraphCenterC.qJetBox,
   E8TAxisProd0436GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0436GraphWholeA.qJetBox,
   E8TAxisProd0436GraphWholeB.qJetBox,
   E8TAxisProd0436GraphWholeC.qJetBox,
   E8TAxisProd0436GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨26879569725982112821822906207625931558847414244, 26879569725982112821822906207626077721542575298⟩
  | 0, 2 => ⟨81334608495613192369084520444109663804036941356, 81334608495613192369084520444110227591549958952⟩
  | 1, 1 => ⟨81587977473518886666955263767299960620414615685, 81587977473518886666955263767300979117306338439⟩
  | 0, 3 => ⟨168314462536142269381735618266003267358116931905, 168314462536142269381735618266005107461211024450⟩
  | 1, 2 => ⟨226536427406667292794121331978443794515427248966, 226536427406667292794121331978447091864335218398⟩
  | 2, 1 => ⟨227154438938847873453902968053673669725655156569, 227154438938847873453902968053679667563662245319⟩
  | 0, 4 => ⟨288018853848230626337240170097973709127163228616, 288018853848230626337240170097979982759683916208⟩
  | 1, 3 => ⟨429651710978830558640815805366488332288422843388, 429651710978830558640815805366499728880750171043⟩
  | 2, 2 => ⟨571589121381230989050809544970454344410001614782, 571589121381230989050809544970475335888805706791⟩
  | 3, 1 => ⟨572944117560198854287193900380978377069347254877, 572944117560198854287193900381017353646022379622⟩
  | 0, 5 => ⟨-1265444750392298795020243107003476937595213445487424, 1272630297892965797858524645100605798064844050863467⟩
  | 1, 4 => ⟨-2476138627285249652826338009220094981012111282168413, 2486970259168713449112207448157868819237278794614697⟩
  | 2, 3 => ⟨-4850080658567158099892913341973821840738790777827364, 4865697438296152834050017845477738264814159323342052⟩
  | 3, 2 => ⟨-9506366117260648311607692896938626246452081852779076, 9526869037034766860189785003581036727341600159634016⟩
  | 4, 1 => ⟨-18642480915974748237861152280603328412615279537560656, 18663416338816313212772491067396785095124521504221475⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0436Geometry.ds, E8TAxisProd0436Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25235859003129687501945149842071257241347151346 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0436CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0437GraphCenterA.qJetBox,
   E8TAxisProd0437GraphCenterB.qJetBox,
   E8TAxisProd0437GraphCenterC.qJetBox,
   E8TAxisProd0437GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0437GraphWholeA.qJetBox,
   E8TAxisProd0437GraphWholeB.qJetBox,
   E8TAxisProd0437GraphWholeC.qJetBox,
   E8TAxisProd0437GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24089844019367036888325275773485912277954873131, 24089844019367036888325275773486044947937429557⟩
  | 0, 2 => ⟨73552726776942689194349832439039717446286718896, 73552726776942689194349832439040224541426603265⟩
  | 1, 1 => ⟨73784740343588120749699586535630464187370063949, 73784740343588120749699586535631377605176689423⟩
  | 0, 3 => ⟨153493588921872170376938575236071971869857388043, 153493588921872170376938575236073621423016064262⟩
  | 1, 2 => ⟨206810820098329583154735962634671614844020575795, 206810820098329583154735962634674563365436798195⟩
  | 2, 1 => ⟨207381847200681714369325383374085551728043077877, 207381847200681714369325383374090905112469868576⟩
  | 0, 4 => ⟨264720586766366228852820132112866035976813534699, 264720586766366228852820132112871639177195825006⟩
  | 1, 3 => ⟨395587442914666275581412225592361864776527222917, 395587442914666275581412225592372023598000516733⟩
  | 2, 2 => ⟨526738495000519551663875963886887992856041180148, 526738495000519551663875963886906677211789176792⟩
  | 3, 1 => ⟨527999390760722935534015776816612328728330378697, 527999390760722935534015776816646975635579005339⟩
  | 0, 5 => ⟨-1117492999532455477976616183452317821710985642132905, 1123901912146151620991424698170047820022289770663142⟩
  | 1, 4 => ⟨-2185270300606283229247485484169093030679367251295520, 2194919671409116572166562998775114730722515620693561⟩
  | 2, 3 => ⟨-4277780299335631980216611450236423538249177200040899, 4291682137163791672698512601207800520152645329124147⟩
  | 3, 2 => ⟨-8379675437045997813207249251550647884696694883165418, 8397922253541629528254747083568012089015850844416991⟩
  | 4, 1 => ⟨-16423284567506978686863424302195791401701064824492670, 16441926911056948517139315896108068497483877777937859⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0437Geometry.ds, E8TAxisProd0437Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 22605026040243755975316122975192623250914850857 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0437CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0438GraphCenterA.qJetBox,
   E8TAxisProd0438GraphCenterB.qJetBox,
   E8TAxisProd0438GraphCenterC.qJetBox,
   E8TAxisProd0438GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0438GraphWholeA.qJetBox,
   E8TAxisProd0438GraphWholeB.qJetBox,
   E8TAxisProd0438GraphWholeC.qJetBox,
   E8TAxisProd0438GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨26778032867324321930030270859842141633229822981, 26778032867324321930030270859842287494439527163⟩
  | 0, 2 => ⟨81124440291363546865792174828659471508943464815, 81124440291363546865792174828660034056659030665⟩
  | 1, 1 => ⟨81305142385573476730770961147909717460266704030, 81305142385573476730770961147910733689046650500⟩
  | 0, 3 => ⟨167954776862729985096177247696763839798102962773, 167954776862729985096177247696765675804482660474⟩
  | 1, 2 => ⟨225999888498561791090514387206495160807129267148, 225999888498561791090514387206498450740915044061⟩
  | 2, 1 => ⟨226440720674384574557628522432355840917688395065, 226440720674384574557628522432361825147008410378⟩
  | 0, 4 => ⟨287478376514821192388243863018750094277216081612, 287478376514821192388243863018756353490036256268⟩
  | 1, 3 => ⟨428810786587510672822216320396563641008561562021, 428810786587510672822216320396575011296535057064⟩
  | 2, 2 => ⟨570360473012552117911188861297200043658222973742, 570360473012552117911188861297220986456452387966⟩
  | 3, 1 => ⟨571327117262603629983527235575063145180451290130, 571327117262603629983527235575102030877135152317⟩
  | 0, 5 => ⟨-1262230210178196059465744972844153459637184914738730, 1269399162895382260083176454447986545738255704053637⟩
  | 1, 4 => ⟨-2469823066147681061539210134157826660362678695937612, 2480629201298576955298672207098500645795077333089957⟩
  | 2, 3 => ⟨-4837659600839694475490440287210878520509133991600956, 4853238657939789856798156752082189642952700592139404⟩
  | 3, 2 => ⟨-9481919513121735377724277474283253413980332128013527, 9502370249394657527104419449983918512436308036135072⟩
  | 4, 1 => ⟨-18594339324632150217819853990533238034697766417169464, 18615212441474061346667145185697399411135587952651481⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0438Geometry.ds, E8TAxisProd0438Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25139883286743485768908438362276096974345829824 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0438CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0439GraphCenterA.qJetBox,
   E8TAxisProd0439GraphCenterB.qJetBox,
   E8TAxisProd0439GraphCenterC.qJetBox,
   E8TAxisProd0439GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0439GraphWholeA.qJetBox,
   E8TAxisProd0439GraphWholeB.qJetBox,
   E8TAxisProd0439GraphWholeC.qJetBox,
   E8TAxisProd0439GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨23998022941630832649041844874187170602483972760, 23998022941630832649041844874187302999435252497⟩
  | 0, 2 => ⟨73361066473536115939966653538723838409691290056, 73361066473536115939966653538724344388552559504⟩
  | 1, 1 => ⟨73526535668160293493384648128196106844665993500, 73526535668160293493384648128197018224659186090⟩
  | 0, 3 => ⟨153163000654439728585456464746549594141804287726, 153163000654439728585456464746551240016273021552⟩
  | 1, 2 => ⟨206316822910939308543405394919931394109686174637, 206316822910939308543405394919934335984949529238⟩
  | 2, 1 => ⟨206724136770637120940616175961202965397855307088, 206724136770637120940616175961208306601492027979⟩
  | 0, 4 => ⟨264220782929493480976761709502438622962819706533, 264220782929493480976761709502444213253128324416⟩
  | 1, 3 => ⟨394808284100097743577960263261443425724384800953, 394808284100097743577960263261453561030774563404⟩
  | 2, 2 => ⟨525598538258370082524564133189809853222148860899, 525598538258370082524564133189828494105308266553⟩
  | 3, 1 => ⟨526498050345852566480530531762280432055030862728, 526498050345852566480530531762314997880208779386⟩
  | 0, 5 => ⟨-1114720967170647603360503774643671312258458193897735, 1121114814778421083578684958915671144957300795264657⟩
  | 1, 4 => ⟨-2179827386600467071981964786070404574947480844896536, 2189453706802308456268657435838049447408528065001083⟩
  | 2, 3 => ⟨-4267081281103527903472484894244631258250360554091243, 4280949262662060031739349318466758863758878682902646⟩
  | 3, 2 => ⟨-8358628630729485025350415445788139694361071224069406, 8376829263584936235587039864300972264337401275813569⟩
  | 4, 1 => ⟨-16381857691771875759554278716229021424315063274540860, 16400446710151516036097298215259352674599379034808952⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0439Geometry.ds, E8TAxisProd0439Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 22518270994299582549561700012305028364491316043 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0439CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0440GraphCenterA.qJetBox,
   E8TAxisProd0440GraphCenterB.qJetBox,
   E8TAxisProd0440GraphCenterC.qJetBox,
   E8TAxisProd0440GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0440GraphWholeA.qJetBox,
   E8TAxisProd0440GraphWholeB.qJetBox,
   E8TAxisProd0440GraphWholeC.qJetBox,
   E8TAxisProd0440GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21568120272258136331225870688718358034399234350, 21568120272258136331225870688718478532121215461⟩
  | 0, 2 => ⟨66451475471752115982275144366001046044356750434, 66451475471752115982275144366001502239637741539⟩
  | 1, 1 => ⟨66663762767260419722344957464912228746436076501, 66663762767260419722344957464913047976517585944⟩
  | 0, 3 => ⟨139852123667273342010274738333074851504491677590, 139852123667273342010274738333076330298114100499⟩
  | 1, 2 => ⟨188638629057005548519197905480349329853537723335, 188638629057005548519197905480351966258764226353⟩
  | 2, 1 => ⟨189165937086608558119133643476306620165198879974, 189165937086608558119133643476311397725404062293⟩
  | 0, 4 => ⟨243136444224116448656377235613117040083567607891, 243136444224116448656377235613122044106205965478⟩
  | 1, 3 => ⟨363985502164173503937523069648327050008856256878, 363985502164173503937523069648336103919736676962⟩
  | 2, 2 => ⟨485099762444662438673903789076561622437357741564, 485099762444662438673903789076578249481993773145⟩
  | 3, 1 => ⟨486272954946660781029110173075858004732471029083, 486272954946660781029110173075888794838937664353⟩
  | 0, 5 => ⟨-988608422070110278380062823535692150755667627729868, 994310656888067891490238762744030626203843562437697⟩
  | 1, 4 => ⟨-1932029204526539602531083066063141490906645647702986, 1940602340973721289790705061242138764928839324831388⟩
  | 2, 3 => ⟨-3779777060841295829781071286141867026883566759970669, 3792116531294450829447963449004167208220055001107184⟩
  | 3, 2 => ⟨-7399753848348418798822783828175848849265765342674902, 7415942110299479802115095883897187755209658156732732⟩
  | 4, 1 => ⟨-14494132725117572273099801917994803373235279612068555, 14510673516051427466654815158017600165017849948433082⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0440Geometry.ds, E8TAxisProd0440Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20227885970682497479523813003176649823960013682 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0440CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0441GraphCenterA.qJetBox,
   E8TAxisProd0441GraphCenterB.qJetBox,
   E8TAxisProd0441GraphCenterC.qJetBox,
   E8TAxisProd0441GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0441GraphWholeA.qJetBox,
   E8TAxisProd0441GraphWholeB.qJetBox,
   E8TAxisProd0441GraphWholeC.qJetBox,
   E8TAxisProd0441GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19290860556454318276155935420446186423478225688, 19290860556454318276155935420446295935610261618⟩
  | 0, 2 => ⟨59977054117910447416308568476002207009462467637, 59977054117910447416308568476002617498472669147⟩
  | 1, 1 => ⟨60171130963704140664480947845322988932384663276, 60171130963704140664480947845323723732016481106⟩
  | 0, 3 => ⟨127304688106154960547332424110175392471076096213, 127304688106154960547332424110176718223169897176⟩
  | 1, 2 => ⟨171908463417547315302517802397660288116861419770, 171908463417547315302517802397662645247619343245⟩
  | 2, 1 => ⟨172395096209990076422530833440704025561981814406, 172395096209990076422530833440708288632745128114⟩
  | 0, 4 => ⟨223146150665063711968043855606023580094587518674, 223146150665063711968043855606028048563891983985⟩
  | 1, 3 => ⟨334674850072590646182591248980780728128325104715, 334674850072590646182591248980788795699479116846⟩
  | 2, 2 => ⟨446451021078682710643664609269580189840497617155, 446451021078682710643664609269594982372545704502⟩
  | 3, 1 => ⟨447542446553581148597600563083824847818039262307, 447542446553581148597600563083852202516714710573⟩
  | 0, 5 => ⟨-872725803374990699688772839859949186497667062043321, 877797557080839827613574289210681211323904464973466⟩
  | 1, 4 => ⟨-1704444612382356088573755823656046333502703521532969, 1712058613738230187424909898026278826853672241559698⟩
  | 2, 3 => ⟨-3332441202396342134370987313909509382852860240769850, 3343389149669305958625681995924206981652518320070241⟩
  | 3, 2 => ⟨-6519951664899530027907179693685948088148046391148938, 6534306236886652950430575783736206746160075096290923⟩
  | 4, 1 => ⟨-12762920032072195136770699244268027293169756110497992, 12777585403432773632783058058240165347329580594300379⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0441Geometry.ds, E8TAxisProd0441Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18082351636107979335913114174558058510275782246 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0441CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0442GraphCenterA.qJetBox,
   E8TAxisProd0442GraphCenterB.qJetBox,
   E8TAxisProd0442GraphCenterC.qJetBox,
   E8TAxisProd0442GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0442GraphWholeA.qJetBox,
   E8TAxisProd0442GraphWholeB.qJetBox,
   E8TAxisProd0442GraphWholeC.qJetBox,
   E8TAxisProd0442GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21485165108281702354736688805775336762204428641, 21485165108281702354736688805775457012723111626⟩
  | 0, 2 => ⟨66276850147144393561476438841211389856704281340, 66276850147144393561476438841211845047503098502⟩
  | 1, 1 => ⟨66428248656580115364646675327234477249891634604, 66428248656580115364646675327235294649822774935⟩
  | 0, 3 => ⟨139548491960531140727520742416149769544217368274, 139548491960531140727520742416151245036750859603⟩
  | 1, 2 => ⟨188184098391620776846136575108443798442404200807, 188184098391620776846136575108446428893590389711⟩
  | 2, 1 => ⟨188560223478624666371123059445334379048523436385, 188560223478624666371123059445339145709869601927⟩
  | 0, 4 => ⟨242674418050033262825154434283197348585962334710, 242674418050033262825154434283202341057786959405⟩
  | 1, 3 => ⟨363263773460694162021716676380548780516431505719, 363263773460694162021716676380557813415576570794⟩
  | 2, 2 => ⟨484042331295492820058050217360600032895394818349, 484042331295492820058050217360616621131239146441⟩
  | 3, 1 => ⟨484879274701011964701314960376070958201378999596, 484879274701011964701314960376101675985612409333⟩
  | 0, 5 => ⟨-986155759685130798041858080882288454944281113614009, 991844737532163771020718549244259171020907671910813⟩
  | 1, 4 => ⟨-1927215509684088260926848920039897331344973631337973, 1935768456017475838827049088623646529807681358984139⟩
  | 2, 3 => ⟨-3770318755547946472086089197929594675279551179905579, 3782628759080421407212253792499984498488628020819277⟩
  | 3, 2 => ⟨-7381154971826294444147199100182340647912612647955945, 7397303450886881703898941636793449057763362832187780⟩
  | 4, 1 => ⟨-14457537913339009307929604451229169568553893671625005, 14474033824676566003740379708515249858125213425426545⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0442Geometry.ds, E8TAxisProd0442Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20149546966447160973030170366162002585475809967 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0442CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0443GraphCenterA.qJetBox,
   E8TAxisProd0443GraphCenterB.qJetBox,
   E8TAxisProd0443GraphCenterC.qJetBox,
   E8TAxisProd0443GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0443GraphWholeA.qJetBox,
   E8TAxisProd0443GraphWholeB.qJetBox,
   E8TAxisProd0443GraphWholeC.qJetBox,
   E8TAxisProd0443GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19215988622990554528297486251527545804859623695, 19215988622990554528297486251527655092936655648⟩
  | 0, 2 => ⟨59818097479478134972395893713394852314789494443, 59818097479478134972395893713395261899197071679⟩
  | 1, 1 => ⟨59956506675038930078114763830591330018817545330, 59956506675038930078114763830592063174114348973⟩
  | 0, 3 => ⟨127026022331305354305016482603479495239422967757, 127026022331305354305016482603480818027035012463⟩
  | 1, 2 => ⟨171490537681453692221199915695194556611695437032, 171490537681453692221199915695196908406268352151⟩
  | 2, 1 => ⟨171837645515233165587900070245122200244225300583, 171837645515233165587900070245126453561237683825⟩
  | 0, 4 => ⟨222719210995855063729644427243675335959549758425, 222719210995855063729644427243679794086983074603⟩
  | 1, 3 => ⟨334006523652936260986913181834462619243137922137, 334006523652936260986913181834470668032304921918⟩
  | 2, 2 => ⟨445470389001125878964711498931082224960364680303, 445470389001125878964711498931096982840702753004⟩
  | 3, 1 => ⟨446248998360384288350516128912697339447309554030, 446248998360384288350516128912724629633367877160⟩
  | 0, 5 => ⟨-870496518553904184265187928856624962749328921181033, 875556593506411156408676970335809074859998098029124⟩
  | 1, 4 => ⟨-1700070979508645260425322381067898830351095048582886, 1707667262088068025826116964088152476905233756125487⟩
  | 2, 3 => ⟨-3323850876757782164367167241846179444756449272034718, 3334773104952885526722659663343738417514554704584249⟩
  | 3, 2 => ⟨-6503066237483324759879761245982931385639616974458499, 6517386413858594330096788623881172382586435853622311⟩
  | 4, 1 => ⟨-12729709909217553202800374441731119143898024212784620, 12744337364737437797773427862874337370615623637395568⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0443Geometry.ds, E8TAxisProd0443Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18011686594265359391493901357078529828674922088 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0443CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0444GraphCenterA.qJetBox,
   E8TAxisProd0444GraphCenterB.qJetBox,
   E8TAxisProd0444GraphCenterC.qJetBox,
   E8TAxisProd0444GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0444GraphWholeA.qJetBox,
   E8TAxisProd0444GraphWholeB.qJetBox,
   E8TAxisProd0444GraphWholeC.qJetBox,
   E8TAxisProd0444GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨26676758438093272737358257007181459442586608902, 26676758438093272737358257007181605002930358521⟩
  | 0, 2 => ⟨80914721272196567626959180867841797169771524586, 80914721272196567626959180867842358480352735235⟩
  | 1, 1 => ⟨81022977314673045314653982108937681718614356180, 81022977314673045314653982108938695684182420067⟩
  | 0, 3 => ⟨167595766212897261945112966857048157203415780697, 167595766212897261945112966857049989122051203632⟩
  | 1, 2 => ⟨225464399829204779798256328054120462117239578915, 225464399829204779798256328054123744652186917731⟩
  | 2, 1 => ⟨225728536828969525259008891023972488865432245552, 225728536828969525259008891023978459516022998921⟩
  | 0, 4 => ⟨286938815880570360811554538008690641242182691445, 286938815880570360811554538008696886067747058834⟩
  | 1, 3 => ⟨427971328581280160077122919292921221269672995495, 427971328581280160077122919292932565312469473865⟩
  | 2, 2 => ⟨569134050276797987277842784112268328320375869020, 569134050276797987277842784112289222547515272917⟩
  | 3, 1 => ⟨569713311663873020047683924814731781536578814269, 569713311663873020047683924814770576557708994795⟩
  | 0, 5 => ⟨-1259022112785838326984694849566125057417665206698348, 1266177615273679917947232247821281718690420890798726⟩
  | 1, 4 => ⟨-2463520186677349435865379618204492297834995360955688, 2474304616197103771206804355918374797968601048598149⟩
  | 2, 3 => ⟨-4825263535352340988246430692778702297571068060889698, 4840808703428962492718710834479541253127728306457584⟩
  | 3, 2 => ⟨-9457522202987899823091696199285417275579493145716977, 9477923419651102785225515949917899377094423430110153⟩
  | 4, 1 => ⟨-18546295019584199512444424263193979400571716794811235, 18567106136738781939218427843254885044130078340723488⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0444Geometry.ds, E8TAxisProd0444Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25044156960480968152070392036291359306652282521 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0444CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0445GraphCenterA.qJetBox,
   E8TAxisProd0445GraphCenterB.qJetBox,
   E8TAxisProd0445GraphCenterC.qJetBox,
   E8TAxisProd0445GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0445GraphWholeA.qJetBox,
   E8TAxisProd0445GraphWholeB.qJetBox,
   E8TAxisProd0445GraphWholeC.qJetBox,
   E8TAxisProd0445GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨23906441181164430037821680920999444856721350931, 23906441181164430037821680920999576981201600931⟩
  | 0, 2 => ⟨73169819015213567080283794660978240632174110350, 73169819015213567080283794660978745497156474788⟩
  | 1, 1 => ⟨73268947880853719762130447049513529767938866000, 73268947880853719762130447049514439114527267949⟩
  | 0, 3 => ⟨152833036610317827802963897791365661278791687811, 152833036610317827802963897791367303482633042853⟩
  | 1, 2 => ⟨205823798820568523469418182674882588715263259686, 205823798820568523469418182674885523958989037860⟩
  | 2, 1 => ⟨206067849992796181183521409712647323620808454390, 206067849992796181183521409712652652670516346051⟩
  | 0, 4 => ⟨263721829246145554664374943213425441214452323392, 263721829246145554664374943213431018623766339704⟩
  | 1, 3 => ⟨394030487311600474406983948992835894747908532139, 394030487311600474406983948992846006592186759557⟩
  | 2, 2 => ⟨524460650891468824017506669891212965688500173792, 524460650891468824017506669891231563196993180605⟩
  | 3, 1 => ⟨524999682367902825842492620320925905610108326046, 524999682367902825842492620320960390535935834744⟩
  | 0, 5 => ⟨-1111954255073966798036751463918761523912102248776427, 1118336443047682398617277821421819230077186078223663⟩
  | 1, 4 => ⟨-2174394936929226254105789279192179702148169955898014, 2184002309512783671737022069327425999411803921834277⟩
  | 2, 3 => ⟨-4256402872821305805106493976748517732329953673952347, 4270241139603963986745155476111684333151553530151982⟩
  | 3, 2 => ⟨-8337622453923349528230250368724984002622383156875172, 8355779758403326154417649345004168842654610071249372⟩
  | 4, 1 => ⟨-16340510966059424273367759849480670694072203867315076, 16359046914433398778687179306378219285709559627913754⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0445Geometry.ds, E8TAxisProd0445Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 22431743302591877336703634182182704324790034558 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0445CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0446GraphCenterA.qJetBox,
   E8TAxisProd0446GraphCenterB.qJetBox,
   E8TAxisProd0446GraphCenterC.qJetBox,
   E8TAxisProd0446GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0446GraphWholeA.qJetBox,
   E8TAxisProd0446GraphWholeB.qJetBox,
   E8TAxisProd0446GraphWholeC.qJetBox,
   E8TAxisProd0446GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21402427988899092101947225309385588855588674213, 21402427988899092101947225309385708859410323533⟩
  | 0, 2 => ⟨66102604001417517191389573588081371707791598162, 66102604001417517191389573588081825896268465175⟩
  | 1, 1 => ⟨66193302145710559264156731008911252400903540053, 66193302145710559264156731008912067974648571314⟩
  | 0, 3 => ⟨139245437293691050512585001637761984795968335847, 139245437293691050512585001637763456994651739649⟩
  | 1, 2 => ⟨187730469096262838531747572676921932769417070625, 187730469096262838531747572676924557279671561895⟩
  | 2, 1 => ⟨187955830456632696096633708874523784873488468900, 187955830456632696096633708874528540660049917655⟩
  | 0, 4 => ⟨242213180173309503445187710582966134745063982164, 242213180173309503445187710582971115692109603698⟩
  | 1, 3 => ⟨362543309775660981811499731632274198705139097671, 362543309775660981811499731632283210639935860160⟩
  | 2, 2 => ⟨482986824315612140289872109306463651875995523923, 482986824315612140289872109306480201390596391183⟩
  | 3, 1 => ⟨483488360422198779268244012111084054084465177461, 483488360422198779268244012111114699709742968172⟩
  | 0, 5 => ⟨-983707816149498166977917888835226023173615474236793, 989386998103210319858978659440343586705924771930538⟩
  | 1, 4 => ⟨-1922411093676015118808779149790500480881303563323025, 1930948016460014433102826698346455314489823569409252⟩
  | 2, 3 => ⟨-3760878721154026829545461815290237585612793293915566, 3773163454249064181809542017728636593078802489752512⟩
  | 3, 2 => ⟨-7362592106768311899897940780839932276999704210220752, 7378703670868988855361887921898891976950539640843074⟩
  | 4, 1 => ⟨-14421014129644772965900135309875993242400981803948761, 14437465341516491125253142736058792009125549893704487⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0446Geometry.ds, E8TAxisProd0446Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20071415010936196606432091196011258070764941997 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0446CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0447GraphCenterA.qJetBox,
   E8TAxisProd0447GraphCenterB.qJetBox,
   E8TAxisProd0447GraphCenterC.qJetBox,
   E8TAxisProd0447GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0447GraphWholeA.qJetBox,
   E8TAxisProd0447GraphWholeB.qJetBox,
   E8TAxisProd0447GraphWholeC.qJetBox,
   E8TAxisProd0447GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19141315167756112823210554699496964523919992209, 19141315167756112823210554699497073588400149677⟩
  | 0, 2 => ⟨59659488839908163905754472867744058987413598689, 59659488839908163905754472867744467669165698248⟩
  | 1, 1 => ⟨59742404271719907821064600727703218180708144835, 59742404271719907821064600727703949695237348842⟩
  | 0, 3 => ⟨126747889774152179372633695413178601023125029271, 126747889774152179372633695413179920852763279248⟩
  | 1, 2 => ⟨171073446618876981262904803694249641509543930921, 171073446618876981262904803694251987979698845918⟩
  | 2, 1 => ⟨171281419491944852728497890884650206241423144679, 171281419491944852728497890884654449826272116681⟩
  | 0, 4 => ⟨222293002158246369240445381866933949751524263964, 222293002158246369240445381866938397560427399571⟩
  | 1, 3 => ⟨333339372124566232846667326429848037947738651554, 333339372124566232846667326429856067997346765990⟩
  | 2, 2 => ⟨444491546225516185486180953959243416419953226955, 444491546225516185486180953959258139726899509168⟩
  | 3, 1 => ⟨444958124430167960782516280387397938811437458568, 444958124430167960782516280387425164630838432349⟩
  | 0, 5 => ⟨-868271713265914752395095797741294023203602367177883, 873323556573558098093885904893771651014423045628282⟩
  | 1, 4 => ⟨-1695706154701874938166936292968885103070917174200809, 1703288866072322408259927494792667852815320773360395⟩
  | 2, 3 => ⟨-3315277893576067926266262257347883410411348215544438, 3326178574966279445813651783852981081006156535595001⟩
  | 3, 2 => ⟨-6486214987377248735680546097712819177718650124645718, 6500503607109169219580266596700354175182239866874067⟩
  | 4, 1 => ⟨-12696567186692459428338311759160729143452994435279051, 12711156871496569284057865447065067842408274894546525⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0447Geometry.ds, E8TAxisProd0447Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 17941209909209342812770997191705713972802055694 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0447CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0448GraphCenterA.qJetBox,
   E8TAxisProd0448GraphCenterB.qJetBox,
   E8TAxisProd0448GraphCenterC.qJetBox,
   E8TAxisProd0448GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0448GraphWholeA.qJetBox,
   E8TAxisProd0448GraphWholeB.qJetBox,
   E8TAxisProd0448GraphWholeC.qJetBox,
   E8TAxisProd0448GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨18060727076575914401592438351247124526218577200, 18060727076575914401592438351247226589803927649⟩
  | 0, 2 => ⟨55839303275733587340003665249604714440653159965, 55839303275733587340003665249605093794648356911⟩
  | 1, 1 => ⟨56639424890023305780999446763298224914317687763, 56639424890023305780999446763298902006512584056⟩
  | 0, 3 => ⟨118877165649440487843033751823361415653967305256, 118877165649440487843033751823362636633795752850⟩
  | 1, 2 => ⟨161185192457401733376904091125472746024620802312, 161185192457401733376904091125474911478058228560⟩
  | 2, 1 => ⟨163206709382642451722758322471749081077600492397, 163206709382642451722758322471752990738884433150⟩
  | 0, 4 => ⟨209423460622602159656600968550679314778611781966, 209423460622602159656600968550683417266303094338⟩
  | 1, 3 => ⟨315006416050805949245116097644034338733819647009, 315006416050805949245116097644041730230957321554⟩
  | 2, 2 => ⟨421626882672434549588996027180733722442299081245, 421626882672434549588996027180747255939941310826⟩
  | 3, 1 => ⟨426191209539428001320506610021054162148299697631, 426191209539428001320506610021079157747064055617⟩
  | 0, 5 => ⟨-791905940227641701524441858164231848751253760568784, 796540599188270510347938666543618532877720758248446⟩
  | 1, 4 => ⟨-1545749706577862277789647328778833443154025202388761, 1552698791194220188870554811577665017221295282777059⟩
  | 2, 3 => ⟨-3020604148495890294198226607117450235669047677294291, 3030587671452798354192200044227888304899823133948459⟩
  | 3, 2 => ⟨-5906864191538204987339136807448749544161871986352728, 5919952180290885372604813418538903148154900970647931⟩
  | 4, 1 => ⟨-11557020714239396236911405715683097190910200969557030, 11570415728429343583746062207542955704978205399860073⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0448Geometry.ds, E8TAxisProd0448Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16925518089168027026284977349374332567471610033 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0448CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0449GraphCenterA.qJetBox,
   E8TAxisProd0449GraphCenterB.qJetBox,
   E8TAxisProd0449GraphCenterC.qJetBox,
   E8TAxisProd0449GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0449GraphWholeA.qJetBox,
   E8TAxisProd0449GraphWholeB.qJetBox,
   E8TAxisProd0449GraphWholeC.qJetBox,
   E8TAxisProd0449GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨16127409992171243893842607415568641986372736108, 16127409992171243893842607415568734861420004656⟩
  | 0, 2 => ⟨50311503082026830675650914837635275628812904480, 50311503082026830675650914837635617129564327729⟩
  | 1, 1 => ⟨51041853846751414652838566480306160545838353479, 51041853846751414652838566480306767963088295165⟩
  | 0, 3 => ⟨108025236422549307697239108285096756096587128600, 108025236422549307697239108285097850814207902967⟩
  | 1, 2 => ⟨146653010108809283141256598433333722037128029520, 146653010108809283141256598433335657855000666262⟩
  | 2, 1 => ⟨148516307330699294603508370425504175684527942790, 148516307330699294603508370425507663516766163231⟩
  | 0, 4 => ⟨191926636354229654988697565398509975645962299023, 191926636354229654988697565398513638393163333201⟩
  | 1, 3 => ⟨289252937342943655435575644765228381368298892166, 289252937342943655435575644765234965161467504350⟩
  | 2, 2 => ⟨387547224441848515531111754320840897715425644461, 387547224441848515531111754320852932346413331321⟩
  | 3, 1 => ⟨391791852909656627240596711945323110457449764792, 391791852909656627240596711945345305246355592414⟩
  | 0, 5 => ⟨-694155904169856231070648765443146552430651539866188, 698270862384038910945300463344610035024773601865730⟩
  | 1, 4 => ⟨-1353950366781931386815153579254098985670291239792597, 1360110123651435577658709495291730984973063075819010⟩
  | 2, 3 => ⟨-2643952927923242523122558113145062099126708297121532, 2652792204440655642019504003767551988207805275563680⟩
  | 3, 2 => ⟨-5166772980594623046529891244992816675350997454570517, 5178352117136030260966565764990932115129299057837897⟩
  | 4, 1 => ⟨-10102108977960289240456205650401201795096910200734866, 10113953346840201550346624753549329506689671523131286⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0449Geometry.ds, E8TAxisProd0449Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 15105597613057860067723554400955291514439439745 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0449CertifiedArithmetic

end


