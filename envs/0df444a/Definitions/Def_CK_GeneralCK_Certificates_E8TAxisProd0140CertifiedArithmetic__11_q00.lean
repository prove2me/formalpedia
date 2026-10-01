-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0140CertifiedArithmetic__11_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0140CertifiedArithmetic__11_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:53:45.674694+00:00
-- url     : https://prove2.me/theorems/987609ec-08d4-48e4-9274-e2dc369af06d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0141CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0141CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0142CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0143CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0144CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0145CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0146CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0147CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0148CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0149CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0150CertifiedArithmetic) (piece 1 of 11)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0141CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0142CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0143CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0144CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0145CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0146CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0147CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0148CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0149CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0150CertifiedArithmetic) (piece 1 of 11)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0141CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0142CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0143CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0144CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0145CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0146CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0147CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0148CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0149CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0150CertifiedArithmetic) (piece 1 of 11) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0140CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0141CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0142CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0143CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0144CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0145CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0146CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0147CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0148CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0149CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0150CertifiedArithmetic) (piece 1 of 11).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0133GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0136GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0125GraphWholeA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0137GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0136GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0140GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0123Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0142Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0143GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0150GraphCenterB__14

-- ===== source module GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0140GraphCenterA.qJetBox,
   E8TAxisProd0140GraphCenterB.qJetBox,
   E8TAxisProd0140GraphCenterC.qJetBox,
   E8TAxisProd0140GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0140GraphWholeA.qJetBox,
   E8TAxisProd0140GraphWholeB.qJetBox,
   E8TAxisProd0140GraphWholeC.qJetBox,
   E8TAxisProd0140GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨915497099720755760976562819561038328544825375, 915497099720755760976562819561052576186402677⟩
  | 0, 2 => ⟨3584902820881201554177961284998641024645517147, 3584902820881201554177961284998679003219411566⟩
  | 1, 1 => ⟨3617662178721213636954663695800994804112301672, 3617662178721213636954663695801054288095035836⟩
  | 0, 3 => ⟨9225851355886108544967902908076902735243849141, 9225851355886108544967902908077009193598432504⟩
  | 1, 2 => ⟨13021703381265091712473649383655939394285931421, 13021703381265091712473649383656108033189445033⟩
  | 2, 1 => ⟨13125556414393927303488736371223121397377707115, 13125556414393927303488736371223406153331478483⟩
  | 0, 4 => ⟨19662141379892470258379338280076682532245438357, 19662141379892470258379338280077001960096282279⟩
  | 1, 3 => ⟨31606876579716629206559696467661061743731621081, 31606876579716629206559696467661584684067368532⟩
  | 2, 2 => ⟨43628150815161223079257388167468362194997100027, 43628150815161223079257388167469265334243099580⟩
  | 3, 1 => ⟨43932796111154055196746302238130745913905759741, 43932796111154055196746302238132337799874541796⟩
  | 0, 5 => ⟨-178240793258993186761366783860972581478934965737662, 179487771168248792178833730080000681557720322854849⟩
  | 1, 4 => ⟨-343391447742289061199503009268662238822003722468859, 345169730847241266032651246276525240774715433628340⟩
  | 2, 3 => ⟨-662867583710371176426272248256366509126127802173462, 665350360944292886743381335584334008993674754926137⟩
  | 3, 2 => ⟨-1280780136466887343216353807482798603580787487840090, 1284004696929960530236311735541683455047079903172216⟩
  | 4, 1 => ⟨-2475836685728967102218469202871272662179538210055404, 2479216750835406906349345523433209033118323114836470⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0140Geometry.ds, E8TAxisProd0140Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 683852291672320758338158928755895545096013495 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0140CertifiedArithmetic

end


