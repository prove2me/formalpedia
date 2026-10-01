-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:43:59.408589+00:00
-- url     : https://prove2.me/theorems/b96c3d8d-4890-4ece-bb51-ec181be5bebd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 1 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 1 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 1 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0078CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0081CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0082CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0083CertifiedArithmetic) (piece 1 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0058GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0047GraphWholeD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0056Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0063GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0067GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0069GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0069GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0071GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0071GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0075GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0076GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0077GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0077Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0083GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0083GraphWholeA__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0062GraphCenterA.qJetBox,
   E8TAxisProd0062GraphCenterB.qJetBox,
   E8TAxisProd0062GraphCenterC.qJetBox,
   E8TAxisProd0062GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0062GraphWholeA.qJetBox,
   E8TAxisProd0062GraphWholeB.qJetBox,
   E8TAxisProd0062GraphWholeC.qJetBox,
   E8TAxisProd0062GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9038716310474412169375306604178468432709711, 9038716310474412169375306604181490059665188⟩
  | 0, 2 => ⟨59368230728532416170930070274497389949845594, 59368230728532416170930070274504073036100968⟩
  | 1, 1 => ⟨61494611435016558888514143823179560303835782, 61494611435016558888514143823188051184542495⟩
  | 0, 3 => ⟨217147266506582966781437833932035946771641081, 217147266506582966781437833932050149926740985⟩
  | 1, 2 => ⟨343516308411952767729113365983133024750844626, 343516308411952767729113365983150772275669104⟩
  | 2, 1 => ⟨353281967652800943676071140463018875763524814, 353281967652800943676071140463044967901094098⟩
  | 0, 4 => ⟨518538622526615932430254816692115268795567925, 518538622526615932430254816692153154824787827⟩
  | 1, 3 => ⟨1082069805001369824280812182285976630616916744, 1082069805001369824280812182286025362774480158⟩
  | 2, 2 => ⟨1658407331145116353319978823737661808179097521, 1658407331145116353319978823737734946674478122⟩
  | 3, 1 => ⟨1695055891019274964242093591403937320872773190, 1695055891019274964242093591404054982506560634⟩
  | 0, 5 => ⟨-6431801804257233768881380573038019017749363821528, 6462455730453252309384292798391048266323236888733⟩
  | 1, 4 => ⟨-11591912746011106449147672461295223425776211582123, 11597735115302211407066057408657080328985682200684⟩
  | 2, 3 => ⟨-21090014539814900426263862406879526193419902431338, 21063792349716191260534440545475151260252415830311⟩
  | 3, 2 => ⟨-38464821756666292102723835499136247095857790385026, 38409076871756878051596718127934419555688190710223⟩
  | 4, 1 => ⟨-70084631213868101189218805510364802696333723797180, 70038494610487817154790298662568258370078199064859⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0062Geometry.ds, E8TAxisProd0062Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3450665738580052301754893478631981833121267 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic

end


