-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:25:00.925485+00:00
-- url     : https://prove2.me/theorems/35bdadd5-4f91-4930-9d74-b6bbec17e810
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 13 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 13 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 13 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0078CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0081CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0082CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0083CertifiedArithmetic) (piece 13 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0076GraphCenterA.qJetBox,
   E8TAxisProd0076GraphCenterB.qJetBox,
   E8TAxisProd0076GraphCenterC.qJetBox,
   E8TAxisProd0076GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0076GraphWholeA.qJetBox,
   E8TAxisProd0076GraphWholeB.qJetBox,
   E8TAxisProd0076GraphWholeC.qJetBox,
   E8TAxisProd0076GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1071883116065999304548572127814433722180895, 1071883116065999304548572127816375734617314⟩
  | 0, 2 => ⟨9877583878657488891713056862351661507349247, 9877583878657488891713056862356318312885773⟩
  | 1, 1 => ⟨10437927373593425725625279510940169285808987, 10437927373593425725625279510945867468102585⟩
  | 0, 3 => ⟨48369589708802959861935314934595236292996294, 48369589708802959861935314934603998012758643⟩
  | 1, 2 => ⟨79989349110693362774207250817581237908967100, 79989349110693362774207250817591444201061959⟩
  | 2, 1 => ⟨83491891585701566093994648035074431135740403, 83491891585701566093994648035088539671632367⟩
  | 0, 4 => ⟨130949875832528881852788093761956534888550166, 130949875832528881852788093761980316861969588⟩
  | 1, 3 => ⟨319169252194809235522854398582626981596292093, 319169252194809235522854398582655171611490832⟩
  | 2, 2 => ⟨514116449917378861503843597322555271050678612, 514116449917378861503843597322594966524690947⟩
  | 3, 1 => ⟨530468214085399760668616959938081592511040151, 530468214085399760668616959938143393782024039⟩
  | 0, 5 => ⟨-514658455000763738714491131251101308451263354026, 520981724886032805728340903981458279987969210488⟩
  | 1, 4 => ⟨-860272187898895222186591261814533847895262230677, 861289477810282421641266440100260209396616509073⟩
  | 2, 3 => ⟨-1471961867096450270567114658303578876786620684306, 1466491339714272621786271180798470141387018646655⟩
  | 3, 2 => ⟨-2532145699450060664975743097008122962788869003468, 2520469511976800445689553918130189913913060421076⟩
  | 4, 1 => ⟨-4338543347569866991515094222153836711317907692499, 4327765426868267492377077237832578581755992151860⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0076Geometry.ds, E8TAxisProd0076Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 871299841178077168956234355587207393024133 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic

end


