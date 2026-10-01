-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:10:21.908708+00:00
-- url     : https://prove2.me/theorems/e0599087-d714-48d7-aea8-569e3b8809a5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 17 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 17 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 17 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0078CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0081CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0082CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0083CertifiedArithmetic) (piece 17 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0082GraphCenterA.qJetBox,
   E8TAxisProd0082GraphCenterB.qJetBox,
   E8TAxisProd0082GraphCenterC.qJetBox,
   E8TAxisProd0082GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0082GraphWholeA.qJetBox,
   E8TAxisProd0082GraphWholeB.qJetBox,
   E8TAxisProd0082GraphWholeC.qJetBox,
   E8TAxisProd0082GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1023097094783818250703309470479934915413749, 1023097094783818250703309470481861992085097⟩
  | 0, 2 => ⟨9637367717113504380402350496303037918386630, 9637367717113504380402350496307668002964420⟩
  | 1, 1 => ⟨10041954498671822890940223575658843444866620, 10041954498671822890940223575664509903002831⟩
  | 0, 3 => ⟨47717888920414478685215061262084109786703600, 47717888920414478685215061262092802717762633⟩
  | 1, 2 => ⟨78402941542555144065458292504592193578079023, 78402941542555144065458292504602317573055765⟩
  | 2, 1 => ⟨80941721150780008502212584685875680692705637, 80941721150780008502212584685889669534581964⟩
  | 0, 4 => ⟨129733059729596975488021398878445859675352690, 129733059729596975488021398878469472735461840⟩
  | 1, 3 => ⟨315400423305966786792631353024250947382184104, 315400423305966786792631353024278930769911704⟩
  | 2, 2 => ⟨505966670630728237960610469069352346814203838, 505966670630728237960610469069391726653811908⟩
  | 3, 1 => ⟨517855430643929477620649949539096776569612704, 517855430643929477620649949539158055698066318⟩
  | 0, 5 => ⟨-510597279953108765010355647279926603069180560478, 517004515103047220785705097761163197463254408754⟩
  | 1, 4 => ⟨-853098341138582329017590204633756252392077101920, 854290996420040238151914413937184802913006380136⟩
  | 2, 3 => ⟨-1458952636485318908757121979061785820192736773961, 1453773328946899469481316869642836831892213981324⟩
  | 3, 2 => ⟨-2508235647571364052240786831408705846363883063858, 2497004396851003699865933933841017315342080986289⟩
  | 4, 1 => ⟨-4294251426441158049695391088716576684222026550648, 4284172678224185591759233801133217910322272843337⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0082Geometry.ds, E8TAxisProd0082Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 829483547821792536628297737559848273602291 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic

end


