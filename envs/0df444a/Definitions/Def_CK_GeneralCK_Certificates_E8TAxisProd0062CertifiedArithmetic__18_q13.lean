-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:33:42.320316+00:00
-- url     : https://prove2.me/theorems/087c5c15-e467-4785-9787-b920c2856d81
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 14 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 14 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 14 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0078CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0081CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0082CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0083CertifiedArithmetic) (piece 14 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0077GraphCenterA.qJetBox,
   E8TAxisProd0077GraphCenterB.qJetBox,
   E8TAxisProd0077GraphCenterC.qJetBox,
   E8TAxisProd0077GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0077GraphWholeA.qJetBox,
   E8TAxisProd0077GraphWholeB.qJetBox,
   E8TAxisProd0077GraphWholeC.qJetBox,
   E8TAxisProd0077GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1410220140048553511386722347984346405630876, 1410220140048553511386722347986391277171759⟩
  | 0, 2 => ⟨12494135223849646950083683320256459839400388, 12494135223849646950083683320261293416992606⟩
  | 1, 1 => ⟨13077468677404513598367426064856908289793020, 13077468677404513598367426064862841816367064⟩
  | 0, 3 => ⟨58788418679961734900851869763618257324079815, 58788418679961734900851869763627493190824496⟩
  | 1, 2 => ⟨96414426890731959040399157678006070191449322, 96414426890731959040399157678016910780408671⟩
  | 2, 1 => ⟨99897731498570387983800397785525959112475983, 99897731498570387983800397785541064738155863⟩
  | 0, 4 => ⟨155723917382808750081372720708458955770619655, 155723917382808750081372720708483927619430415⟩
  | 1, 3 => ⟨371566348304101746002764571124609074113606519, 371566348304101746002764571124638948517808833⟩
  | 2, 2 => ⟨593749623520380147124576434696646112289037591, 593749623520380147124576434696688519032999092⟩
  | 3, 1 => ⟨609448017068099054944233229956141325354838808, 609448017068099054944233229956207599109610590⟩
  | 0, 5 => ⟨-547579100493567930576282645316393242073128990174, 554050713988864893264552938249644576134898100094⟩
  | 1, 4 => ⟨-918278689389849977784796153520909865270236792898, 919242918800702529421194931931577264545287093998⟩
  | 2, 3 => ⟨-1575914438882643705242104771942072906338084925546, 1570148611912275394815859129476111403035929554152⟩
  | 3, 2 => ⟨-2719501155184920892606077580614548273846680061586, 2707347832582927320115783036199668592338890860450⟩
  | 4, 1 => ⟨-4676511311678427999458813504830327221368195585786, 4665523929652394717430463221142538515002549475984⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0077Geometry.ds, E8TAxisProd0077Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1161730261272479701287145450364312393258478 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic

end


