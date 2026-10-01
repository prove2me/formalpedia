-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:17:28.060243+00:00
-- url     : https://prove2.me/theorems/39658b4a-47b2-4dd2-ace8-7f941e53d686
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 12 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 12 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0063CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0064CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0065CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0066CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0067CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0068CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0069CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0070CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0071CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0072CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0076CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0077CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0078CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0081CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0082CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0083CertifiedArithmetic) (piece 12 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0063CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0064CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0065CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0066CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0067CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0068CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0069CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0070CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0071CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0072CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0075CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0076CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0077CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0078CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0081CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0082CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0083CertifiedArithmetic) (piece 12 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18_q10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0075GraphCenterA.qJetBox,
   E8TAxisProd0075GraphCenterB.qJetBox,
   E8TAxisProd0075GraphCenterC.qJetBox,
   E8TAxisProd0075GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0075GraphWholeA.qJetBox,
   E8TAxisProd0075GraphWholeB.qJetBox,
   E8TAxisProd0075GraphWholeC.qJetBox,
   E8TAxisProd0075GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1441639597932143223525870403566331403759689, 1441639597932143223525870403568384015443976⟩
  | 0, 2 => ⟨12641593683324406567861518226666813527235516, 12641593683324406567861518226671661195125785⟩
  | 1, 1 => ⟨13319668166994268099815924686744357923437793, 13319668166994268099815924686750308318056230⟩
  | 0, 3 => ⟨59178659600502208629338672187037086620360542, 59178659600502208629338672187046358661936871⟩
  | 1, 2 => ⟨97346077007250033389403066299906744392489751, 97346077007250033389403066299917628689242897⟩
  | 2, 1 => ⟨101387892752714985903275847973787640727308309, 101387892752714985903275847973802810377306986⟩
  | 0, 4 => ⟨156469599287064543113043460801162747357732195, 156469599287064543113043460801187808770852619⟩
  | 1, 3 => ⟨373755692194316175603487097946685471080378871, 373755692194316175603487097946715456221842837⟩
  | 2, 2 => ⟨598383640938156095241719025459423055904054374, 598383640938156095241719025459465632754754111⟩
  | 3, 1 => ⟨616574096668001183273315657632382490958203350, 616574096668001183273315657632449046855975942⟩
  | 0, 5 => ⟨-549755902858427180775244030406780896473387913561, 556218961897758177879137655435107420535819710277⟩
  | 1, 4 => ⟨-922132453418320909700037350739591403322070804055, 923048709028923896714715963861941703487349720221⟩
  | 2, 3 => ⟨-1582914402092555800999778870462077917508080066169, 1577041967553363295296986384076868725488268895606⟩
  | 3, 2 => ⟨-2732384111349284408570294092903124394660722890197, 2720032471385689757477463679528399831959763809719⟩
  | 4, 1 => ⟨-4700404966350027995639227611577085292240407477103, 4689061523759855909193791865842509650073789658106⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0075Geometry.ds, E8TAxisProd0075Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1188905092604096918960318499540815244526221 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0075CertifiedArithmetic

end


