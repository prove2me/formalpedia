-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:20:26.669962+00:00
-- url     : https://prove2.me/theorems/fb1f59c5-cbca-4467-9396-4c5fb6d6a118
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 13 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 13 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 13 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0104CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0105CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0106CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0107CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0108CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0109CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0110CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0111CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0112CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0113CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0114CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0115CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0116CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0117CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0118CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0119CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0120CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0121CertifiedArithmetic) (piece 13 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0115GraphCenterA.qJetBox,
   E8TAxisProd0115GraphCenterB.qJetBox,
   E8TAxisProd0115GraphCenterC.qJetBox,
   E8TAxisProd0115GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0115GraphWholeA.qJetBox,
   E8TAxisProd0115GraphWholeB.qJetBox,
   E8TAxisProd0115GraphWholeC.qJetBox,
   E8TAxisProd0115GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨734917359091160817169242245680190894620084640, 734917359091160817169242245680203682124760571⟩
  | 0, 2 => ⟨2907217620000786701900619765024953325802028256, 2907217620000786701900619765024986686464525866⟩
  | 1, 1 => ⟨2957652384670086635897221642533777363311372923, 2957652384670086635897221642533828964684076164⟩
  | 0, 3 => ⟨7554184214196925449858949320404048078676630169, 7554184214196925449858949320404140449749229017⟩
  | 1, 2 => ⟨10738912112707512335775484682342527861882446341, 10738912112707512335775484682342672511629473246⟩
  | 2, 1 => ⟨10901031927174656061762524556151085788322016909, 10901031927174656061762524556151328543300456032⟩
  | 0, 4 => ⟨16230091752984995720615786249022751111313078417, 16230091752984995720615786249023025790775706622⟩
  | 1, 3 => ⟨26325703221080132188394338572277092013002156726, 26325703221080132188394338572277537007228590720⟩
  | 2, 2 => ⟨36543863675716008656914563549279342515866620981, 36543863675716008656914563549280106623826931922⟩
  | 3, 1 => ⟨37026795629602824124861341020884267444819238249, 37026795629602824124861341020885608490933366366⟩
  | 0, 5 => ⟨-134808503310062195620436945133193303544940932421272, 135832948609054450434198349881039604420045481145044⟩
  | 1, 4 => ⟨-258964749584735423733402102829802185435805739277318, 260413368361232173310045081296756116382851839422326⟩
  | 2, 3 => ⟨-498605482882355504773145421142995364469733106398783, 500620725765688818911703047858499772895741301161634⟩
  | 3, 2 => ⟨-961039026091479718230834777393847822718844521186601, 963663886733675708089957506651378253004285628851202⟩
  | 4, 1 => ⟨-1853287321750273906204783556847400267391500637733074, 1856089530235934378468770773229093524168200731845541⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0115Geometry.ds, E8TAxisProd0115Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 552822443528113828492177583752320818586290161 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic

end


