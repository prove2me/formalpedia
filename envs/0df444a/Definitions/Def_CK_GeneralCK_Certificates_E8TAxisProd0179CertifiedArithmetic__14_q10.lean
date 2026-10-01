-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q10
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:36:44.78763+00:00
-- url     : https://prove2.me/theorems/661177d5-fd74-4b51-aaee-910d9fc40a26
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 11 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 11 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 11 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0180CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0181CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0182CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0183CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0184CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0185CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0186CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0187CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0188CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0189CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0190CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0191CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0192CertifiedArithmetic) (piece 11 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q09

-- ===== source module GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0189GraphCenterA.qJetBox,
   E8TAxisProd0189GraphCenterB.qJetBox,
   E8TAxisProd0189GraphCenterC.qJetBox,
   E8TAxisProd0189GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0189GraphWholeA.qJetBox,
   E8TAxisProd0189GraphWholeB.qJetBox,
   E8TAxisProd0189GraphWholeC.qJetBox,
   E8TAxisProd0189GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨139918016858509202482365514962391196611722750, 139918016858509202482365514962397775800251319⟩
  | 0, 2 => ⟨652609248736972232889547823754226348498237735, 652609248736972232889547823754241529387261831⟩
  | 1, 1 => ⟨660187232721145979788713751411525131781993432, 660187232721145979788713751411546663301220577⟩
  | 0, 3 => ⟨1867543190272138543853381292840204827691894461, 1867543190272138543853381292840242926299620290⟩
  | 1, 2 => ⟨2747033234078613526018309578544964718264618691, 2747033234078613526018309578545019349896632721⟩
  | 2, 1 => ⟨2773916882810709722400372026665908211298514836, 2773916882810709722400372026665995611323509108⟩
  | 0, 4 => ⟨4189295849667890715468941770909600226787208318, 4189295849667890715468941770909705915618700166⟩
  | 1, 3 => ⟨7281008125660903738648689081527919437958840625, 7281008125660903738648689081528076544057215123⟩
  | 2, 2 => ⟨10396878387313600320721750057865835467648909495, 10396878387313600320721750057866092552904739293⟩
  | 3, 1 => ⟨10483782557048549230625235552129303340972732870, 10483782557048549230625235552129739171028771685⟩
  | 0, 5 => ⟨-29218051578932445304427080868753667739542229401123, 29447400037312155760963864018471868648334918936288⟩
  | 1, 4 => ⟨-54905081042688028688495829349044750102314103395598, 55176191925607980174834259756374706982830780904290⟩
  | 2, 3 => ⟨-103645136935170091934299014556498595449511781992757, 103971483827244842204203463002131672415028263383449⟩
  | 3, 2 => ⟨-196001362055396369065615366467268288333494252878950, 196390436929914467413678569668597148097742883954109⟩
  | 4, 1 => ⟨-370820243038097939439772288722091738317189457721669, 371239618127024052650626228613566228511559428267404⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0189Geometry.ds, E8TAxisProd0189Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 100907759454202030674461748618914580100137123 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic

end


