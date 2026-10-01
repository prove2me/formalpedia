-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q07
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:38:08.056734+00:00
-- url     : https://prove2.me/theorems/0870e983-d8eb-47a7-8fb1-65a9ce7b19a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 8 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 8 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 8 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0104CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0105CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0106CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0107CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0108CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0109CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0110CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0111CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0112CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0113CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0114CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0115CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0116CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0117CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0118CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0119CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0120CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0121CertifiedArithmetic) (piece 8 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q06

-- ===== source module GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0110GraphCenterA.qJetBox,
   E8TAxisProd0110GraphCenterB.qJetBox,
   E8TAxisProd0110GraphCenterC.qJetBox,
   E8TAxisProd0110GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0110GraphWholeA.qJetBox,
   E8TAxisProd0110GraphWholeB.qJetBox,
   E8TAxisProd0110GraphWholeC.qJetBox,
   E8TAxisProd0110GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1500073030808934222542566637201932157164517193, 1500073030808934222542566637201950440820481979⟩
  | 0, 2 => ⟨5636485367452909992672538763612949373705210985, 5636485367452909992672538763613000425126358779⟩
  | 1, 1 => ⟨5698959650111384635903610468521818302997064032, 5698959650111384635903610468521900229993539972⟩
  | 0, 3 => ⟨14123744732957821274453926951108630867025140696, 14123744732957821274453926951108777145892785970⟩
  | 1, 2 => ⟨19773083572445902371686783183339789442574644528, 19773083572445902371686783183340026235737492484⟩
  | 2, 1 => ⟨19965207755669179571358932846701703201091533854, 19965207755669179571358932846702107806873472307⟩
  | 0, 4 => ⟨29441330927157103182072979731026961805096525883, 29441330927157103182072979731027407687817973026⟩
  | 1, 3 => ⟨46656924200239391733996063280297823310730374950, 46656924200239391733996063280298567213219412909⟩
  | 2, 2 => ⟨64006488353673644619827272424327192458547648393, 64006488353673644619827272424328491125125864117⟩
  | 3, 1 => ⟨64550028071576232961279307575318283666572128711, 64550028071576232961279307575320591935082297107⟩
  | 0, 5 => ⟨-366118903651110963404812765505915116571278212567603, 367598929254794584929630957419827380151442239336471⟩
  | 1, 4 => ⟨-709837570198488250781476840952503260020346974894394, 711918953672124405040196632778804172928809006750290⟩
  | 2, 3 => ⟨-1378026462069719743627794107353416304813082257164877, 1380902045213149454704291652488709251849454695807607⟩
  | 3, 2 => ⟨-2676925888632987527738116036708988968865508371395254, 2680650474278430672955215515866956380738938068668478⟩
  | 4, 1 => ⟨-5201897469930400198352836003794883040196693930997409, 5205851973463932605846135607559152638679667124320877⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0110Geometry.ds, E8TAxisProd0110Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1079595204419730998925898474567619957504193878 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic

end


