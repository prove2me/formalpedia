-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:39:08.732339+00:00
-- url     : https://prove2.me/theorems/6cd8509a-0070-4b8b-a525-94907e478ced
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 14 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 14 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 14 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK/Certificates/E8TAxisProd0404CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0405CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0406CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0407CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0408CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0409CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0410CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0411CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0412CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0413CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0414CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0415CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0416CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0417CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0418CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0419CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0420CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0421CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0422CertifiedArithmetic) (piece 14 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0416GraphCenterA.qJetBox,
   E8TAxisProd0416GraphCenterB.qJetBox,
   E8TAxisProd0416GraphCenterC.qJetBox,
   E8TAxisProd0416GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0416GraphWholeA.qJetBox,
   E8TAxisProd0416GraphWholeB.qJetBox,
   E8TAxisProd0416GraphWholeC.qJetBox,
   E8TAxisProd0416GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27083432980670492223713861336675622174122125174, 27083432980670492223713861336675768941651849388⟩
  | 0, 2 => ⟨81756295838779165332502130634143354717392074470, 81756295838779165332502130634143920992512061553⟩
  | 1, 1 => ⟨82155662958618318421800313534331474266557009673, 82155662958618318421800313534332497314413845865⟩
  | 0, 3 => ⟨169035863542613716122366734977806457806082717094, 169035863542613716122366734977808306129594523299⟩
  | 1, 2 => ⟨227612663280056086923211917937706783982737637743, 227612663280056086923211917937710096210883627000⟩
  | 2, 1 => ⟨228586489867209220350989652009485324284535614642, 228586489867209220350989652009491349430051680231⟩
  | 0, 4 => ⟨289102564387339925755890375559792616243147518472, 289102564387339925755890375559798918812695145311⟩
  | 1, 3 => ⟨431337968526924190972468963220475609965670425878, 431337968526924190972468963220487059344766530234⟩
  | 2, 2 => ⟨574053110089145089344867633539100868136093616689, 574053110089145089344867633539121957305479997409⟩
  | 3, 1 => ⟨576187724823814282315927632001545469017588935616, 576187724823814282315927632001584627969382254356⟩
  | 0, 5 => ⟨-1271893195483107220333995513610361846763805324142918, 1279112043173558725253491098344622733854936944581469⟩
  | 1, 4 => ⟨-2488807861797461404582910490613906661576224594973869, 2499690670783979469546103310866434959628624342516038⟩
  | 2, 3 => ⟨-4874997879755313119579772062858329460816139923983384, 4890690415134454745727142293892496849806948414643086⟩
  | 3, 2 => ⟨-9555407459111246112394821537034843375698266954938776, 9576015319166594336317820156609820680876774989487385⟩
  | 4, 1 => ⟨-18739056451570211978901781818680542593850482504381082, 18760117737427168555186763655749738756210437728422836⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0416Geometry.ds, E8TAxisProd0416Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25428560757966886726975297913451652498962599722 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic

end


