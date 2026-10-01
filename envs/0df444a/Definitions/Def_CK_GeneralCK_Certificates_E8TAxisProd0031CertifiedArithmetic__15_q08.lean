-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q08
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:30:14.12947+00:00
-- url     : https://prove2.me/theorems/011c8fe1-8815-45ae-85cd-fdcbe9a2d28a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 9 of 15)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 9 of 15)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 9 of 15) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0045CertifiedArithmetic) (piece 9 of 15).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q07

-- ===== source module GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0039GraphCenterA.qJetBox,
   E8TAxisProd0039GraphCenterB.qJetBox,
   E8TAxisProd0039GraphCenterC.qJetBox,
   E8TAxisProd0039GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0039GraphWholeA.qJetBox,
   E8TAxisProd0039GraphWholeB.qJetBox,
   E8TAxisProd0039GraphWholeC.qJetBox,
   E8TAxisProd0039GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨368663689169450424865840410991775336013863, 368663689169450424865840410993389805640153⟩
  | 0, 2 => ⟨4164955726881540046196425625747477271328355, 4164955726881540046196425625751592463949070⟩
  | 1, 1 => ⟨4358225369357538472621990877950416968137174, 4358225369357538472621990877955419150896463⟩
  | 0, 3 => ⟨24350534399069913231148356769885034795732340, 24350534399069913231148356769892347782089946⟩
  | 1, 2 => ⟨40525653074937361918073876580695475694883924, 40525653074937361918073876580703809219379542⟩
  | 2, 1 => ⟨41964730801165394589985190371012302814151040, 41964730801165394589985190371023512779997274⟩
  | 0, 4 => ⟨73097526164672453223369069586510516140302663, 73097526164672453223369069586530736594530957⟩
  | 1, 3 => ⟨188708358073416928219216555131826705679528617, 188708358073416928219216555131850030086494657⟩
  | 2, 2 => ⟨307693748300712682945416389850966449798569858, 307693748300712682945416389850998407815374967⟩
  | 3, 1 => ⟨315439903178104804368779327015898472995295458, 315439903178104804368779327015947583053185757⟩
  | 0, 5 => ⟨-465330743256396402571386404595421876976562999398, 470267667397008872791192268520964368358649015733⟩
  | 1, 4 => ⟨-760083848752651159529541595428936894303005039231, 760119244561562848669605307473917370883380561065⟩
  | 2, 3 => ⟨-1281533583265368246534084200433314347759630749943, 1275675358036643368586546116790330424678295682620⟩
  | 3, 2 => ⟨-2176095225248732313445682390869650086724867344658, 2164881902175922136225204716301561006778334294174⟩
  | 4, 1 => ⟨-3674408209467831417916654324159394339228498336159, 3665442340897178725945765006806131846980889565174⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0039Geometry.ds, E8TAxisProd0039Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 269963532586493158306439123706229245627080 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic

end


