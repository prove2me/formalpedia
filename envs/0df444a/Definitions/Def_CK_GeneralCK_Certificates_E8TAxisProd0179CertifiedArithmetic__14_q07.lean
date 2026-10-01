-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q07
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:24:17.001855+00:00
-- url     : https://prove2.me/theorems/e88f360d-bfa9-4799-9d13-cc686e8f1f62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 8 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 8 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 8 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0180CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0181CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0182CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0183CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0184CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0185CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0186CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0187CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0188CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0189CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0190CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0191CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0192CertifiedArithmetic) (piece 8 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q06

-- ===== source module GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0186GraphCenterA.qJetBox,
   E8TAxisProd0186GraphCenterB.qJetBox,
   E8TAxisProd0186GraphCenterC.qJetBox,
   E8TAxisProd0186GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0186GraphWholeA.qJetBox,
   E8TAxisProd0186GraphWholeB.qJetBox,
   E8TAxisProd0186GraphWholeC.qJetBox,
   E8TAxisProd0186GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨322617982928751891135819329264543858456551469, 322617982928751891135819329264552854304335024⟩
  | 0, 2 => ⟨1387241435529843829431600833899946357055831187, 1387241435529843829431600833899968291770213506⟩
  | 1, 1 => ⟨1397539655512003409672974496914293760237769109, 1397539655512003409672974496914326283753821091⟩
  | 0, 3 => ⟨3776805105703262358627836908504553499205356125, 3776805105703262358627836908504611539150178184⟩
  | 1, 2 => ⟨5441855873683830122079857397109939112497112665, 5441855873683830122079857397110026338789001449⟩
  | 2, 1 => ⟨5476533299338712596769456151581624110259575563, 5476533299338712596769456151581767269429731727⟩
  | 0, 4 => ⟨8323405467473558412516849114983929731039683680, 8323405467473558412516849114984096621495527404⟩
  | 1, 3 => ⟨13897284769224580588491558053673047691661819713, 13897284769224580588491558053673307799947798452⟩
  | 2, 2 => ⟨19499666637853675892199866674260156612155933859, 19499666637853675892199866674260593631309154792⟩
  | 3, 1 => ⟨19607644202696998914206672126533969655497586433, 19607644202696998914206672126534724352376850162⟩
  | 0, 5 => ⟨-60880390694095014337776679320520549230525693792794, 61352172899855280549363735961236986892737994105371⟩
  | 1, 4 => ⟨-115795664490476258772452154787741890903434978411887, 116417220279353095135011768812832742107162544377923⟩
  | 2, 3 => ⟨-220957174481719089231461546934925128478246751996669, 221776545630401339511529913766059119568618017171395⟩
  | 3, 2 => ⟨-422203998560889717601992162384382337421532515787628, 423234775167384998690239299691566491758171608731374⟩
  | 4, 1 => ⟨-807144511168811992690761664683658806262395254468758, 808231654468406566211662751790253555659976236925765⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0186Geometry.ds, E8TAxisProd0186Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 239316345754597006282486373306003319962801834 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic

end


