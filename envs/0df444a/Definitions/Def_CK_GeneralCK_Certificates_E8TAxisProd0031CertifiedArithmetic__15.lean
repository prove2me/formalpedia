-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:23:08.177281+00:00
-- url     : https://prove2.me/theorems/231d6903-844d-411e-99a4-89d4491f3cb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0045CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0045GraphCenterA.qJetBox,
   E8TAxisProd0045GraphCenterB.qJetBox,
   E8TAxisProd0045GraphCenterC.qJetBox,
   E8TAxisProd0045GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0045GraphWholeA.qJetBox,
   E8TAxisProd0045GraphWholeB.qJetBox,
   E8TAxisProd0045GraphWholeC.qJetBox,
   E8TAxisProd0045GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨177482211105944667425977255654961567060434, 177482211105944667425977255656398149635268⟩
  | 0, 2 => ⟨2240132710990187595576031416980939931526769, 2240132710990187595576031416984780204615221⟩
  | 1, 1 => ⟨2407939192109830150121153885608718963821225, 2407939192109830150121153885613374725680060⟩
  | 0, 3 => ⟨14756353888460404229376569698055532869630534, 14756353888460404229376569698062103040028861⟩
  | 1, 2 => ⟨25050826060653621019772788454482710568303371, 25050826060653621019772788454490100924421715⟩
  | 2, 1 => ⟨26482097549715150036192291605997275740683195, 26482097549715150036192291606007025825331760⟩
  | 0, 4 => ⟨48240052363484421388473919029141372510496502, 48240052363484421388473919029159809997521882⟩
  | 1, 3 => ⟨130432007192334352155798434841898169804383563, 130432007192334352155798434841919085399344164⟩
  | 2, 2 => ⟨216521207054995905432932764738832553165860835, 216521207054995905432932764738860691754815179⟩
  | 3, 1 => ⟨225180436175349096644224549626291688578162507, 225180436175349096644224549626334589226964779⟩
  | 0, 5 => ⟨-414832709678287285756267266625799093490128939647, 417947682747873037686676100415533335852895551237⟩
  | 1, 4 => ⟨-671784389529999033031206771501656132327401848286, 670108593038338689160203452366220951302962304684⟩
  | 2, 3 => ⟨-1123982890115012596021627326655905623633094776107, 1116495389694114674265197061773190534206181173072⟩
  | 3, 2 => ⟨-1893876857304028901785761452110805826460604757109, 1881009927933615248257622919289883639807686966939⟩
  | 4, 1 => ⟨-3169511903341913492729755439155274792425822810216, 3158295757705267051213481734429156422028123478929⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0045Geometry.ds, E8TAxisProd0045Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 118446167925346997942601207543900778208064 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic

end


