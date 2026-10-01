-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:03:29.691111+00:00
-- url     : https://prove2.me/theorems/db89b3b7-2a98-41d7-9e58-e91c39c8a2ba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 3 of 15)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 3 of 15)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 3 of 15) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0045CertifiedArithmetic) (piece 3 of 15).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q01

-- ===== source module GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0033GraphCenterA.qJetBox,
   E8TAxisProd0033GraphCenterB.qJetBox,
   E8TAxisProd0033GraphCenterC.qJetBox,
   E8TAxisProd0033GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0033GraphWholeA.qJetBox,
   E8TAxisProd0033GraphWholeB.qJetBox,
   E8TAxisProd0033GraphWholeC.qJetBox,
   E8TAxisProd0033GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨774378065897177840749802420993188272216630, 774378065897177840749802420995019741030178⟩
  | 0, 2 => ⟨7567545123024880320355306744673147982740621, 7567545123024880320355306744677617931651252⟩
  | 1, 1 => ⟨7993826090769373739436680380256169163902557, 7993826090769373739436680380261623999806241⟩
  | 0, 3 => ⟨39026915025455552392991931651879277608798991, 39026915025455552392991931651887540036259828⟩
  | 1, 2 => ⟨64776517908523255816366467454215200701265374, 64776517908523255816366467454224753032288823⟩
  | 2, 1 => ⟨67584919380304711630463983903025033117788768, 67584919380304711630463983903038124166627839⟩
  | 0, 4 => ⟨108709578647780865002889563175280763639868677, 108709578647780865002889563175303305899700994⟩
  | 1, 3 => ⟨270263507304162451303861384762521341415844241, 270263507304162451303861384762547816249429195⟩
  | 2, 2 => ⟨437550709907796356463688595488075545098209408, 437550709907796356463688595488112500904861452⟩
  | 3, 1 => ⟨451219106083011050988077631942031877635250515, 451219106083011050988077631942089171570502075⟩
  | 0, 5 => ⟨-531418665380084151224959661228521089482525005421, 538280754376528964725288972880940380900915517785⟩
  | 1, 4 => ⟨-876405321368834969044837235239261101020043788779, 878069934223886809353680797950877186542321959755⟩
  | 2, 3 => ⟨-1490385436215954502647436566880493675468128355128, 1485855857075016535024221487602882494223893866405⟩
  | 3, 2 => ⟨-2552907762040534201187667902555667232487638604703, 2542813712640783571395109214519881612008262094957⟩
  | 4, 1 => ⟨-4354328870452256398988858875136501683363246615062, 4346755250898243442761071031541075292432947310337⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0033Geometry.ds, E8TAxisProd0033Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 603742407402900295619236214923990154598361 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic

end


