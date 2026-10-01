-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q08
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:21:59.180509+00:00
-- url     : https://prove2.me/theorems/4c42ec2d-c1c7-4e99-aed1-5e87688d2dfb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 9 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 9 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 9 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK/Certificates/E8TAxisProd0404CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0405CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0406CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0407CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0408CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0409CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0410CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0411CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0412CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0413CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0414CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0415CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0416CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0417CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0418CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0419CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0420CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0421CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0422CertifiedArithmetic) (piece 9 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q07

-- ===== source module GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0411GraphCenterA.qJetBox,
   E8TAxisProd0411GraphCenterB.qJetBox,
   E8TAxisProd0411GraphCenterC.qJetBox,
   E8TAxisProd0411GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0411GraphWholeA.qJetBox,
   E8TAxisProd0411GraphWholeB.qJetBox,
   E8TAxisProd0411GraphWholeC.qJetBox,
   E8TAxisProd0411GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24366748326524241730741708074640055026787065739, 24366748326524241730741708074640188519236551222⟩
  | 0, 2 => ⟨74130192573757653961215391590992820678684310491, 74130192573757653961215391590993331137109630307⟩
  | 1, 1 => ⟨74563067883620279664916626454852747682043933201, 74563067883620279664916626454853667239836979788⟩
  | 0, 3 => ⟨154489109707721709905781278375008472813229932105, 154489109707721709905781278375010133451010446281⟩
  | 1, 2 => ⟨208298667295867366173802840112772341456521826763, 208298667295867366173802840112775310004408093779⟩
  | 2, 1 => ⟨209363546315022787080985927288879743130952143594, 209363546315022787080985927288885133219503068855⟩
  | 0, 4 => ⟨266225112618512881923430732874211848109523483930, 266225112618512881923430732874217490215255293164⟩
  | 1, 3 => ⟨397933113862130518532237817900753099974662182853, 397933113862130518532237817900763329660406100518⟩
  | 2, 2 => ⟨530170816527527877354652852514346765363875162811, 530170816527527877354652852514365580727111966011⟩
  | 3, 1 => ⟨532521299101972859492934550358099880353157776894, 532521299101972859492934550358134771607015731913⟩
  | 0, 5 => ⟨-1125841085196233142919539612770970481792843731223141, 1132295417553570734162164752041337358702401698629026⟩
  | 1, 4 => ⟨-2201661952334789653649122606523529266828312352327964, 2211380841318623358788110591841878614606505824354998⟩
  | 2, 3 => ⟨-4310001250109207473515160393033467634115019795206185, 4324005254058616101782222582656876505418186582329129⟩
  | 3, 2 => ⟨-8443060092587194347949372730734488575577331596763394, 8461446426803247029634801857535160053751605672072249⟩
  | 4, 1 => ⟨-16548046995590282030680445667042041059798428328473592, 16566850853037090976973881057308921259004829305055997⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0411Geometry.ds, E8TAxisProd0411Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 22866660251880882549628000367816138760699077858 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic

end


