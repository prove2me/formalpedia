-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T23:27:15.186339+00:00
-- url     : https://prove2.me/theorems/ca88e964-16f7-426d-a1ef-a940bd71743b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 17 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 17 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 17 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0254CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0255CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0256CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0257CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0258CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0259CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0260CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0261CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0262CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0263CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0264CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0265CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0266CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0267CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0268CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0269CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0270CertifiedArithmetic) (piece 17 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0269GraphCenterA.qJetBox,
   E8TAxisProd0269GraphCenterB.qJetBox,
   E8TAxisProd0269GraphCenterC.qJetBox,
   E8TAxisProd0269GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0269GraphWholeA.qJetBox,
   E8TAxisProd0269GraphWholeB.qJetBox,
   E8TAxisProd0269GraphWholeC.qJetBox,
   E8TAxisProd0269GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨46824136558671877932992000488680098985136734986, 46824136558671877932992000488680341151592872737⟩
  | 0, 2 => ⟨134634025174903739409171221764083483844992409888, 134634025174903739409171221764084458665153020999⟩
  | 1, 1 => ⟨135699641736168343655365252560035585513870177444, 135699641736168343655365252560037369873115942557⟩
  | 0, 3 => ⟨266854174108060155154611686875902327758570660124, 266854174108060155154611686875905570818168959965⟩
  | 1, 2 => ⟨357837075152974738754991987952344541244256195008, 357837075152974738754991987952350421235579532913⟩
  | 2, 1 => ⟨360329440431516036142163275649773343739896546502, 360329440431516036142163275649784136979550420651⟩
  | 0, 4 => ⟨439908928821935123009013681137395226066599447647, 439908928821935123009013681137406549074496667073⟩
  | 1, 3 => ⟨651268300676935437255023479992646611428592775924, 651268300676935437255023479992667374681155436144⟩
  | 2, 2 => ⟨863805665113228411476926085950702095472486264924, 863805665113228411476926085950740618062003130532⟩
  | 3, 1 => ⟨869110743916986132729608359063886908545332650837, 869110743916986132729608359063958913061007392375⟩
  | 0, 5 => ⟨-2308531581698665390234258341598408717946014008787312, 2320395008078903685991051037897048988496360752907806⟩
  | 1, 4 => ⟨-4529812299147872578499258100164346668996335549854351, 4547707711691351136793011976834668290254220873030110⟩
  | 2, 3 => ⟨-8896728690329878247250950433970024175127537671398014, 8922536951435971810466669992508786048055182619998425⟩
  | 3, 2 => ⟨-17484795237860544103391722981715829838260645954107700, 17518693054102698031429235471310445009772292738382981⟩
  | 4, 1 => ⟨-34380706916996394386030085645129961358403714119659781, 34415398619139569622852333130890950943271178677084773⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0269Geometry.ds, E8TAxisProd0269Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 44078103601607849367666514952818359426794142225 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic

end


