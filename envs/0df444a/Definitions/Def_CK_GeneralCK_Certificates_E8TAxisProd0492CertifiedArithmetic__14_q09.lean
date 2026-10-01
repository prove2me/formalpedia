-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q09
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:31:48.470097+00:00
-- url     : https://prove2.me/theorems/a6d6f389-fc56-4964-8859-0c3a08e72f2d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 10 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 10 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 10 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0493CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0494CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0495CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0496CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0497CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0498CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0499CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0500CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0501CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0502CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0503CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0504CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0505CertifiedArithmetic) (piece 10 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q08

-- ===== source module GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0501GraphCenterA.qJetBox,
   E8TAxisProd0501GraphCenterB.qJetBox,
   E8TAxisProd0501GraphCenterC.qJetBox,
   E8TAxisProd0501GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0501GraphWholeA.qJetBox,
   E8TAxisProd0501GraphWholeB.qJetBox,
   E8TAxisProd0501GraphWholeC.qJetBox,
   E8TAxisProd0501GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7864547887778890418509778553713451803444345651, 7864547887778890418509778553713504952669678578⟩
  | 0, 2 => ⟨26035693360314350857447359270143385861106322294, 26035693360314350857447359270143567561371015465⟩
  | 1, 1 => ⟨26340966162269948039452283230970578753089446948, 26340966162269948039452283230970894161464023475⟩
  | 0, 3 => ⟨58932865753374842700051165363358577346846053714, 58932865753374842700051165363359146202582781584⟩
  | 1, 2 => ⟨80583515403699342382558017187580290032260107711, 80583515403699342382558017187581275982278244962⟩
  | 2, 1 => ⟨81411751036018789796280181861154450964486741063, 81411751036018789796280181861156203909116711184⟩
  | 0, 4 => ⟨110540788530582716167372440893478282162814605594, 110540788530582716167372440893480148998406785038⟩
  | 1, 3 => ⟨168694251425834572014570657121323054804477954581, 168694251425834572014570657121326358380956244151⟩
  | 2, 2 => ⟨227316167492838219458917162415263226731659725409, 227316167492838219458917162415269202216546761946⟩
  | 3, 1 => ⟨229326050400025357016354152606961042273461757323, 229326050400025357016354152606971963367074893592⟩
  | 0, 5 => ⟨-287937860152398868755217861604275082188982083573322, 289897966429136903493476864762830804627884970367639⟩
  | 1, 4 => ⟨-558467107349212294863387517748144673369654320992327, 561369170917918913410712438447697364872244050043943⟩
  | 2, 3 => ⟨-1084847446215678154614767088035384816696247120889012, 1088982405865257910284576939621541853902797318846007⟩
  | 3, 2 => ⟨-2109233389724581555662835071858128472788664871875921, 2114630019364588047596645479989453640674107724086066⟩
  | 4, 1 => ⟨-4103278579890090747745558088608555762745529844440308, 4108800040931687405618652357330418740847970302659782⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0501Geometry.ds, E8TAxisProd0501Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7341496496416323581200110963755870596891144663 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic

end


