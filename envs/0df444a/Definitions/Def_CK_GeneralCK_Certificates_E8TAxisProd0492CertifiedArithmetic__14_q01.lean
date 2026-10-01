-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:16:58.700351+00:00
-- url     : https://prove2.me/theorems/3bb9b3aa-e81c-4f62-93d3-97e89235ef3d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 2 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 2 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 2 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0493CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0494CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0495CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0496CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0497CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0498CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0499CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0500CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0501CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0502CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0503CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0504CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0505CertifiedArithmetic) (piece 2 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0493GraphCenterA.qJetBox,
   E8TAxisProd0493GraphCenterB.qJetBox,
   E8TAxisProd0493GraphCenterC.qJetBox,
   E8TAxisProd0493GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0493GraphWholeA.qJetBox,
   E8TAxisProd0493GraphWholeB.qJetBox,
   E8TAxisProd0493GraphWholeC.qJetBox,
   E8TAxisProd0493GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12516253717261529001860460679883574443693717045, 12516253717261529001860460679883650584661448089⟩
  | 0, 2 => ⟨40054948406103631665076762015337536050889638694, 40054948406103631665076762015337809363109185374⟩
  | 1, 1 => ⟨40423288678088982968575162444790516541191417154, 40423288678088982968575162444790998949009082886⟩
  | 0, 3 => ⟨87730851408656055838960711356801414818153538717, 87730851408656055838960711356802283146059308683⟩
  | 1, 2 => ⟨119228975055736044674035170635460995630475175511, 119228975055736044674035170635462521168857609410⟩
  | 2, 1 => ⟨120188607427739641079338906284269436648950371957, 120188607427739641079338906284272172899199007446⟩
  | 0, 4 => ⟨158876480900460274476772138586333030620586512997, 158876480900460274476772138586335908724404947664⟩
  | 1, 3 => ⟨240291159935953289853128553688125878352733440024, 240291159935953289853128553688131025130871968012⟩
  | 2, 2 => ⟨322218215608316376317356839739301035111757879635, 322218215608316376317356839739310408958375273021⟩
  | 3, 1 => ⟨324448902575086281660573573059384885290704297577, 324448902575086281660573573059402118107896429355⟩
  | 0, 5 => ⟨-518181537146789894183458296565637814606527815552770, 521367982328878683662898538998542787331769596269716⟩
  | 1, 4 => ⟨-1008972554352164634139447949381132843958459812317764, 1013725298746245707377112274026651030782452870640206⟩
  | 2, 3 => ⟨-1967085613644396393436238538587451577291300928419014, 1973889470055201931431936863677806855891791039173284⟩
  | 3, 2 => ⟨-3837937747000439030351132864331642078642404387631857, 3846837683497734326296133481058903407535212211050216⟩
  | 4, 1 => ⟨-7492100352953966556000441749928634890805000089542104, 7501195563236450734683204422474507172289356560672491⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0493Geometry.ds, E8TAxisProd0493Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11708786421468011142032766157948383064496927039 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic

end


