-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:44:35.453034+00:00
-- url     : https://prove2.me/theorems/18f945c1-8621-4663-9acf-aa6e127c8f5b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 12 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 12 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 12 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0493CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0494CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0495CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0496CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0497CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0498CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0499CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0500CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0501CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0502CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0503CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0504CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0505CertifiedArithmetic) (piece 12 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0503GraphCenterA.qJetBox,
   E8TAxisProd0503GraphCenterB.qJetBox,
   E8TAxisProd0503GraphCenterC.qJetBox,
   E8TAxisProd0503GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0503GraphWholeA.qJetBox,
   E8TAxisProd0503GraphWholeB.qJetBox,
   E8TAxisProd0503GraphWholeC.qJetBox,
   E8TAxisProd0503GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7832049276414929119073884870235356316287206689, 7832049276414929119073884870235409360072634593⟩
  | 0, 2 => ⟨25962113579266393070328823687000273239873191479, 25962113579266393070328823687000454541267816460⟩
  | 1, 1 => ⟨26240368466431252304135361267403482016312721909, 26240368466431252304135361267403796716396776610⟩
  | 0, 3 => ⟨58794830980187892768753888735846230676376546316, 58794830980187892768753888735846798265451889579⟩
  | 1, 2 => ⟨80372873078194633385673675391196937455604290490, 80372873078194633385673675391197921169860762461⟩
  | 2, 1 => ⟨81127941396000868197273133900390243665032647093, 81127941396000868197273133900391992577547118561⟩
  | 0, 4 => ⟨110314915734652431268449652705956353623021437319, 110314915734652431268449652705958216195738513535⟩
  | 1, 3 => ⟨168333579500135039958156664739198941676336459323, 168333579500135039958156664739202237630157312386⟩
  | 2, 2 => ⟨226779426691422730192366348152477230218480754363, 226779426691422730192366348152483191781015971878⟩
  | 3, 1 => ⟨228612121550050954809429963442800788987873938860, 228612121550050954809429963442811684383341222917⟩
  | 0, 5 => ⟨-287049961746791956884822469604505435645503935044005, 289005459674275800972419655108257466478126794896228⟩
  | 1, 4 => ⟨-556733387414499054866990880652299705080541473015315, 559628554541875968611469484358320226610865841031384⟩
  | 2, 3 => ⟨-1081457584094338107071956772505008752759191892464072, 1085582708215598932218895134074355690570668536976461⟩
  | 3, 2 => ⟨-2102599582826071915298496973742676301182306227627965, 2107983414271655726812480202252443053141268736804397⟩
  | 4, 1 => ⟨-4090288444366767791656250817903697603286822209339687, 4095796691782839119236179356624067378685351611626937⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0503Geometry.ds, E8TAxisProd0503Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7310961051246585009089983970155925161019872949 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic

end


