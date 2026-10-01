-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q08
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:22:04.396266+00:00
-- url     : https://prove2.me/theorems/c37c9a7d-2e9e-440f-913b-561492619fb6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 9 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 9 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 9 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0493CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0494CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0495CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0496CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0497CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0498CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0499CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0500CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0501CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0502CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0503CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0504CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0505CertifiedArithmetic) (piece 9 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q07

-- ===== source module GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0500GraphCenterA.qJetBox,
   E8TAxisProd0500GraphCenterB.qJetBox,
   E8TAxisProd0500GraphCenterC.qJetBox,
   E8TAxisProd0500GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0500GraphWholeA.qJetBox,
   E8TAxisProd0500GraphWholeB.qJetBox,
   E8TAxisProd0500GraphWholeC.qJetBox,
   E8TAxisProd0500GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8865562788793297557761783906170789151427110956, 8865562788793297557761783906170847283992703403⟩
  | 0, 2 => ⟨29082964029408710136236768626431872222168563230, 29082964029408710136236768626432073551196666002⟩
  | 1, 1 => ⟨29419332726793499317011309695898391837923131877, 29419332726793499317011309695898742885762433541⟩
  | 0, 3 => ⟨65280344121866960899698363734173692121434129851, 65280344121866960899698363734174324989792763103⟩
  | 1, 2 => ⟨89131720830408687783892290277450177559375968759, 89131720830408687783892290277451278470628315293⟩
  | 2, 1 => ⟨90034981262771499724338598533119161759902126182, 90034981262771499724338598533121123650466553860⟩
  | 0, 4 => ⟨121352104159902618877863360411727522136107151311, 121352104159902618877863360411729604827630286755⟩
  | 1, 3 => ⟨184768633036706899499961857670964220149287270619, 184768633036706899499961857670967916337785838673⟩
  | 2, 2 => ⟨248688354371199091345378858321841747696671650595, 248688354371199091345378858321848445809497458334⟩
  | 3, 1 => ⟨250855503450208341194617758315439300783662424933, 250855503450208341194617758315451561722127305914⟩
  | 0, 5 => ⟨-335660501679400135462373226206340430585465035352288, 337879937039090249064030729373155610137789038673563⟩
  | 1, 4 => ⟨-651732292708449838962410213635298224259423881600125, 655024962187967333466143369047546504720455429840439⟩
  | 2, 3 => ⟨-1267279662006644349295935515380239245440222540403032, 1271977085199100055967589259758378424614455242133210⟩
  | 3, 2 => ⟨-2466288931213596496010267886834670082372500582201501, 2472423137950364880135120510418589161955850382678472⟩
  | 4, 1 => ⟨-4802413570421010522887015733047703324059001253642823, 4808687044922839583967233239744166507373042886611669⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0500Geometry.ds, E8TAxisProd0500Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8280517895965028828043276331207607045445878274 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic

end


