-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T23:11:58.60399+00:00
-- url     : https://prove2.me/theorems/9c495a21-75e0-4cba-80d0-4d922d2df7dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 14 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 14 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 14 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0254CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0255CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0256CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0257CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0258CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0259CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0260CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0261CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0262CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0263CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0264CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0265CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0266CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0267CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0268CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0269CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0270CertifiedArithmetic) (piece 14 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0266GraphCenterA.qJetBox,
   E8TAxisProd0266GraphCenterB.qJetBox,
   E8TAxisProd0266GraphCenterC.qJetBox,
   E8TAxisProd0266GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0266GraphWholeA.qJetBox,
   E8TAxisProd0266GraphWholeB.qJetBox,
   E8TAxisProd0266GraphWholeC.qJetBox,
   E8TAxisProd0266GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨63518097722940886041970891828738266464129019850, 63518097722940886041970891828738593080469203271⟩
  | 0, 2 => ⟨178219830837098621442523104402379930916110241140, 178219830837098621442523104402381274301411055707⟩
  | 1, 1 => ⟨179441623548692391170434477041629804099043161897, 179441623548692391170434477041632279486016201549⟩
  | 0, 3 => ⟨345408384052774300997950775442526586449895858745, 345408384052774300997950775442531107963870438806⟩
  | 1, 2 => ⟨461799857626466077131591612458630321129003314281, 461799857626466077131591612458638569967956826110⟩
  | 2, 1 => ⟨464597080781991936300226669015622807488475874884, 464597080781991936300226669015638024732700696978⟩
  | 0, 4 => ⟨558893955873558561868976805904630057480933733368, 558893955873558561868976805904646093705934227267⟩
  | 1, 3 => ⟨823803980716825872129517778651823646274579500591, 823803980716825872129517778651853202246062968426⟩
  | 2, 2 => ⟨1090011897127289739947151683884223695115193570095, 1090011897127289739947151683884278755101815899963⟩
  | 3, 1 => ⟨1095888775664566530584698178182076407264705435617, 1095888775664566530584698178182179710839350286381⟩
  | 0, 5 => ⟨-3184189545626283745066541144709830129107265063029385, 3199567437750364696766328617814686920935357488283691⟩
  | 1, 4 => ⟨-6256509707803347795157002480195529449908812328099969, 6279689878326078262039818084162602918116809585930816⟩
  | 2, 3 => ⟨-12304370775153564232108755226732666095902739267495255, 12337777054767799724240321599524359940030275244339983⟩
  | 3, 2 => ⟨-24213877506652973916338486398997575209566327519979484, 24257724835552780024868370637340652245311416260134543⟩
  | 4, 1 => ⟨-47675508768925129716705513573208759541635933832263232, 47720327730601730144122744200663300368705257927001059⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0266Geometry.ds, E8TAxisProd0266Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 59878602226287559046185082047830725838311296851 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic

end


