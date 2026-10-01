-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0450CertifiedArithmetic__14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0450CertifiedArithmetic__14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:50:42.518386+00:00
-- url     : https://prove2.me/theorems/65daf19b-a820-4b1a-ab94-6ad4da5e65f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0450CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0451CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0452CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0453CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0454CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0455CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0456CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0457CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0458CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0459CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0460CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0461CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0462CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0463CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0446GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0450GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0446GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0444GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0453GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0454GraphWholeC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphCenterA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0457GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0458GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0461GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0462GraphWholeC__9

-- ===== source module GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0450GraphCenterA.qJetBox,
   E8TAxisProd0450GraphCenterB.qJetBox,
   E8TAxisProd0450GraphCenterC.qJetBox,
   E8TAxisProd0450GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0450GraphWholeA.qJetBox,
   E8TAxisProd0450GraphWholeB.qJetBox,
   E8TAxisProd0450GraphWholeC.qJetBox,
   E8TAxisProd0450GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17991020752127989448076446067805478130476141781, 17991020752127989448076446067805579985857474647⟩
  | 0, 2 => ⟨55690870325870352322404074338033450258864419584, 55690870325870352322404074338033828776763027731⟩
  | 1, 1 => ⟨56438189333584529038622876621926308277247396126, 56438189333584529038622876621926983853005842928⟩
  | 0, 3 => ⟨118615637999777512384938183036997366674267536567, 118615637999777512384938183036998584920609683888⟩
  | 1, 2 => ⟨160791829490274458166622700761074370682485165638, 160791829490274458166622700761076531225181620318⟩
  | 2, 1 => ⟨162680256792714287062061842969306972198103028954, 162680256792714287062061842969310872895697211045⟩
  | 0, 4 => ⟨209020894002950224560908272733791812850269567260, 209020894002950224560908272733795905823782872427⟩
  | 1, 3 => ⟨314374516980082000566276743861676974673200112244, 314374516980082000566276743861684348920216710379⟩
  | 2, 2 => ⟨420697544464469890070007950030282385455408813621, 420697544464469890070007950030295887163449063319⟩
  | 3, 1 => ⟨424962013535110993837212946377772005509467301555, 424962013535110993837212946377796941980893682006⟩
  | 0, 5 => ⟨-789837758960209593684745917772077582888238973058592, 794461755164255542868165860565821054843806780034151⟩
  | 1, 4 => ⟨-1541693758349376989600105861106035259238034809481044, 1548626682139124706303056851274298906201222981008381⟩
  | 2, 3 => ⟨-3012640808545817820256717855954225088537964020804616, 3022600930014295758043689277130555790823466532564672⟩
  | 3, 2 => ⟨-5891217004284582791528840787299624260309047887463639, 5904273835003761065398889410773716991443017806373935⟩
  | 4, 1 => ⟨-11526257380493260761689051327202038801335231440689584, 11539618392953632288762062803190547789086339383408699⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0450Geometry.ds, E8TAxisProd0450Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16859754733867827048928672855119693565295145697 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0450CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0451GraphCenterA.qJetBox,
   E8TAxisProd0451GraphCenterB.qJetBox,
   E8TAxisProd0451GraphCenterC.qJetBox,
   E8TAxisProd0451GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0451GraphWholeA.qJetBox,
   E8TAxisProd0451GraphWholeB.qJetBox,
   E8TAxisProd0451GraphWholeC.qJetBox,
   E8TAxisProd0451GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨16064604945588811549376805021098083380763801956, 16064604945588811549376805021098176066949024386⟩
  | 0, 2 => ⟨50176621382344654773465154042230049733411518995, 50176621382344654773465154042230390481029844102⟩
  | 1, 1 => ⟨50858763410622448938997628244519142200000668252, 50858763410622448938997628244519748254753291524⟩
  | 0, 3 => ⟨107785560506481300181430062360649127139824429894, 107785560506481300181430062360650219402505087873⟩
  | 1, 2 => ⟨146291809523852241971167678622550371508044905958, 146291809523852241971167678622552302925124888675⟩
  | 2, 1 => ⟨148032411825717010752023020942416237599195256840, 148032411825717010752023020942419717410802058009⟩
  | 0, 4 => ⟨191554936101377090066246878092864944510664206482, 191554936101377090066246878092868598739581781625⟩
  | 1, 3 => ⟨288668170996106123294434319009570598805713173553, 288668170996106123294434319009577167181406547176⟩
  | 2, 2 => ⟨386685846990703529749885489319564689948920161207, 386685846990703529749885489319576696200904240197⟩
  | 3, 1 => ⟨390651603173868673422501882347453771418948607402, 390651603173868673422501882347475913477313625281⟩
  | 0, 5 => ⟨-692291763128525750404876871331286384023571096561265, 696397243141356184699851825028915133921169501823595⟩
  | 1, 4 => ⟨-1350296313556433727246808098707960729739552564011284, 1356441753308590653999706377543030523933891521841160⟩
  | 2, 3 => ⟨-2636782007350753221607929693816234617340878404689560, 2645600647932327163458913816674839158633670501254202⟩
  | 3, 2 => ⟨-5152689355586737996476564743686277581720788376553222, 5164241229057794679205870905982799688601962934367407⟩
  | 4, 1 => ⟨-10074432580697859633213010988353434752303681174412697, 10086247760117049148936247898347605963245722184678477⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0451Geometry.ds, E8TAxisProd0451Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 15046379289844266676197477325295870655348132987 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0451CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0452GraphCenterA.qJetBox,
   E8TAxisProd0452GraphCenterB.qJetBox,
   E8TAxisProd0452GraphCenterC.qJetBox,
   E8TAxisProd0452GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0452GraphWholeA.qJetBox,
   E8TAxisProd0452GraphWholeB.qJetBox,
   E8TAxisProd0452GraphWholeC.qJetBox,
   E8TAxisProd0452GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14386030437137462789050474069782307395325835653, 14386030437137462789050474069782391968531389059⟩
  | 0, 2 => ⟨45284487522591706083170235731569515541969276749, 45284487522591706083170235731569823042346940371⟩
  | 1, 1 => ⟨45950551683192426308274059550763438392823970061, 45950551683192426308274059550763983350991133464⟩
  | 0, 3 => ⟨98064504936558533703364559128007372732420248859, 98064504936558533703364559128008354289330543827⟩
  | 1, 2 => ⟨133300639468344500213183626478250593063274502933, 133300639468344500213183626478252323449768554473⟩
  | 2, 1 => ⟨135016818678243846616137829037461542249769562635, 135016818678243846616137829037464653306597593858⟩
  | 0, 4 => ⟨175738102030957827562103046734154414243466537777, 175738102030957827562103046734157684112251532728⟩
  | 1, 3 => ⟨265386891794610880262726157501470563132238686926, 265386891794610880262726157501476426324394656628⟩
  | 2, 2 => ⟨355938646802893788023382445235900758168456030278, 355938646802893788023382445235911457191276504932⟩
  | 3, 1 => ⟨359884871577426096217723331847319208738548547888, 359884871577426096217723331847338910703723435418⟩
  | 0, 5 => ⟨-606065089746055613640928842508154182430450089221016, 609713989168740836387080064003798897759211148488335⟩
  | 1, 4 => ⟨-1181199195630359211714441538243259785158502446325590, 1186651978537705063370856243091317779222109860566823⟩
  | 2, 3 => ⟨-2304895404949884448019762049002008700403920404995580, 2312710865175996127360566255348302098911952833559593⟩
  | 3, 2 => ⟨-4500922172826048772805956162562271396267209158919826, 4511152441678863565537225903697466930330476849855335⟩
  | 4, 1 => ⟨-8793884273760319321677829291991753688560570580909192, 8804344189371836426282167707018987549186923908447882⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0452Geometry.ds, E8TAxisProd0452Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13467312255043813567126199873647724421402180816 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0452CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0453GraphCenterA.qJetBox,
   E8TAxisProd0453GraphCenterB.qJetBox,
   E8TAxisProd0453GraphCenterC.qJetBox,
   E8TAxisProd0453GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0453GraphWholeA.qJetBox,
   E8TAxisProd0453GraphWholeB.qJetBox,
   E8TAxisProd0453GraphWholeC.qJetBox,
   E8TAxisProd0453GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12819144464627587316838176932805295438386703156, 12819144464627587316838176932805372508321747772⟩
  | 0, 2 => ⟨40717415866912669923932558034777084153030829861, 40717415866912669923932558034777361113189777257⟩
  | 1, 1 => ⟨41324292112180996777859680617326233572572974239, 41324292112180996777859680617326722543514741693⟩
  | 0, 3 => ⟨88929500861814990922341798061453445047799914857, 88929500861814990922341798061454325188152438387⟩
  | 1, 2 => ⟨121042341665893010118947163273959093214715181581, 121042341665893010118947163273960639831825541286⟩
  | 2, 1 => ⟨122621767539348751778913492104853908622889566149, 122621767539348751778913492104856683167947969280⟩
  | 0, 4 => ⟨160766661132582267440495241517610678764411707182, 160766661132582267440495241517613597564171272768⟩
  | 1, 3 => ⟨243278602830038348468673343746801225833133930637, 243278602830038348468673343746806446005967680794⟩
  | 2, 2 => ⟨326632656675953295011621897032427213759131529614, 326632656675953295011621897032436722384754683717⟩
  | 3, 1 => ⟨330300219494970424146895569365413441094801429336, 330300219494970424146895569365430923827598524624⟩
  | 0, 5 => ⟨-527082504550335033369749254955607758320683367270903, 530313614242079122342377074175212766663753393486148⟩
  | 1, 4 => ⟨-1026400884070142779034512508071022998689927960444476, 1031220679807900415665352734233847676249514330856405⟩
  | 2, 3 => ⟨-2001251620389555501536889978398518306498796146503608, 2008151293124671788407998214611922637178583639772141⟩
  | 3, 2 => ⟨-3904969138018826681582428420991099225820183449104509, 3913993806389947744382523855172419663494801288388008⟩
  | 4, 1 => ⟨-7623689086547285070184281811448373330562199606183480, 7632912867636671675640603653514753951648888432540292⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0453Geometry.ds, E8TAxisProd0453Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11994039884426993572254756236295531028666571556 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0453CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0454GraphCenterA.qJetBox,
   E8TAxisProd0454GraphCenterB.qJetBox,
   E8TAxisProd0454GraphCenterC.qJetBox,
   E8TAxisProd0454GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0454GraphWholeA.qJetBox,
   E8TAxisProd0454GraphWholeB.qJetBox,
   E8TAxisProd0454GraphWholeC.qJetBox,
   E8TAxisProd0454GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14329501383450221871323453926084203636152551167, 14329501383450221871323453926084288037963681823⟩
  | 0, 2 => ⟨45162044097443510823666326764098468622055149302, 45162044097443510823666326764098775443959402390⟩
  | 1, 1 => ⟨45784133076438278682500030889837421597308699023, 45784133076438278682500030889837965331315756853⟩
  | 0, 3 => ⟨97845046765398527978338343065512741812431817978, 97845046765398527978338343065513721165080015932⟩
  | 1, 2 => ⟨132969244030585302891326875420837841118729679738, 132969244030585302891326875420839567562470243140⟩
  | 2, 1 => ⟨134572394331941274845595444552141210402406927399, 134572394331941274845595444552144314284461747364⟩
  | 0, 4 => ⟨175395070761024357084075284108785352430281607943, 175395070761024357084075284108788614679035902393⟩
  | 1, 3 => ⟨264845968759160871876211994735850152602507496498, 264845968759160871876211994735856002026152576444⟩
  | 2, 2 => ⟨355140552377775812713045906738440129937168805191, 355140552377775812713045906738450803644905061231⟩
  | 3, 1 => ⟨358827490284891430723134968004551075852481915057, 358827490284891430723134968004570730827103190339⟩
  | 0, 5 => ⟨-604393109241312716963603188301922706073922669244715, 608033583330705513981930072120926440275169266124646⟩
  | 1, 4 => ⟨-1177923513441696367512865700423715978747569793470383, 1183363609222324199167151054616481769675675850519847⟩
  | 2, 3 => ⟨-2298470254708234505701885548410952072012129634156293, 2306267506556885820060798180486909501968758008303401⟩
  | 3, 2 => ⟨-4488309508238070202634608701888393989719615923826428, 4498515895446429855306236898025139092084345643212811⟩
  | 4, 1 => ⟨-8769110843259531540898136773429782490350418406126852, 8779545654905306735792242077579090480084454294009547⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0454Geometry.ds, E8TAxisProd0454Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13414042239130410401527434585206856662433663758 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0454CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0455GraphCenterA.qJetBox,
   E8TAxisProd0455GraphCenterB.qJetBox,
   E8TAxisProd0455GraphCenterC.qJetBox,
   E8TAxisProd0455GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0455GraphWholeA.qJetBox,
   E8TAxisProd0455GraphWholeB.qJetBox,
   E8TAxisProd0455GraphWholeC.qJetBox,
   E8TAxisProd0455GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12768317118659359514418185617422431689046252558, 12768317118659359514418185617422508603365796436⟩
  | 0, 2 => ⟨40606379507357388646966041581356950174660341718, 40606379507357388646966041581357226523537767964⟩
  | 1, 1 => ⟨41173179116206321304051181979174165360900854260, 41173179116206321304051181979174653232001503474⟩
  | 0, 3 => ⟨88728740343595113212564793072805500931671745399, 88728740343595113212564793072806379092397707171⟩
  | 1, 2 => ⟨120738556087710424630219826764134820904446275783, 120738556087710424630219826764136363988882481670⟩
  | 2, 1 => ⟨122213938830154670694122345571241880790872205018, 122213938830154670694122345571244648917751080913⟩
  | 0, 4 => ⟨160450259709807022621524760224919469159895566250, 160450259709807022621524760224922381138403436291⟩
  | 1, 3 => ⟨242778471016925615560224137917331998275863072931, 242778471016925615560224137917337206146461605811⟩
  | 2, 2 => ⟨325893506092462231550732076520585175094383137495, 325893506092462231550732076520594661128465649951⟩
  | 3, 1 => ⟨329320069502317450095515216586135096203378801661, 329320069502317450095515216586152537045014198835⟩
  | 0, 5 => ⟨-525590268447447009326627489190110118155839601552545, 528813888844193650355078854176405791326245949171723⟩
  | 1, 4 => ⟨-1023478990069688831843705818142484333817489758958542, 1028287542199560845928962128581677268389419859809409⟩
  | 2, 3 => ⟨-1995523508086320766488419213912963602540187798539230, 2002407110116521171625643523016008373050805556256592⟩
  | 3, 2 => ⟨-3893730741529085247315098616352945174713005261010336, 3902734478394490400402315678011011166391295710965285⟩
  | 4, 1 => ⟨-7601626633444610808024160748732266309635735362828116, 7610828805045993525099366961409928604985285634877181⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0455Geometry.ds, E8TAxisProd0455Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11946170476224319589010522200922569512719714282 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0455CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0456GraphCenterA.qJetBox,
   E8TAxisProd0456GraphCenterB.qJetBox,
   E8TAxisProd0456GraphCenterC.qJetBox,
   E8TAxisProd0456GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0456GraphWholeA.qJetBox,
   E8TAxisProd0456GraphWholeB.qJetBox,
   E8TAxisProd0456GraphWholeC.qJetBox,
   E8TAxisProd0456GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17921499764679904845579088423340985943029405480, 17921499764679904845579088423341087590631811668⟩
  | 0, 2 => ⟨55542763971243898396301127195356215449594535797, 55542763971243898396301127195356593133197427125⟩
  | 1, 1 => ⟨56237444987473436315861139370441684151105692960, 56237444987473436315861139370442358213721557192⟩
  | 0, 3 => ⟨118354613126748359667587647731476504112012777109, 118354613126748359667587647731477719630875676910⟩
  | 1, 2 => ⟨160399255701263055789773845314630030960583802763, 160399255701263055789773845314632186603383126231⟩
  | 2, 1 => ⟨162154964813947798270288676508090629918544012491, 162154964813947798270288676508094521672320081971⟩
  | 0, 4 => ⟨208619017826757111594885153739797632545869722337, 208619017826757111594885153739801716026704932359⟩
  | 1, 3 => ⟨313743730761787398791104055165164114769274965261, 313743730761787398791104055165171471805196393324⟩
  | 2, 2 => ⟨419769904337011502532775843550131518501609227172, 419769904337011502532775843550144988492016622041⟩
  | 3, 1 => ⟨423735264739697270398052447635790557116690039333, 423735264739697270398052447635815434594800560483⟩
  | 0, 5 => ⟨-787773875517212766304795825148465256449431157592625, 792387234673574194259041548200221222904829108341632⟩
  | 1, 4 => ⟨-1537646259285560699618817205298330898303744578806185, 1544563062876174039354402564468288693349294440505533⟩
  | 2, 3 => ⟨-3004694101090183067691006084846483371082833471887460, 3014630883454186114857185615933934974175527048227142⟩
  | 3, 2 => ⟨-5875602588342531609983891182526637474014288545719842, 5888628352875101448816214006901177319699945817118685⟩
  | 4, 1 => ⟨-11495558660206727620262271128810678582743992495578053, 11508885796699534433294632990926169463704558925337430⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0456Geometry.ds, E8TAxisProd0456Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16794167184539288342643577530737678370507201062 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0456CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0457GraphCenterA.qJetBox,
   E8TAxisProd0457GraphCenterB.qJetBox,
   E8TAxisProd0457GraphCenterC.qJetBox,
   E8TAxisProd0457GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0457GraphWholeA.qJetBox,
   E8TAxisProd0457GraphWholeB.qJetBox,
   E8TAxisProd0457GraphWholeC.qJetBox,
   E8TAxisProd0457GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨16001968314005116566720592085664909381821702545, 16001968314005116566720592085665001879529792641⟩
  | 0, 2 => ⟨50042038987333467358710143621855512337260962847, 50042038987333467358710143621855852333369883542⟩
  | 1, 1 => ⟨50676124018645248114929867816753096413475543051, 50676124018645248114929867816753701108695397334⟩
  | 0, 3 => ⟨107546348815639580434511733269613026313193095066, 107546348815639580434511733269614116126335392971⟩
  | 1, 2 => ⟨145931339250651882679026129089123769244021721596, 145931339250651882679026129089125696270044185120⟩
  | 2, 1 => ⟨147549592055123616560221837796890198436295080930, 147549592055123616560221837796893670245090510533⟩
  | 0, 4 => ⟨191183875823656420853076992513696209512073591914, 191183875823656420853076992513699855241988205301⟩
  | 1, 3 => ⟨288084438250481742969413001855658277559526761392, 288084438250481742969413001855664830552693962508⟩
  | 2, 2 => ⟨385826048977111438424902103988777653819775551831, 385826048977111438424902103988789631757149322691⟩
  | 3, 1 => ⟨389513631915080047243545635576675287444423459577, 389513631915080047243545635576697376892075316627⟩
  | 0, 5 => ⟨-690431661999825658193087397459589470072402988166715, 694527686377596792696649334692279435216970613024061⟩
  | 1, 4 => ⟨-1346650200960223707607157834873723100484806331277366, 1352781358978330059666416279483136310665582902337892⟩
  | 2, 3 => ⟨-2629626714825640538473865904739755937325682222339678, 2638424773225995915338532912115018348689220689180008⟩
  | 3, 2 => ⟨-5138636515591348713224212754796076386083398227880995, 5150161203886510402370961400276169772447143236798697⟩
  | 4, 1 => ⟨-10046816865555964780989593105424124848701576333797629, 10058602959284009662825301913925697025398122841942862⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0457Geometry.ds, E8TAxisProd0457Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14987320622353433586725266051112328083805728528 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0457CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0458GraphCenterA.qJetBox,
   E8TAxisProd0458GraphCenterB.qJetBox,
   E8TAxisProd0458GraphCenterC.qJetBox,
   E8TAxisProd0458GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0458GraphWholeA.qJetBox,
   E8TAxisProd0458GraphWholeB.qJetBox,
   E8TAxisProd0458GraphWholeC.qJetBox,
   E8TAxisProd0458GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17852163706380184197888973101804583383774784701, 17852163706380184197888973101804684824022479745⟩
  | 0, 2 => ⟨55394983583922558387040213191879982568667434519, 55394983583922558387040213191880359419771641234⟩
  | 1, 1 => ⟨56037190866086324508455027512658132233477198261, 56037190866086324508455027512658804786237319114⟩
  | 0, 3 => ⟨118094090167979860334379010116358241169875292993, 118094090167979860334379010116359453967252880418⟩
  | 1, 2 => ⟨160007469700439977730839111754620521450710489192, 160007469700439977730839111754622672204432859973⟩
  | 2, 1 => ⟨161630831325529150854551667868192220660872063056, 161630831325529150854551667868196103490658355641⟩
  | 0, 4 => ⟨208217831004438738595758057867578806683720097678, 208217831004438738595758057867582880693328963834⟩
  | 1, 3 => ⟨313114055575616464999770373274107833604475690430, 313114055575616464999770373274115173468240663819⟩
  | 2, 2 => ⟨418843959431968097874345708300619931987589231182, 418843959431968097874345708300633370332172525009⟩
  | 3, 1 => ⟨422510958874192572269299780816509148047771685373, 422510958874192572269299780816533966666290525556⟩
  | 0, 5 => ⟨-785714284256448816921339037394404343170990391449661, 790317032002136853867624750956647364411906458723935⟩
  | 1, 4 => ⟨-1533607198322498741373297741438050738355578350732784, 1540507922221441108015042448958008233366619322096856⟩
  | 2, 3 => ⟨-2996764004370149216375469588544883731508322255683790, 3006677509808466012692562528475599820307838389566562⟩
  | 3, 2 => ⟨-5860020900852893686718309291196969281762247296548361, 5873015690702195227102482018794548111796891760050063⟩
  | 4, 1 => ⟨-11464924468874115784272678765903932995850805460002124, 11478217854591474401372344436138842889069422529676208⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0458Geometry.ds, E8TAxisProd0458Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16728755052192401665116676824408942598761174592 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0458CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0459GraphCenterA.qJetBox,
   E8TAxisProd0459GraphCenterB.qJetBox,
   E8TAxisProd0459GraphCenterC.qJetBox,
   E8TAxisProd0459GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0459GraphWholeA.qJetBox,
   E8TAxisProd0459GraphWholeB.qJetBox,
   E8TAxisProd0459GraphWholeC.qJetBox,
   E8TAxisProd0459GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15939499723651787925321473312209755247636607784, 15939499723651787925321473312209847557251687753⟩
  | 0, 2 => ⟨49907755317211452937896480480028176604479648695, 49907755317211452937896480480028515850699395928⟩
  | 1, 1 => ⟨50493934758737177182359570765938984256352743969, 50493934758737177182359570765939587594998049783⟩
  | 0, 3 => ⟨107307600550686850423633298860912609153344174155, 107307600550686850423633298860913696522338069805⟩
  | 1, 2 => ⟨145571597998262775065433018122188249901817160606, 145571597998262775065433018122190172546495987052⟩
  | 2, 1 => ⟨147067846046280680089240881838749617869376454766, 147067846046280680089240881838753081693141694457⟩
  | 0, 4 => ⟨190813454510725593801325782826120585269802446498, 190813454510725593801325782826124222519951409428⟩
  | 1, 3 => ⟨287501737416776140714218295526423742883626285232, 287501737416776140714218295526430280529138299400⟩
  | 2, 2 => ⟨384967827748190860426649108404790163048207138807, 384967827748190860426649108404802112735220406466⟩
  | 3, 1 => ⟨388377935162346300156203897949914885932024873560, 388377935162346300156203897949936922888524800601⟩
  | 0, 5 => ⟨-688575595046379521411999395280192701859125904827375, 692662186295007956921305814864230695574267086947051⟩
  | 1, 4 => ⟨-1343012017734389023672390017735864831028839513061699, 1349128929302690315969731742351060893015138428595979⟩
  | 2, 3 => ⟨-2622487028193711751517442490374447302328096810695642, 2631264558000742614533684606565478806323175176934098⟩
  | 3, 2 => ⟨-5124614416952202238865568163973894522088452831627390, 5136111997692627724025716136965925238265256517071283⟩
  | 4, 1 => ⟨-10019261746427087629620973890619009078669437607699432, 10031018857792117744062831215697453761197895961256850⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0459Geometry.ds, E8TAxisProd0459Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14928421254308768089680963864966847292994730903 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0459CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0460GraphCenterA.qJetBox,
   E8TAxisProd0460GraphCenterB.qJetBox,
   E8TAxisProd0460GraphCenterC.qJetBox,
   E8TAxisProd0460GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0460GraphWholeA.qJetBox,
   E8TAxisProd0460GraphWholeB.qJetBox,
   E8TAxisProd0460GraphWholeC.qJetBox,
   E8TAxisProd0460GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14273125212704335510442375944345791850085665556, 14273125212704335510442375944345876080851023410⟩
  | 0, 2 => ⟨45039874727170612361217396847594761417989335376, 45039874727170612361217396847595067562884308534⟩
  | 1, 1 => ⟨45618128291635323734608864260397701508589407977, 45618128291635323734608864260398244021104634834⟩
  | 0, 3 => ⟨97626017012511334512979594624614185640288726162, 97626017012511334512979594624615162793530656843⟩
  | 1, 2 => ⟨132638524146425815935301365362150304868592545559, 132638524146425815935301365362152027378316943505⟩
  | 2, 1 => ⟨134128966685071488775214185071770788846215780963, 134128966685071488775214185071773885569473591018⟩
  | 0, 4 => ⟨175052632638268435404405797833007221618732564655, 175052632638268435404405797833010476264723082853⟩
  | 1, 3 => ⟨264306005773670614739594335314719577472736245249, 264306005773670614739594335314725413159133785396⟩
  | 2, 2 => ⟨354343927299798455332732505218795481860336115181, 354343927299798455332732505218806130310546644095⟩
  | 3, 1 => ⟨357772230942724636026792045174930707310432252677, 357772230942724636026792045174950315401537625002⟩
  | 0, 5 => ⟨-602724903110076843370818521724769819270259774080565, 606356971747243457762642316632084500970272253523055⟩
  | 1, 4 => ⟨-1174655248166909186329428815707819632149556438708261, 1180082687778198337680846679135925348727349104843536⟩
  | 2, 3 => ⟨-2292059697971750695355968755503314337091320223237778, 2299838788025670100359910324042585451206795438261664⟩
  | 3, 2 => ⟨-4475725582839733452963776089057383370191601356731038, 4485908154929289791212945406342140944934873002012411⟩
  | 4, 1 => ⟨-8744394045995301593317805383665715116647355567097212, 8754803840005181205416029516069313432772584795719303⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0460Geometry.ds, E8TAxisProd0460Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13360917063983228807198130294110903300594909451 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0460CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0461GraphCenterA.qJetBox,
   E8TAxisProd0461GraphCenterB.qJetBox,
   E8TAxisProd0461GraphCenterC.qJetBox,
   E8TAxisProd0461GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0461GraphWholeA.qJetBox,
   E8TAxisProd0461GraphWholeB.qJetBox,
   E8TAxisProd0461GraphWholeC.qJetBox,
   E8TAxisProd0461GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12717628411399371452469042951226300267212831321, 12717628411399371452469042951226377026232783157⟩
  | 0, 2 => ⟨40495593851404480662804692694077360448514453202, 40495593851404480662804692694077636187430758597⟩
  | 1, 1 => ⟨41022445461708729741012563478827894802726891651, 41022445461708729741012563478828381576388100241⟩
  | 0, 3 => ⟨88528374983494962664320900504603444581876363599, 88528374983494962664320900504604320767342641817⟩
  | 1, 2 => ⟨120435395116766793668490524653856054257113708081, 120435395116766793668490524653857593816719716345⟩
  | 2, 1 => ⟨121807033204449311125613124979387460266462475405, 121807033204449311125613124979390221989487984054⟩
  | 0, 4 => ⟨160134407996299883908684018210260529395931855409, 160134407996299883908684018210263434568672105181⟩
  | 1, 3 => ⟨242279231005255593943070745529752821260626409520, 242279231005255593943070745529758016856987381361⟩
  | 2, 2 => ⟨325155722712982369296315559936423389855575016569, 325155722712982369296315559936432853349618895270⟩
  | 3, 1 => ⟨328341896264016962443431690116000704002095230864, 328341896264016962443431690116018103048276678548⟩
  | 0, 5 => ⟨-524101536558377655922797490969696281002444929440902, 527317685263766736453433855900446289718270580645416⟩
  | 1, 4 => ⟨-1020563980103170562531424771760232955010589500087175, 1025361315875366702817143127762410702030887275893636⟩
  | 2, 3 => ⟨-1989808936670751559313280306852964720207405563708859, 1996676508671606170958653279219434888627395883380512⟩
  | 3, 2 => ⟨-3882519002884297184048894394654722485928224025737049, 3891501865618685433974475089804889188600679999820286⟩
  | 4, 1 => ⟨-7579616695062899365049116698207160054071689199056875, 7588797329933517728298292082308419622932353425141365⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0461Geometry.ds, E8TAxisProd0461Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11898432330580030238680137718048394330094099525 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0461CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0462GraphCenterA.qJetBox,
   E8TAxisProd0462GraphCenterB.qJetBox,
   E8TAxisProd0462GraphCenterC.qJetBox,
   E8TAxisProd0462GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0462GraphWholeA.qJetBox,
   E8TAxisProd0462GraphWholeB.qJetBox,
   E8TAxisProd0462GraphWholeC.qJetBox,
   E8TAxisProd0462GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14216901582665718355524237857988258757706259892, 14216901582665718355524237857988342817773778824⟩
  | 0, 2 => ⟨44917978876713321955534253177740422353319077840, 44917978876713321955534253177740727822665778075⟩
  | 1, 1 => ⟨45452536485091192575942933800593404720646297338, 45452536485091192575942933800593946014332267090⟩
  | 0, 3 => ⟨97407414937048407920439850454404317144749231134, 97407414937048407920439850454405292103430115660⟩
  | 1, 2 => ⟨132308478616783336698835074748701003311876118631, 132308478616783336698835074748702721896302588529⟩
  | 2, 1 => ⟨133686533902489602090699306103419341106646639022, 133686533902489602090699306103422430687048766722⟩
  | 0, 4 => ⟨174710786726235620543953060377023100341093274992, 174710786726235620543953060377026347401548277300⟩
  | 1, 3 => ⟨263767001270958132355087897901181727534930442993, 263767001270958132355087897901187549515273952387⟩
  | 2, 2 => ⟨353548769107181447637207414938028818970117391436, 353548769107181447637207414938039442220232408241⟩
  | 3, 1 => ⟨356719089866549052368241661429769967893310672491, 356719089866549052368241661429789529207699809165⟩
  | 0, 5 => ⟨-601060466420828408635652642555372824422244343830142, 604684148769510536320442391632786118950573230236275⟩
  | 1, 4 => ⟨-1171394389473472874088065201483285777053894460939145, 1176809202954789177629247119583762472776970389118751⟩
  | 2, 3 => ⟨-2285663713611929029844522111285383675531883119513235, 2293424687283797942405895994340705897876890768965841⟩
  | 3, 2 => ⟨-4463170354028264149573149106226078805166758304859142, 4473329176046082518587165252838595826569634778557214⟩
  | 4, 1 => ⟨-8719733796769304321343747104598533399670231047736379, 8730118657615787462226367921700312854062469348934287⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0462Geometry.ds, E8TAxisProd0462Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13307936403581878191559275584234781644291028390 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0462CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0463GraphCenterA.qJetBox,
   E8TAxisProd0463GraphCenterB.qJetBox,
   E8TAxisProd0463GraphCenterC.qJetBox,
   E8TAxisProd0463GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0463GraphWholeA.qJetBox,
   E8TAxisProd0463GraphWholeB.qJetBox,
   E8TAxisProd0463GraphWholeC.qJetBox,
   E8TAxisProd0463GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12667078029776658574235372227266617554425711224, 12667078029776658574235372227266694158461331725⟩
  | 0, 2 => ⟨40385058405535530637713880761786674098946872128, 40385058405535530637713880761786949229219638545⟩
  | 1, 1 => ⟨40872090368625514586151361944832081893651618564, 40872090368625514586151361944832567572269928110⟩
  | 0, 3 => ⟨88328404094920385069292551300322477596384201940, 88328404094920385069292551300323351810948131121⟩
  | 1, 2 => ⟨120132857639219041444310935569186764334262059591, 120132857639219041444310935569188300376864681006⟩
  | 2, 1 => ⟨121401048954655677423381641703359814596283203940, 121401048954655677423381641703362569929750203879⟩
  | 0, 4 => ⟨159819105124383356760793427096861028618630182114, 159819105124383356760793427096863927001052221173⟩
  | 1, 3 => ⟨241780881341448469404823568272126109652089384918, 241780881341448469404823568272131293002147905534⟩
  | 2, 2 => ⟨324419304253318966897287022053639500549849694488, 324419304253318966897287022053648941555242149884⟩
  | 3, 1 => ⟨327365696361651539079472919806228340426400280680, 327365696361651539079472919806245697772622616827⟩
  | 0, 5 => ⟨-522616303111905802445351540786709714313404904882173, 525824997686417837383935606704165803985699263134632⟩
  | 1, 4 => ⟨-1017655842834780304516706898439199156535337967643730, 1022441989431289841745991446581375991835550804738837⟩
  | 2, 3 => ⟨-1984107883823765862448315914916180705695167429277090, 1990959466359725600415985935810733847613665722384465⟩
  | 3, 2 => ⟨-3871333878084354556645178032621411366835985539997269, 3880295923888827422768301253571978081582977143195652⟩
  | 4, 1 => ⟨-7557659184588515609546843192386689676266795042008615, 7566818355222673476693359194728346840822238276639390⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0463Geometry.ds, E8TAxisProd0463Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11850825149445860128382413048835202218189869926 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0463CertifiedArithmetic

end


