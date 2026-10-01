-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:48:34.705425+00:00
-- url     : https://prove2.me/theorems/3774eaf1-abdb-4083-b36a-1c106a9cb411
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 1 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 1 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 1 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0104CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0105CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0106CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0107CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0108CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0109CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0110CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0111CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0112CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0113CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0114CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0115CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0116CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0117CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0118CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0119CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0120CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0121CertifiedArithmetic) (piece 1 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0094GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0095GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0100GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0092GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0099GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0089GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0097GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0095GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0101Geometry__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0104GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0107GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0110GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0110GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0110GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0112GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0114GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0114GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0119GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0120GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0120GraphWholeB__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0103GraphCenterA.qJetBox,
   E8TAxisProd0103GraphCenterB.qJetBox,
   E8TAxisProd0103GraphCenterC.qJetBox,
   E8TAxisProd0103GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0103GraphWholeA.qJetBox,
   E8TAxisProd0103GraphWholeB.qJetBox,
   E8TAxisProd0103GraphWholeC.qJetBox,
   E8TAxisProd0103GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1203108720477705928452540064297572501187755637, 1203108720477705928452540064297588755724753625⟩
  | 0, 2 => ⟨4575919579057638308898313694527236324030278750, 4575919579057638308898313694527280720068324545⟩
  | 1, 1 => ⟨4650853480582728649760506737705565852247996418, 4650853480582728649760506737705636280582617171⟩
  | 0, 3 => ⟨11588716506824186029433564769119288794909235201, 11588716506824186029433564769119414729911414504⟩
  | 1, 2 => ⟨16316953533688770049128726490339391188483218885, 16316953533688770049128726490339592992275883303⟩
  | 2, 1 => ⟨16550783667269366460287717203458149266275690154, 16550783667269366460287717203458492196298078188⟩
  | 0, 4 => ⟨24405828511790404559527263529931714350238647875, 24405828511790404559527263529932095587126851361⟩
  | 1, 3 => ⟨38964779941084188571417288282802696144178445477, 38964779941084188571417288282803326612874535003⟩
  | 2, 2 => ⟨53691162366332930554530086945192095637273911849, 53691162366332930554530086945193190850638485888⟩
  | 3, 1 => ⟨54364534965684399082062747958932987668927831187, 54364534965684399082062747958934926918405784787⟩
  | 0, 5 => ⟨-259805906738432707290590466323761060711475198961591, 261221911925853538817782924478285273179648017253365⟩
  | 1, 4 => ⟨-502291827605074874857289606681578833788649471257115, 504310254121169037121800747944538581596365251370264⟩
  | 2, 3 => ⟨-972641571700874113273168146701990380014227975094338, 975463889210748308651371575603696962863125870158416⟩
  | 3, 2 => ⟨-1884897890336415660251399681870587913051212613890757, 1888588780414631328931790452164999262553211320152086⟩
  | 4, 1 => ⟨-3654216306103985323497711789004337065065871968333831, 3658174881254334334842644595909892246988793477330611⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0103Geometry.ds, E8TAxisProd0103Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 885264135405771029649241794625154626334704912 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic

end


