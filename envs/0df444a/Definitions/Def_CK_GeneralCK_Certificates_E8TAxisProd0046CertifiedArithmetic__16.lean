-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0046CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0046CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:39:03.534764+00:00
-- url     : https://prove2.me/theorems/d9a4ee4a-bdb7-4731-bc0b-0a1e36d4bf2f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0046CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0047CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0048CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0049CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0050CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0051CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0052CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0053CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0054CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0055CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0056CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0057CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0058CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0059CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0060CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0061CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0042GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0043GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0038GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0042GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0034GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0046GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0025Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0047GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0047GraphWholeB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0047GraphWholeD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0049Geometry__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0056Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0058GraphCenterA__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0046GraphCenterA.qJetBox,
   E8TAxisProd0046GraphCenterB.qJetBox,
   E8TAxisProd0046GraphCenterC.qJetBox,
   E8TAxisProd0046GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0046GraphWholeA.qJetBox,
   E8TAxisProd0046GraphWholeB.qJetBox,
   E8TAxisProd0046GraphWholeC.qJetBox,
   E8TAxisProd0046GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨114073229975550002625611521573516828812508, 114073229975550002625611521574861808691960⟩
  | 0, 2 => ⟨1556351688477045652566971943581722713754135, 1556351688477045652566971943585425582574763⟩
  | 1, 1 => ⟨1683491923626785934596426220548375257119445, 1683491923626785934596426220552862386829147⟩
  | 0, 3 => ⟨11073241351285328018561278222922508243183009, 11073241351285328018561278222928706052056024⟩
  | 1, 2 => ⟨18917452476060828680473711211172434246701522, 18917452476060828680473711211179363355073226⟩
  | 2, 1 => ⟨20094061862353666247970923147619064521935135, 20094061862353666247970923147628108571868435⟩
  | 0, 4 => ⟨38335418995607088151115805013901462344748401, 38335418995607088151115805013919020827106231⟩
  | 1, 3 => ⟨105870264632804364787814434251000776665214466, 105870264632804364787814434251020535887753110⟩
  | 2, 2 => ⟨176904075898180461636251346897869822055704318, 176904075898180461636251346897896143371356416⟩
  | 3, 1 => ⟨184556839554267912658114251144370125202466039, 184556839554267912658114251144410084797343355⟩
  | 0, 5 => ⟨-390803055689188845216073033079514567578936486490, 392876801657887992199654964635154017215013297508⟩
  | 1, 4 => ⟨-629810031242692809803928809540866184552599709091, 627162002351286806357706487237192951009752612176⟩
  | 2, 3 => ⟨-1049112589208011870475656728244855750926190180680, 1040698851946637533637925371424335542558770318831⟩
  | 3, 2 => ⟨-1759808410739279454923676528716451476037139323101, 1746021761402970369174366812337715832866736900986⟩
  | 4, 1 => ⟨-2929737650394236147408888102792233820158186344814, 2917421549107302490290898775631419215688123301429⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0046Geometry.ds, E8TAxisProd0046Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 69975046494951949011665628770826760416485 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0046CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0047GraphCenterA.qJetBox,
   E8TAxisProd0047GraphCenterB.qJetBox,
   E8TAxisProd0047GraphCenterC.qJetBox,
   E8TAxisProd0047GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0047GraphWholeA.qJetBox,
   E8TAxisProd0047GraphWholeB.qJetBox,
   E8TAxisProd0047GraphWholeC.qJetBox,
   E8TAxisProd0047GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨166464998926223400845094921848433996214854, 166464998926223400845094921849857921282953⟩
  | 0, 2 => ⟨2166952381270894331483411730223847513940038, 2166952381270894331483411730227667123175020⟩
  | 1, 1 => ⟨2284308302674387174836247753001826191804081, 2284308302674387174836247753006458359190211⟩
  | 0, 3 => ⟨14516088945796969136873437947130557476435466, 14516088945796969136873437947137073138303551⟩
  | 1, 2 => ⟨24402958126050822806428449136081139008782838, 24402958126050822806428449136088467148830858⟩
  | 2, 1 => ⟨25409990452766368989482571652012817616668108, 25409990452766368989482571652022480563588430⟩
  | 0, 4 => ⟨47866915848800554335908598065612158691687569, 47866915848800554335908598065630468166824883⟩
  | 1, 3 => ⟨128717908702079694607861057410024955444301903, 128717908702079694607861057410045722525421129⟩
  | 2, 2 => ⟨212329267305985530035140320586482113434631352, 212329267305985530035140320586510031897351033⟩
  | 3, 1 => ⟨218454729657237007675630564828923050704604884, 218454729657237007675630564828965592074824542⟩
  | 0, 5 => ⟨-411764168948517249497652256937500929996545717733, 414869016057590529009678354190735942585352269754⟩
  | 1, 4 => ⟨-666366390813902153800769491074995708029794998084, 664761567746141674314381704636548235023752659697⟩
  | 2, 3 => ⟨-1114141528649464649913006953370333595096738650703, 1106812460518353768899670721061652549134210443110⟩
  | 3, 2 => ⟨-1875792342179382176885574186786730042276444226810, 1863186701703649271562856472829552578516042529176⟩
  | 4, 1 => ⟨-3136059842667718820941568845269539851506030633531, 3125296806376463612033338915891946886206188598930⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0047Geometry.ds, E8TAxisProd0047Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 109822013175619508683444700636872121773991 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0047CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0048GraphCenterA.qJetBox,
   E8TAxisProd0048GraphCenterB.qJetBox,
   E8TAxisProd0048GraphCenterC.qJetBox,
   E8TAxisProd0048GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0048GraphWholeA.qJetBox,
   E8TAxisProd0048GraphWholeB.qJetBox,
   E8TAxisProd0048GraphWholeC.qJetBox,
   E8TAxisProd0048GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨106429089862080896972898427643143668753266, 106429089862080896972898427644476380001741⟩
  | 0, 2 => ⟨1501463502178693680519288118763308943401218, 1501463502178693680519288118766992177642080⟩
  | 1, 1 => ⟨1590221998006240433316144576508272989933793, 1590221998006240433316144576512737862555580⟩
  | 0, 3 => ⟨10882266633746465484152737869277250343264618, 10882266633746465484152737869283395971113176⟩
  | 1, 2 => ⟨18391723292262015096175815693126150410835350, 18391723292262015096175815693133020483168584⟩
  | 2, 1 => ⟨19218645665474773495246963928554621216933090, 19218645665474773495246963928563583242547388⟩
  | 0, 4 => ⟨38055259665289741191256509736576136049655109, 38055259665289741191256509736593573192621983⟩
  | 1, 3 => ⟨104423637569443202552029026041319457195075686, 104423637569443202552029026041339077107061903⟩
  | 2, 2 => ⟨173269054049814519218564391584767801032420641, 173269054049814519218564391584793917209268283⟩
  | 3, 1 => ⟨178680260347560868874972738652948788953199247, 178680260347560868874972738652988414663386125⟩
  | 0, 5 => ⟨-387918662069093846502127587898683160832957811537, 389985006243618318979085354174493631387786725151⟩
  | 1, 4 => ⟨-624729418570983451589898899103825101225068415890, 622153839905642305963184940892951432048606346554⟩
  | 2, 3 => ⟨-1039899777867073096060669079657417283740618557253, 1031645127952470094891930778959035884863357894964⟩
  | 3, 2 => ⟨-1742903347430890665757404321872932114203184504169, 1729378182883292909857026684178401316359528898246⟩
  | 4, 1 => ⟨-2898508299487241014836561169758732945392886989541, 2886642611436922374607717102804825426862937941878⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0048Geometry.ds, E8TAxisProd0048Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 64166536423189366096368843406053257670340 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0048CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0049GraphCenterA.qJetBox,
   E8TAxisProd0049GraphCenterB.qJetBox,
   E8TAxisProd0049GraphCenterC.qJetBox,
   E8TAxisProd0049GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0049GraphWholeA.qJetBox,
   E8TAxisProd0049GraphWholeB.qJetBox,
   E8TAxisProd0049GraphWholeC.qJetBox,
   E8TAxisProd0049GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨70383934404001783974593864648747879390839, 70383934404001783974593864650003760006614⟩
  | 0, 2 => ⟨1045741909854892176703520282349421948056004, 1045741909854892176703520282352994471694485⟩
  | 1, 1 => ⟨1139695549244774555025689274215095431580996, 1139695549244774555025689274219424834568813⟩
  | 0, 3 => ⟨8104927492369596959828441309526272398449622, 8104927492369596959828441309532115239604307⟩
  | 1, 2 => ⟨13941400410634720466113373868372582434372085, 13941400410634720466113373868379077287043751⟩
  | 2, 1 => ⟨14893574269321975995041405901264166439593573, 14893574269321975995041405901272548197805889⟩
  | 0, 4 => ⟨30001076664442464868504478501874384765419717, 30001076664442464868504478501891114853322502⟩
  | 1, 3 => ⟨84625425212972577535928139685403477096613473, 84625425212972577535928139685422159567421813⟩
  | 2, 2 => ⟨142369497739080616051229310016033844818802978, 142369497739080616051229310016058480046029080⟩
  | 3, 1 => ⟨149092611855702106415620366926008221360213008, 149092611855702106415620366926045461694435284⟩
  | 0, 5 => ⟨-368326370178377558493689684295451910754035217194, 369413821485923517878081858759418293048971193895⟩
  | 1, 4 => ⟨-590662021701400169434885103739761280520037548022, 587108241526927404563934644346814708875737002333⟩
  | 2, 3 => ⟨-979442858024566714124317146992752734411833512100, 970184847366091464805482157992911331950983880571⟩
  | 3, 2 => ⟨-1635352926630231251176718049968763911239720605435, 1620747710580668049511821193605421696043493662037⟩
  | 4, 1 => ⟨-2707767333633563912377351612517870225577454536481, 2694469751491559054737550272353492528586272485748⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0049Geometry.ds, E8TAxisProd0049Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 37709011523161826189355061362618445433621 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0049CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0050GraphCenterA.qJetBox,
   E8TAxisProd0050GraphCenterB.qJetBox,
   E8TAxisProd0050GraphCenterC.qJetBox,
   E8TAxisProd0050GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0050GraphWholeA.qJetBox,
   E8TAxisProd0050GraphWholeB.qJetBox,
   E8TAxisProd0050GraphWholeC.qJetBox,
   E8TAxisProd0050GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41323229853151758638894876233304571192571, 41323229853151758638894876234473701883174⟩
  | 0, 2 => ⟨674540171163668430309494634428539594020840, 674540171163668430309494634431988421062466⟩
  | 1, 1 => ⟨741878245892866918627620638561729627064128, 741878245892866918627620638565911541980374⟩
  | 0, 3 => ⟨5753096980515063988219590703069073636505889, 5753096980515063988219590703074577645364379⟩
  | 1, 2 => ⟨9971306694531636236628161408438102978770333, 9971306694531636236628161408444188530824664⟩
  | 2, 1 => ⟨10727018616031489738059235625911362934473963, 10727018616031489738059235625919122723623664⟩
  | 0, 4 => ⟨23033977081019325995687817101017106821282151, 23033977081019325995687817101033055570328028⟩
  | 1, 3 => ⟨66363322918883121323896683667030558433884024, 66363322918883121323896683667048237892708223⟩
  | 2, 2 => ⟨112449902002134827600287011503615228475714705, 112449902002134827600287011503638298736727288⟩
  | 3, 1 => ⟨118310860848378733682213484255602090668366556, 118310860848378733682213484255636816091952424⟩
  | 0, 5 => ⟨-347260356151680107318199219912910463957983976810, 347428905002165656143309308538650904105624581335⟩
  | 1, 4 => ⟨-554092024730618785419078508164121452880108899771, 549709651082270793597496423157394964682229825280⟩
  | 2, 3 => ⟨-914526309417340345842983392278840593039708959162, 904514494954555380758659559284799619862681897937⟩
  | 3, 2 => ⟨-1519691008433941998242625752240090720097090478358, 1504374188860280750220787771787487858943155701377⟩
  | 4, 1 => ⟨-2502074890953287483943844811723594415457202410361, 2487917373649652406368693765625957275338925928397⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0050Geometry.ds, E8TAxisProd0050Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 17213831677813314651912694299611634478338 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0050CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0051GraphCenterA.qJetBox,
   E8TAxisProd0051GraphCenterB.qJetBox,
   E8TAxisProd0051GraphCenterC.qJetBox,
   E8TAxisProd0051GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0051GraphWholeA.qJetBox,
   E8TAxisProd0051GraphWholeB.qJetBox,
   E8TAxisProd0051GraphWholeC.qJetBox,
   E8TAxisProd0051GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨65255912500191093011036546962555360920535, 65255912500191093011036546963799343514134⟩
  | 0, 2 => ⟨1005591427238637232061286798734248939064084, 1005591427238637232061286798737802809361069⟩
  | 1, 1 => ⟨1071041296743676434518370568515006960489980, 1071041296743676434518370568519315367438271⟩
  | 0, 3 => ⟨7955436497966513537599507019861048602175457, 7955436497966513537599507019866841448353170⟩
  | 1, 2 => ⟨13521312009938066291035159286309839010737431, 13521312009938066291035159286316277783806615⟩
  | 2, 1 => ⟨14189578332461432225589620307187223098324114, 14189578332461432225589620307195527573596189⟩
  | 0, 4 => ⟨29795943696174728649053849368291010628391121, 29795943696174728649053849368307625652788482⟩
  | 1, 3 => ⟨83411718571142172474577085079876860401854676, 83411718571142172474577085079895412128812150⟩
  | 2, 2 => ⟨139234667955699869286738304717318651963925477, 139234667955699869286738304717343095960745354⟩
  | 3, 1 => ⟨143985934743057451104665748422755442126978901, 143985934743057451104665748422792372094037882⟩
  | 0, 5 => ⟨-365614780689227720297913759656279468127878902306, 366695004131979077527589282791344562340877197279⟩
  | 1, 4 => ⟨-585895784228445883313380429966765760335979331521, 582413275856141130988821705206989068764409014195⟩
  | 2, 3 => ⟨-970813504904534388224121107520147988980551750501, 961712338048917035370502367598127227481424803395⟩
  | 3, 2 => ⟨-1619540461302106179969857211564449869987632874525, 1605193523348103893419840323628543840296097703006⟩
  | 4, 1 => ⟨-2678594827835895705433448648592638775767663194694, 2665740661453824121075446925657390358888808881758⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0051Geometry.ds, E8TAxisProd0051Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 33962239736450645429557190447719565062744 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0051CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0052GraphCenterA.qJetBox,
   E8TAxisProd0052GraphCenterB.qJetBox,
   E8TAxisProd0052GraphCenterC.qJetBox,
   E8TAxisProd0052GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0052GraphWholeA.qJetBox,
   E8TAxisProd0052GraphWholeB.qJetBox,
   E8TAxisProd0052GraphWholeC.qJetBox,
   E8TAxisProd0052GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38021963598043239395996665464654001266115, 38021963598043239395996665465811587310914⟩
  | 0, 2 => ⟨646062001194787687361645581990209807518954, 646062001194787687361645581993640917940686⟩
  | 1, 1 => ⟨692847033167325853314755459651296530637465, 692847033167325853314755459655458640093485⟩
  | 0, 3 => ⟨5638292362312161230747753534240966320644069, 5638292362312161230747753534246422388997916⟩
  | 1, 2 => ⟨9642020801053559621386589272217967097607388, 9642020801053559621386589272223999319400315⟩
  | 2, 1 => ⟨10171492301081664982586820504472821671699106, 10171492301081664982586820504480508575787577⟩
  | 0, 4 => ⟨22888350490103975852192724707266276708537842, 22888350490103975852192724707282116304181769⟩
  | 1, 3 => ⟨65352434395417016015219184665332351822506715, 65352434395417016015219184665349908519362200⟩
  | 2, 2 => ⟨109765668038337929261054665710515905653267305, 109765668038337929261054665710538797603512190⟩
  | 3, 1 => ⟨113904694215046775597502532557660393195039027, 113904694215046775597502532557694830052947216⟩
  | 0, 5 => ⟨-344706119380189290927757317629822067104616131302, 344870318995934354884025350291156853981117499169⟩
  | 1, 4 => ⟨-549614184055951750889619177488719420399222587309, 545304376878094803091346745302829621611322966771⟩
  | 2, 3 => ⟨-906434484763206700293347379144544563451364037620, 896579340157275044925651192752678896840516799880⟩
  | 3, 2 => ⟨-1504887438293839198133238562943551037866312480429, 1489827115422751321808581203760072211260707450355⟩
  | 4, 1 => ⟨-2474804025093230700709165283449159584106690803355, 2461083522718709533721411784942907386180397486789⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0052Geometry.ds, E8TAxisProd0052Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14929109302878665054545007819391438509939 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0052CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0053GraphCenterA.qJetBox,
   E8TAxisProd0053GraphCenterB.qJetBox,
   E8TAxisProd0053GraphCenterC.qJetBox,
   E8TAxisProd0053GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0053GraphWholeA.qJetBox,
   E8TAxisProd0053GraphWholeB.qJetBox,
   E8TAxisProd0053GraphWholeC.qJetBox,
   E8TAxisProd0053GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨155810692826060855144237762177848085807962, 155810692826060855144237762179259409163350⟩
  | 0, 2 => ⟨2094968736795669120953919337035452144905666, 2094968736795669120953919337039251237428839⟩
  | 1, 1 => ⟨2163895395016551762915266936408337420602946, 2163895395016551762915266936412946162292130⟩
  | 0, 3 => ⟨14277674851676565987391311376267394254052774, 14277674851676565987391311376273855734350721⟩
  | 1, 2 => ⟨23763619725539910438660150793166166274645716, 23763619725539910438660150793173432582921031⟩
  | 2, 1 => ⟨24358728959423085181938619286416964775830745, 24358728959423085181938619286426541164322496⟩
  | 0, 4 => ⟨47499706332497451345602344639150879149453185, 47499706332497451345602344639169061551034945⟩
  | 1, 3 => ⟨127020159125721487018286648349810718925919507, 127020159125721487018286648349831338595858278⟩
  | 2, 2 => ⟨208182878072774988542922298464127306778362783, 208182878072774988542922298464155006792930158⟩
  | 3, 1 => ⟨211822571430088997804960043444409118873410491, 211822571430088997804960043444451303759841095⟩
  | 0, 5 => ⟨-408716646117305342302966062997092525279673197383, 411811670729123659094951453396561599584486059427⟩
  | 1, 4 => ⟨-660986505950709779655983950968482232665656745330, 659452615779660414776612853494726067216674052135⟩
  | 2, 3 => ⟨-1104370855364758800597740788437866309501084609564, 1097199896714578979849233277602465806407230751349⟩
  | 3, 2 => ⟨-1857840309005620815905727444103097293538998138699, 1845495407325189315844563324843411825212220834061⟩
  | 4, 1 => ⟨-3102857678894990682494974574076927549397653486884, 3092546716468008809886293847111746867920872258859⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0053Geometry.ds, E8TAxisProd0053Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 101503674286835600771555835233487191288352 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0053CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0054GraphCenterA.qJetBox,
   E8TAxisProd0054GraphCenterB.qJetBox,
   E8TAxisProd0054GraphCenterC.qJetBox,
   E8TAxisProd0054GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0054GraphWholeA.qJetBox,
   E8TAxisProd0054GraphWholeB.qJetBox,
   E8TAxisProd0054GraphWholeC.qJetBox,
   E8TAxisProd0054GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨99057009308079301575548380516328167711959, 99057009308079301575548380517648663709767⟩
  | 0, 2 => ⟨1447526707236361087902542705752080484828616, 1447526707236361087902542705755744225581548⟩
  | 1, 1 => ⟨1499562691000249223335548333897473943607388, 1499562691000249223335548333901916719313641⟩
  | 0, 3 => ⟨10692680863108772862575179978463997744346986, 10692680863108772862575179978470091500769348⟩
  | 1, 2 => ⟨17873193960072372246912055325434286612691578, 17873193960072372246912055325441098008647015⟩
  | 2, 1 => ⟨18361305191207427520094445585223937436420440, 18361305191207427520094445585232817977017521⟩
  | 0, 4 => ⟨37779835265905887176625435616889835929479218, 37779835265905887176625435616907152623591626⟩
  | 1, 3 => ⟨102990294729843242299420228612615002923606018, 102990294729843242299420228612634484558126474⟩
  | 2, 2 => ⟨169673710745207330787836328176929312179304417, 169673710745207330787836328176955224780560273⟩
  | 3, 1 => ⟨172887611514877018580422155965227183353023695, 172887611514877018580422155965266477775745808⟩
  | 0, 5 => ⟨-385056993236618814979755884649520514397390370070, 387113056220210567325688552238670983684254213103⟩
  | 1, 4 => ⟨-619687406396472683502298247879554695970216318325, 617181034414292426147803837670763066140958344988⟩
  | 2, 3 => ⟨-1030755823627832082423954357321110466733139552093, 1022656688689635932511381550969138497134776985099⟩
  | 3, 2 => ⟨-1726124529638278539393749933998647408856919522142, 1712856960189770067564102861309005260831905254819⟩
  | 4, 1 => ⟨-2867514230489666819239667229917192282653691504560, 2856094432411089459490225716407201736504089107773⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0054Geometry.ds, E8TAxisProd0054Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 58583545430837078692034554223863420197076 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0054CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0055GraphCenterA.qJetBox,
   E8TAxisProd0055GraphCenterB.qJetBox,
   E8TAxisProd0055GraphCenterC.qJetBox,
   E8TAxisProd0055GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0055GraphWholeA.qJetBox,
   E8TAxisProd0055GraphWholeB.qJetBox,
   E8TAxisProd0055GraphWholeC.qJetBox,
   E8TAxisProd0055GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨60326778626201766484421253325377688115538, 60326778626201766484421253326609823770840⟩
  | 0, 2 => ⟨966185850974432406897733287330795623188888, 966185850974432406897733287334330975578471⟩
  | 1, 1 => ⟨1004472359345893462743067880688525924516354, 1004472359345893462743067880692813487625418⟩
  | 0, 3 => ⟨7806961847680241766754116586600384693337046, 7806961847680241766754116586606127837857356⟩
  | 1, 2 => ⟨13107265513662403099968043581740013274730112, 13107265513662403099968043581746396304966005⟩
  | 2, 1 => ⟨13501170009917655187472260256304457752078282, 13501170009917655187472260256312685446684567⟩
  | 0, 4 => ⟨29594535377680027261951942522561660683325823, 29594535377680027261951942522578161490330160⟩
  | 1, 3 => ⟨82208638723793322175713783873161697169016342, 82208638723793322175713783873180119121085816⟩
  | 2, 2 => ⟨136134386216698035782907982270237686795533541, 136134386216698035782907982270261941019626008⟩
  | 3, 1 => ⟨138954755243842967629453027023639138064738470, 138954755243842967629453027023675760080743852⟩
  | 0, 5 => ⟨-362921358526644195732616578473586099021177448027, 363994675885796552356250377505225488206006383934⟩
  | 1, 4 => ⟨-581162474249079840780420343826128044592250092254, 577751175906594041961795664558967720270523495174⟩
  | 2, 3 => ⟨-962245218671775472219803759607655953800056736132, 953300461232614568829041762082537069956311646562⟩
  | 3, 2 => ⟨-1603842430532944883635907949629564838404515264446, 1589752935859553742403804037572095591171810871719⟩
  | 4, 1 => ⟨-2649638153903571113093244309281496174587935506070, 2637225800869407346418756230852433857826408258985⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0055Geometry.ds, E8TAxisProd0055Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 30376967042217492655574377303061558003488 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0055CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0056GraphCenterA.qJetBox,
   E8TAxisProd0056GraphCenterB.qJetBox,
   E8TAxisProd0056GraphCenterC.qJetBox,
   E8TAxisProd0056GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0056GraphWholeA.qJetBox,
   E8TAxisProd0056GraphWholeB.qJetBox,
   E8TAxisProd0056GraphWholeC.qJetBox,
   E8TAxisProd0056GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34861656153946069640241255487885450180853, 34861656153946069640241255489031540476402⟩
  | 0, 2 => ⟨618156045975556753213573873814405881842083, 618156045975556753213573873817819405785603⟩
  | 1, 1 => ⟨645449648670899192838306856238169576851590, 645449648670899192838306856242312025661384⟩
  | 0, 3 => ⟨5524208685687739996226875547076317898275084, 5524208685687739996226875547081726304164145⟩
  | 1, 2 => ⟨9317768455169435683054989206917996309411261, 9317768455169435683054989206923975516424645⟩
  | 2, 1 => ⟨9629311777962760995324310530213977759186723, 9629311777962760995324310530221592246186090⟩
  | 0, 4 => ⟨22745597865179230294086184016770431141732663, 22745597865179230294086184016786162388781401⟩
  | 1, 3 => ⟨64349883146585394763338840700527560481629642, 64349883146585394763338840700544995326377747⟩
  | 2, 2 => ⟨107111528805263993867827558071159973571919930, 107111528805263993867827558071182688572127925⟩
  | 3, 1 => ⟨109566680508135272520390202053052855251059031, 109566680508135272520390202053087005793396131⟩
  | 0, 5 => ⟨-342168851790346438187828939897820533149026770507, 342328976187206994278002727940202838501969617451⟩
  | 1, 4 => ⟨-545167050985490657761481736195296905208317936656, 540929684650272635510134910976946768237747728107⟩
  | 2, 3 => ⟨-898399570679942652953056871468262004063056325913, 888700560246115256763493143007566495279830430855⟩
  | 3, 2 => ⟨-1490190474397305493900774545839170898388029679685, 1475385640379527317065665443897142683921354015542⟩
  | 4, 1 => ⟨-2447734197383970590332865620042103051246917359667, 2434448818962205293791678344116798218956578260548⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0056Geometry.ds, E8TAxisProd0056Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12755813988972322994603230710270428992079 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0056CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0057GraphCenterA.qJetBox,
   E8TAxisProd0057GraphCenterB.qJetBox,
   E8TAxisProd0057GraphCenterC.qJetBox,
   E8TAxisProd0057GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0057GraphWholeA.qJetBox,
   E8TAxisProd0057GraphWholeB.qJetBox,
   E8TAxisProd0057GraphWholeC.qJetBox,
   E8TAxisProd0057GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29046148294275033231751691798326730941639615, 29046148294275033231751691798330785820587890⟩
  | 0, 2 => ⟨161727211702807276902396418891120504880583856, 161727211702807276902396418891129414722679427⟩
  | 1, 1 => ⟨166480178569725819643043096321894046842426494, 166480178569725819643043096321905803062958332⟩
  | 0, 3 => ⟨522603682064685970316227576536352282423413196, 522603682064685970316227576536372573761869253⟩
  | 1, 2 => ⟨803769470099945517940738094341670735117893561, 803769470099945517940738094341697464643801429⟩
  | 2, 1 => ⟨822955672612861096060642400399388146626196142, 822955672612861096060642400399428861479277257⟩
  | 0, 4 => ⟨1206689584036163019423867797050642512016777763, 1206689584036163019423867797050696958959907589⟩
  | 1, 3 => ⟨2315349219158726429675713209827978380990033489, 2315349219158726429675713209828052543409423657⟩
  | 2, 2 => ⟨3445049259522892868998990893556722359661298115, 3445049259522892868998990893556837818179359851⟩
  | 3, 1 => ⟨3511779047604108079218412979968959935849041667, 3511779047604108079218412979969149612959139266⟩
  | 0, 5 => ⟨-11119949785020782478020610273456889044068962392455, 11188532051552718237141864991291564144019344891638⟩
  | 1, 4 => ⟨-20383728487631136771890270230542645640987238175325, 20435047365657003391280474693894804908655498153013⟩
  | 2, 3 => ⟨-37659274546971374148627596133801850216429593676979, 37689195737145610976755878579375905699979673160279⟩
  | 3, 2 => ⟨-69752205760221638047221670763325817075133138183925, 69766135912431983575749043748766193317035005693181⟩
  | 4, 1 => ⟨-129193634195886729188851986268569751862278504607150, 129228654976362537135083126786016473784573842201405⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0057Geometry.ds, E8TAxisProd0057Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16869368725002587100248889608856516907163932 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0057CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0058GraphCenterA.qJetBox,
   E8TAxisProd0058GraphCenterB.qJetBox,
   E8TAxisProd0058GraphCenterC.qJetBox,
   E8TAxisProd0058GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0058GraphWholeA.qJetBox,
   E8TAxisProd0058GraphWholeB.qJetBox,
   E8TAxisProd0058GraphWholeC.qJetBox,
   E8TAxisProd0058GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨20113612774697887294649706659101915783056274, 20113612774697887294649706659105594041162262⟩
  | 0, 2 => ⟨117719579659442460414808929561672861223461635, 117719579659442460414808929561680931419271102⟩
  | 1, 1 => ⟨121395540192703471264345536986038656143906714, 121395540192703471264345536986049163257712624⟩
  | 0, 3 => ⟨394333775356526521920140171365466505345912206, 394333775356526521920140171365484485820064986⟩
  | 1, 2 => ⟨612066059984514833808453716820959052042248576, 612066059984514833808453716820982323123902442⟩
  | 2, 1 => ⟨627469139973502305365150916068828270638145957, 627469139973502305365150916068863321432450980⟩
  | 0, 4 => ⟨918539766451197312696152405250929231836355400, 918539766451197312696152405250977324600716461⟩
  | 1, 3 => ⟨1808234000161617584341836644051200271728402867, 1808234000161617584341836644051264560159948075⟩
  | 2, 2 => ⟨2715746026968358208405390524701522262137541505, 2715746026968358208405390524701621201425710240⟩
  | 3, 1 => ⟨2770461044725320688231157823250738658071063112, 2770461044725320688231157823250900101171242177⟩
  | 0, 5 => ⟨-9236871646807917964816608527691357361353746555746, 9288058086781359214428971738171828499752532322952⟩
  | 1, 4 => ⟨-16840901487393545922070054195393005749810578075448, 16870052941652093721068433575195044037144543924321⟩
  | 2, 3 => ⟨-30962940218770807206455680775914184272935920715458, 30964150607470382188078479897671385878956992249139⟩
  | 3, 2 => ⟨-57071693340088683683997300435898004805884802123005, 57049195188202508521273407987789141521329926986979⟩
  | 4, 1 => ⟨-105167761646072080113013253987855191669813079390653, 105161546384294728903505636532782043398716628148562⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0058Geometry.ds, E8TAxisProd0058Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10699355392378789848658920909057092572233923 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0058CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0059GraphCenterA.qJetBox,
   E8TAxisProd0059GraphCenterB.qJetBox,
   E8TAxisProd0059GraphCenterC.qJetBox,
   E8TAxisProd0059GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0059GraphWholeA.qJetBox,
   E8TAxisProd0059GraphWholeB.qJetBox,
   E8TAxisProd0059GraphWholeC.qJetBox,
   E8TAxisProd0059GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨28244019708966363918951124285727468565461736, 28244019708966363918951124285731497146058545⟩
  | 0, 2 => ⟨159129223703471385107400123133391757297903238, 159129223703471385107400123133400608480627743⟩
  | 1, 1 => ⟨162490165185585036422146741412196452159381388, 162490165185585036422146741412208129250041415⟩
  | 0, 3 => ⟨516602131548631335784255101645550679063483584, 516602131548631335784255101645570817627929983⟩
  | 1, 2 => ⟨792257405900883205848725932331228693094642760, 792257405900883205848725932331255211891905022⟩
  | 2, 1 => ⟨805843205687833455155646523351971794648632221, 805843205687833455155646523352012175227026065⟩
  | 0, 4 => ⟨1193952908260652676162083028878222902502771628, 1193952908260652676162083028878276935889588515⟩
  | 1, 3 => ⟨2289522360099155944823597074231059521593157072, 2289522360099155944823597074231133098665983266⟩
  | 2, 2 => ⟨3400020531583089235017123370874701792681128902, 3400020531583089235017123370874816293902681590⟩
  | 3, 1 => ⟨3447308685367003375141038926650069578891165033, 3447308685367003375141038926650257616337520172⟩
  | 0, 5 => ⟨-11007459619041149284152329382735139209587358261246, 11075731643258746632132723449670671920043340177472⟩
  | 1, 4 => ⟨-20170919090698148745543468977011458791165494068520, 20222032890753451714134685802690183831546148117121⟩
  | 2, 3 => ⟨-37253714213192081576912650226505873527174111639471, 37283521227768959054759660326741894755759813727881⟩
  | 3, 2 => ⟨-68976296820240279468904147289936207386960791158861, 68990304944495172144370671444779216460998157692334⟩
  | 4, 1 => ⟨-127705875959265875653184328107033903280767702292063, 127741911938299219765584291449271650095218581802459⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0059Geometry.ds, E8TAxisProd0059Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16277661885076609563190781480024055422334007 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0059CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0060GraphCenterA.qJetBox,
   E8TAxisProd0060GraphCenterB.qJetBox,
   E8TAxisProd0060GraphCenterC.qJetBox,
   E8TAxisProd0060GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0060GraphWholeA.qJetBox,
   E8TAxisProd0060GraphWholeB.qJetBox,
   E8TAxisProd0060GraphWholeC.qJetBox,
   E8TAxisProd0060GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19529924962876359686847095727788275340065517, 19529924962876359686847095727791929496023753⟩
  | 0, 2 => ⟨115759352128156210260203361441879964761338185, 115759352128156210260203361441887982720128462⟩
  | 1, 1 => ⟨118357728272278206425082820238486534503265851, 118357728272278206425082820238496972420309486⟩
  | 0, 3 => ⟨389765295982591175946582594923339013133076002, 389765295982591175946582594923356858514527580⟩
  | 1, 2 => ⟨603075571992816644220496939005231831095654196, 603075571992816644220496939005254919368262036⟩
  | 2, 1 => ⟨613980520697620017548329283179848092922168899, 613980520697620017548329283179882856692393124⟩
  | 0, 4 => ⟨908869160698800665941274439542991343376499029, 908869160698800665941274439543039074817143882⟩
  | 1, 3 => ⟨1787997395102367505935972820072722869863212198, 1787997395102367505935972820072786656435003118⟩
  | 2, 2 => ⟨2679768279978837530932475755710450876595804045, 2679768279978837530932475755710549001762116918⟩
  | 3, 1 => ⟨2718540253368775333972547234488563380421059003, 2718540253368775333972547234488723435243076325⟩
  | 0, 5 => ⟨-9144215165574264889855018895768285874003781136232, 9195420456518289004030494394752110244860284900613⟩
  | 1, 4 => ⟨-16666195584645207751972333788228736825956910850285, 16695648506304698165115110596524905763245727337079⟩
  | 2, 3 => ⟨-30630893183716007267814468949687832251145146219177, 30632761875270492715039977790063084764929563105226⟩
  | 3, 2 => ⟨-56437952182619792830321583251195832527906040368636, 56416664348256115374840942963429471683469455126873⟩
  | 4, 1 => ⟨-103955340562423655540936954825552290901186275255344, 103951643276731548385076579726892096517518594376788⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0060Geometry.ds, E8TAxisProd0060Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10279868396313382241821296447647809248184485 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0060CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0061GraphCenterA.qJetBox,
   E8TAxisProd0061GraphCenterB.qJetBox,
   E8TAxisProd0061GraphCenterC.qJetBox,
   E8TAxisProd0061GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0061GraphWholeA.qJetBox,
   E8TAxisProd0061GraphWholeB.qJetBox,
   E8TAxisProd0061GraphWholeC.qJetBox,
   E8TAxisProd0061GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13645657417327311257336534725364212406973240, 13645657417327311257336534725367547692294681⟩
  | 0, 2 => ⟨84366675532948124950552713923297889821621059, 84366675532948124950552713923305222629225500⟩
  | 1, 1 => ⟨87180045530779355578612019849952499052029936, 87180045530779355578612019849961926125215379⟩
  | 0, 3 => ⟨294440439257063238427913752009142960711388824, 294440439257063238427913752009158927064358682⟩
  | 1, 2 => ⟨461333166574405244425343128525948470341048318, 461333166574405244425343128525968773594924937⟩
  | 2, 1 => ⟨473636112563455633133932673444172245030908658, 473636112563455633133932673444202467296743189⟩
  | 0, 4 => ⟨693386732065785092614423931762973830246760309, 693386732065785092614423931763016449395014445⟩
  | 1, 3 => ⟨1403691754153574745942863727158417227947323218, 1403691754153574745942863727158473120612803497⟩
  | 2, 2 => ⟨2129098394637638287261891898674606163645023433, 2129098394637638287261891898674691139410747088⟩
  | 3, 1 => ⟨2173907023807777617712475269047862534272204800, 2173907023807777617712475269048000227648732663⟩
  | 0, 5 => ⟨-7698006031752633618631305063761335491185130446650, 7737583798955011467657853429092576978678347950172⟩
  | 1, 4 => ⟨-13956521240456496558661517645422490756414245407671, 13972110339355854475055633707011833429527239272146⟩
  | 2, 3 => ⟨-25529599352548303110554203956979451282134523197819, 25514446918612006560058556361163130569043387217226⟩
  | 3, 2 => ⟨-46816972062782190198018912912389226486375000458898, 46774308531074076087166900083384095250553416368972⟩
  | 4, 1 => ⟨-85803886870059180009533893730276950191254724226920, 85773418427274007206114286733809688657602889994786⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0061Geometry.ds, E8TAxisProd0061Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6383386507643436670893860383519550404478725 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0061CertifiedArithmetic

end


