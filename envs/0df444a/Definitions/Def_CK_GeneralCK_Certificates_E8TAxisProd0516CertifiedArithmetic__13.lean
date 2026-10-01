-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0516CertifiedArithmetic__13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0516CertifiedArithmetic__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T12:57:22.846283+00:00
-- url     : https://prove2.me/theorems/b419ba2f-6d9d-43d1-8a0b-154ff723a5d6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0516CertifiedArithmetic (+12 modules: GeneralCK/Certificates/E8TAxisProd0517CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0518CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0519CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0520CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0521CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0522CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0523CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0524CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0525CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0526CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0527CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0528CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0514GraphCenterA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0516GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0502GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0511GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0508GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0509GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0504GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0505GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0494Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0517Geometry__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0518GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0520GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0520GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0523GraphWholeA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0525GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0527GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0527GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0528GraphCenterA__8

-- ===== source module GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0516GraphCenterA.qJetBox,
   E8TAxisProd0516GraphCenterB.qJetBox,
   E8TAxisProd0516GraphCenterC.qJetBox,
   E8TAxisProd0516GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0516GraphWholeA.qJetBox,
   E8TAxisProd0516GraphWholeB.qJetBox,
   E8TAxisProd0516GraphWholeC.qJetBox,
   E8TAxisProd0516GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5546327510458461173225523084617621910958871274, 5546327510458461173225523084617663073359491878⟩
  | 0, 2 => ⟨18772543148858359617986062727503399122166900453, 18772543148858359617986062727503534236911364574⟩
  | 1, 1 => ⟨19080399858198914767794276117253634785409829605, 19080399858198914767794276117253865962052172746⟩
  | 0, 3 => ⟨43471310907084829802437067100683599855695164770, 43471310907084829802437067100684016908092653277⟩
  | 1, 2 => ⟨59791249833036198109298740116873447127248607051, 59791249833036198109298740116874161396011228969⟩
  | 2, 1 => ⟨60651973270521720546750428221178867054320414025, 60651973270521720546750428221180127650694503393⟩
  | 0, 4 => ⟨83650123459999434014327018914347345561903957621, 83650123459999434014327018914348699864875068982⟩
  | 1, 3 => ⟨128646790474306019692426837163879101821787778505, 128646790474306019692426837163881475345289694001⟩
  | 2, 2 => ⟨174153368827657284248512462863132081356589033073, 174153368827657284248512462863136348440833920821⟩
  | 3, 1 => ⟨176316052163790242451247201940489241196885677015, 176316052163790242451247201940497000932593478030⟩
  | 0, 5 => ⟨-181015592071438988440740841223264207922424854996215, 182381257538868334261512398093568509873704808092067⟩
  | 1, 4 => ⟨-349829952662819223738784591963393531864205512762398, 351838079142320638610861970698303967905213665452640⟩
  | 2, 3 => ⟨-677357431798608396762819297092912060918402805222537, 680206973044177436147042305339029253029209238572589⟩
  | 3, 2 => ⟨-1312896213221309015928635027311283727200844016582453, 1316609237816111873733704166596896344316964505171175⟩
  | 4, 1 => ⟨-2546365343010952062706191893328346836541705248883160, 2550173957583281877650704891204027162398837471000354⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0516Geometry.ds, E8TAxisProd0516Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5169189126068321488359988495828121627060709632 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0516CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0517GraphCenterA.qJetBox,
   E8TAxisProd0517GraphCenterB.qJetBox,
   E8TAxisProd0517GraphCenterC.qJetBox,
   E8TAxisProd0517GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0517GraphWholeA.qJetBox,
   E8TAxisProd0517GraphWholeB.qJetBox,
   E8TAxisProd0517GraphWholeC.qJetBox,
   E8TAxisProd0517GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4898459230188654180708503522419524682611002402, 4898459230188654180708503522419562456031010636⟩
  | 0, 2 => ⟨16732813781796409542885115608294590527050206781, 16732813781796409542885115608294712703456546711⟩
  | 1, 1 => ⟨17011099009019638925699605351329541176172177261, 17011099009019638925699605351329749102657207292⟩
  | 0, 3 => ⟨39061685982734709086067430954548793018560017548, 39061685982734709086067430954549168028482478929⟩
  | 1, 2 => ⟨53817952483769005088975965042163737091424486728, 53817952483769005088975965042164376490920171633⟩
  | 2, 1 => ⟨54603925990197782056530412725167269416510316307, 54603925990197782056530412725168394830580299138⟩
  | 0, 4 => ⟨75826519729775620338926051706156891819760754582, 75826519729775620338926051706158104109581708293⟩
  | 1, 3 => ⟨116919911424985350588935209795732778869663827112, 116919911424985350588935209795734895658567632496⟩
  | 2, 2 => ⟨158486565531360177262863014517915781308338028201, 158486565531360177262863014517919578084656826294⟩
  | 3, 1 => ⟨160485673797716597222861802435852109665081713031, 160485673797716597222861802435859001255471285628⟩
  | 0, 5 => ⟨-153659874158863321679952795097105288756306468069652, 154868905744575062869926438857558752698478712485306⟩
  | 1, 4 => ⟨-296550884422472093853334913065947567712260459039383, 298323496091816819699273691273005806721895609697825⟩
  | 2, 3 => ⟨-573484236394240985184289810760837662305219586648321, 575995185248627291795935045355740392014201003355749⟩
  | 3, 2 => ⟨-1110259047261838603357605272644323182008843326326258, 1113528773519679356877869153667954742985323639444601⟩
  | 4, 1 => ⟨-2150885315434518052285473031539900232447919958570660, 2154243106146117565745464490991642230371136788786242⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0517Geometry.ds, E8TAxisProd0517Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4562685545970921348764305744219076273476027838 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0517CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0518GraphCenterA.qJetBox,
   E8TAxisProd0518GraphCenterB.qJetBox,
   E8TAxisProd0518GraphCenterC.qJetBox,
   E8TAxisProd0518GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0518GraphWholeA.qJetBox,
   E8TAxisProd0518GraphWholeB.qJetBox,
   E8TAxisProd0518GraphWholeC.qJetBox,
   E8TAxisProd0518GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5522895766268509176255157456599021640603306899, 5522895766268509176255157456599062722656052575⟩
  | 0, 2 => ⟨18718269316023044425678718904519655309794553204, 18718269316023044425678718904519790128884212622⟩
  | 1, 1 => ⟨19005761227345257963925218548917421367550581824, 19005761227345257963925218548917652024932126031⟩
  | 0, 3 => ⟨43366858300972493519023669308336202984490433605, 43366858300972493519023669308336619104004869538⟩
  | 1, 2 => ⟨59630618598979035764548934754291079830555267862, 59630618598979035764548934754291792466625020473⟩
  | 2, 1 => ⟨60434546973869011131765565205858496783543660715, 60434546973869011131765565205859754450802214272⟩
  | 0, 4 => ⟨83474099997012287280790659464747355026926539314, 83474099997012287280790659464748706194829095845⟩
  | 1, 3 => ⟨128363272870997857550692060857946977333959830545, 128363272870997857550692060857949345287750988601⟩
  | 2, 2 => ⟨173728844120050540777592315500046443418993630140, 173728844120050540777592315500050700368067800270⟩
  | 3, 1 => ⟨175749248780181394920740322770730202740953085208, 175749248780181394920740322770737943824601291356⟩
  | 0, 5 => ⟨-180430552318278808637208666950913163462188763308697, 181793012905948332195803286719346537993788245877150⟩
  | 1, 4 => ⟨-348690448612604548926264149722292283855943691541703, 350693767491810815405006334627348215688084693484422⟩
  | 2, 3 => ⟨-675134575715500215371733169756119714803561808932756, 677977218621062260988467182536126802636643508907961⟩
  | 3, 2 => ⟨-1308555880962105850397314783096971523246458885222188, 1312259802360413265723509380290344743118529127306467⟩
  | 4, 1 => ⟨-2537884818901820827899843667009544657206351392333270, 2541683656804454767916261007180252846171553485149599⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0518Geometry.ds, E8TAxisProd0518Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5147209562099579937553676502218873522386769553 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0518CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0519GraphCenterA.qJetBox,
   E8TAxisProd0519GraphCenterB.qJetBox,
   E8TAxisProd0519GraphCenterC.qJetBox,
   E8TAxisProd0519GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0519GraphWholeA.qJetBox,
   E8TAxisProd0519GraphWholeB.qJetBox,
   E8TAxisProd0519GraphWholeC.qJetBox,
   E8TAxisProd0519GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4877573705233600660161940330593601494369610419, 4877573705233600660161940330593639194501101463⟩
  | 0, 2 => ⟨16684045871774824082048765498792145134226073281, 16684045871774824082048765498792267043678035219⟩
  | 1, 1 => ⟨16943917844226558703732340523244246441812464448, 16943917844226558703732340523244453901355503723⟩
  | 0, 3 => ⟨38967003645642293932906659456187043050166702147, 38967003645642293932906659456187417219858486466⟩
  | 1, 2 => ⟨53671965454709500284414171238273176752285324853, 53671965454709500284414171238273814685857666880⟩
  | 2, 1 => ⟨54406062144246254168163769318290248791992874568, 54406062144246254168163769318291371581130731595⟩
  | 0, 4 => ⟨75665269288594025079687983037558220277837651158, 75665269288594025079687983037559429746954108759⟩
  | 1, 3 => ⟨116659417570816205566052764299225129181787640674, 116659417570816205566052764299227240971761671595⟩
  | 2, 2 => ⟨158095716737067842772288697461676067124992327864, 158095716737067842772288697461679854817384424296⟩
  | 3, 1 => ⟨159963274925169293620422938895544589501707572582, 159963274925169293620422938895551464393250404483⟩
  | 0, 5 => ⟨-153156259103793720817878494519730777706257809089972, 154362471265100137820120431938642306776246415721555⟩
  | 1, 4 => ⟨-295570905937298652368117029052854194582620564455087, 297339257422728741920597659446620301269682183067557⟩
  | 2, 3 => ⟨-571574229977021397195475727999389330071643670745938, 574079016122825818904686465938596930080208658085712⟩
  | 3, 2 => ⟨-1106532667390708685233094200121404327206242847663238, 1109794173820712571317545402771103227556224354365878⟩
  | 4, 1 => ⟨-2143610263329189051276538790299736786536114193625240, 2146959029211913357965066753953794999702507226121481⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0519Geometry.ds, E8TAxisProd0519Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4543105766728536125765148342176132854227454326 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0519CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0520GraphCenterA.qJetBox,
   E8TAxisProd0520GraphCenterB.qJetBox,
   E8TAxisProd0520GraphCenterC.qJetBox,
   E8TAxisProd0520GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0520GraphWholeA.qJetBox,
   E8TAxisProd0520GraphWholeB.qJetBox,
   E8TAxisProd0520GraphWholeC.qJetBox,
   E8TAxisProd0520GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7027128421670585675928958914483394727535161781, 7027128421670585675928958914483443556526641360⟩
  | 0, 2 => ⟨23415342608433540916329652591585193662406835460, 23415342608433540916329652591585358439827522847⟩
  | 1, 1 => ⟨23741366385234143919916435210412993753283629812, 23741366385234143919916435210413278480774550256⟩
  | 0, 3 => ⟨53392689492194944945195871096999787755219492130, 53392689492194944945195871097000301393650268549⟩
  | 1, 2 => ⟨73159496165875325945774134390399744297440619007, 73159496165875325945774134390400631208744163073⟩
  | 2, 1 => ⟨74052858525296280052233070788139054562429862900, 74052858525296280052233070788140627732747047220⟩
  | 0, 4 => ⟨100990638160514668794005528583951386230619620808, 100990638160514668794005528583953066691297591938⟩
  | 1, 3 => ⟨154514674671258139270544028232412941918793624452, 154514674671258139270544028232415906739175904747⟩
  | 2, 2 => ⟨208551630206407773411003391985867552056536543832, 208551630206407773411003391985872904537997930132⟩
  | 3, 1 => ⟨210744089705377121747325092525841142742417905872, 210744089705377121747325092525850909727371789306⟩
  | 0, 5 => ⟨-247754804604998672992420861449194627862597595206917, 249493041035035637012005925270416132524952251616406⟩
  | 1, 4 => ⟨-479996437324068230120978897224630222559320430104924, 482564090980382059616108396921917219300920436619699⟩
  | 2, 3 => ⟨-931470401890551670279189583000179622818060208560663, 935123574061658654472004829719536086474430256245738⟩
  | 3, 2 => ⟨-1809273567202071153023709445269739929867606718920003, 1814038196189000349723348452835654103980526370756344⟩
  | 4, 1 => ⟨-3516394330701338578397830282676209116995152205698339, 3521271804389851672250535365664724029378892072840038⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0520Geometry.ds, E8TAxisProd0520Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6556457299359054483367902295080596151681106185 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0520CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0521GraphCenterA.qJetBox,
   E8TAxisProd0521GraphCenterB.qJetBox,
   E8TAxisProd0521GraphCenterC.qJetBox,
   E8TAxisProd0521GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0521GraphWholeA.qJetBox,
   E8TAxisProd0521GraphWholeB.qJetBox,
   E8TAxisProd0521GraphWholeC.qJetBox,
   E8TAxisProd0521GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6220149236330279936864859777649263762439165351, 6220149236330279936864859777649308485749834715⟩
  | 0, 2 => ⟨20916821718653085375268937114864815675660660845, 20916821718653085375268937114864964523781470783⟩
  | 1, 1 => ⟨21212120594346680075545376617610170757593459783, 21212120594346680075545376617610426706714699501⟩
  | 0, 3 => ⟨48090272779465145015381788344417706960539775117, 48090272779465145015381788344418168743622338014⟩
  | 1, 2 => ⟨65998396347941095159562482214121936202805600917, 65998396347941095159562482214122730367709295929⟩
  | 2, 1 => ⟨66815912600245293581992874898485456589573011698, 66815912600245293581992874898486861735498275752⟩
  | 0, 4 => ⟨91776956638151904439762346091832013441645026817, 91776956638151904439762346091833518851482083097⟩
  | 1, 3 => ⟨140761332839226252798787956248197248992578521655, 140761332839226252798787956248199896348288039427⟩
  | 2, 2 => ⟨190222568233147580442001022669887883777776910436, 190222568233147580442001022669892653276394111309⟩
  | 3, 1 => ⟨192252888869476457422231720458532854636917629658, 192252888869476457422231720458541543016376937150⟩
  | 0, 5 => ⟨-211363491155696387240464841074842045660176956111753, 212900642393937195785448150183330385256717347317866⟩
  | 1, 4 => ⟨-408991996341449672791318803172209044748885505895089, 411257247912060962799291294669959565580429840307809⟩
  | 2, 3 => ⟨-792800839923197017780032133860776247496061922200418, 796019265055520139030897833197248151361393291192360⟩
  | 3, 2 => ⟨-1538294934245554014485982445748136314908123448813949, 1542490237634018958244747740152844353815669593251652⟩
  | 4, 1 => ⟨-2986635186140754508392047064080683496770884565268764, 2990933263934335716725623348495167386051999767368717⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0521Geometry.ds, E8TAxisProd0521Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5800228808799612705769626087322823923985934128 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0521CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0522GraphCenterA.qJetBox,
   E8TAxisProd0522GraphCenterB.qJetBox,
   E8TAxisProd0522GraphCenterC.qJetBox,
   E8TAxisProd0522GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0522GraphWholeA.qJetBox,
   E8TAxisProd0522GraphWholeB.qJetBox,
   E8TAxisProd0522GraphWholeC.qJetBox,
   E8TAxisProd0522GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6997900923591114013821578840587833705526562362, 6997900923591114013821578840587882438140074694⟩
  | 0, 2 => ⟨23348680591233462646901644530913523223904046873, 23348680591233462646901644530913687640031461723⟩
  | 1, 1 => ⟨23650037642708835433644068802846909021180605342, 23650037642708835433644068802847193109357559525⟩
  | 0, 3 => ⟨53266581425141245554560763549064243614590602850, 53266581425141245554560763549064756108425921712⟩
  | 1, 2 => ⟨72966561368577867689092330670226476174821114379, 72966561368577867689092330670227361071353118150⟩
  | 2, 1 => ⟨73792479979878934438181535978455720354887164010, 73792479979878934438181535978457289897865503683⟩
  | 0, 4 => ⟨100782331538049850966599363838704271930032822983, 100782331538049850966599363838705948541053443816⟩
  | 1, 3 => ⟨154181103648459458391192243469270674200000941996, 154181103648459458391192243469273632151027127341⟩
  | 2, 2 => ⟨208054201441124433239862578428399046434019662441, 208054201441124433239862578428404386384090518299⟩
  | 3, 1 => ⟨210081558064888017461392002628780197009831372223, 210081558064888017461392002628789940886366566575⟩
  | 0, 5 => ⟨-246976314989909966254624015277525394655923981428225, 248710511515642298367849067222576298553309980985836⟩
  | 1, 4 => ⟨-478477522346785643787957204748295875555602455304786, 481039089814768833335771513614228281358711613602288⟩
  | 2, 3 => ⟨-928502664609928728662947986625451954327173162895289, 932147116059578805591440451444885343467995303101049⟩
  | 3, 2 => ⟨-1803469841796745299249936463546842755159819193550478, 1808223080417833343841985456641426902633089492284038⟩
  | 4, 1 => ⟨-3505037330311950002464427597246626511299690399205664, 3509902994754936736895837516849338430285466980484535⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0522Geometry.ds, E8TAxisProd0522Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6529010438781056386258447891886952276339244676 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0522CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0523GraphCenterA.qJetBox,
   E8TAxisProd0523GraphCenterB.qJetBox,
   E8TAxisProd0523GraphCenterC.qJetBox,
   E8TAxisProd0523GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0523GraphWholeA.qJetBox,
   E8TAxisProd0523GraphWholeB.qJetBox,
   E8TAxisProd0523GraphWholeC.qJetBox,
   E8TAxisProd0523GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6194040749847832479678418985774219654292957335, 6194040749847832479678418985774264289808535072⟩
  | 0, 2 => ⟨20856780528602330477569357531756084913869344896, 20856780528602330477569357531756233435893082173⟩
  | 1, 1 => ⟨21129732488691521093512908582461125396256908372, 21129732488691521093512908582461380770467018840⟩
  | 0, 3 => ⟨47975671142715437907518154105926486618937449534, 47975671142715437907518154105926947370881389137⟩
  | 1, 2 => ⟨65822636679720491220853866182528744705575999442, 65822636679720491220853866182529537060523662324⟩
  | 2, 1 => ⟨66578421264827852408750723937683779886005266694, 66578421264827852408750723937685181778993571167⟩
  | 0, 4 => ⟨91585719959823200505758745606403233164174435841, 91585719959823200505758745606404735106690071429⟩
  | 1, 3 => ⟨140454231669122034515584337298000408721264548942, 140454231669122034515584337298003049903004208062⟩
  | 2, 2 => ⟨189763716480074345156637098677825363473835096068, 189763716480074345156637098677830121723255260111⟩
  | 3, 1 => ⟨191641116518394056547373318306644877079965885172, 191641116518394056547373318306653544735795681163⟩
  | 0, 5 => ⟨-210690599966159463625890114093956174191513798344744, 212224163020030314621063279498704343689501293200119⟩
  | 1, 4 => ⟨-407680223790966299568281656978034178010388787105071, 409940102137889780653853324691572831706658784402857⟩
  | 2, 3 => ⟨-790239865356668432927247512535320996173845497391113, 793450608662051928141125635152767737864285683301194⟩
  | 3, 2 => ⟨-1533290533955646056211939454128455339412440667747932, 1537475776244525770090218867102954810305555989757218⟩
  | 4, 1 => ⟨-2976849773360706447620251748528853727324015753914465, 2981137259369066213426453556023896218403511693555112⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0523Geometry.ds, E8TAxisProd0523Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5775724897988918786023269702336883302711568126 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0523CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0524GraphCenterA.qJetBox,
   E8TAxisProd0524GraphCenterB.qJetBox,
   E8TAxisProd0524GraphCenterC.qJetBox,
   E8TAxisProd0524GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0524GraphWholeA.qJetBox,
   E8TAxisProd0524GraphWholeB.qJetBox,
   E8TAxisProd0524GraphWholeC.qJetBox,
   E8TAxisProd0524GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5499531782823275901073635647061512968909234598, 5499531782823275901073635647061553970774068815⟩
  | 0, 2 => ⟨18664125911510876697234017892586335288017317923, 18664125911510876697234017892586469812089386215⟩
  | 1, 1 => ⟨18931323164174822779367815292757553924331064607, 18931323164174822779367815292757784063590749338⟩
  | 0, 3 => ⟨43262625523005471123920243104352955895832301827, 43262625523005471123920243104353371084497128257⟩
  | 1, 2 => ⟨59470341428904501807523745398212592317979561191, 59470341428904501807523745398213303324949840308⟩
  | 2, 1 => ⟨60217650814748923177149871827161774196852111731, 60217650814748923177149871827163028941488170615⟩
  | 0, 4 => ⟨83298398342436419359948998363658755043147471370, 83298398342436419359948998363660103082876861158⟩
  | 1, 3 => ⟨128080287957817586483999836923690014016458309882, 128080287957817586483999836923692376412841163282⟩
  | 2, 2 => ⟨173305148546926131760257960055779130428468247731, 173305148546926131760257960055783377264813499979⟩
  | 3, 1 => ⟨175183657026437293057031119309297095863995789397, 175183657026437293057031119309304818337010221801⟩
  | 0, 5 => ⟨-179847216270579345742684173668906787184161712620405, 181206478385057619246135488884298034752471120464653⟩
  | 1, 4 => ⟨-347554279637825225163907238567096865232599899965251, 349552800109010442603148552598203195833248386847780⟩
  | 2, 3 => ⟨-672918257020901598033776160965780126096416099980085, 675754013710509509551064000918331619091784200256006⟩
  | 3, 2 => ⟨-1304228374721768139410182155652965487609742387178009, 1307923206387506357469317690839027420953097822582430⟩
  | 4, 1 => ⟨-2529429475163613052330870068086148352987576825198746, 2533218544547951492201541833750005521732284369766447⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0524Geometry.ds, E8TAxisProd0524Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5125293865166714029826225540012490751617219618 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0524CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0525GraphCenterA.qJetBox,
   E8TAxisProd0525GraphCenterB.qJetBox,
   E8TAxisProd0525GraphCenterC.qJetBox,
   E8TAxisProd0525GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0525GraphWholeA.qJetBox,
   E8TAxisProd0525GraphWholeB.qJetBox,
   E8TAxisProd0525GraphWholeC.qJetBox,
   E8TAxisProd0525GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4856749066247964400522730692169304719904416957, 4856749066247964400522730692169342346892752067⟩
  | 0, 2 => ⟨16635396188775276259199392070846210080549812702, 16635396188775276259199392070846331723623050118⟩
  | 1, 1 => ⟨16876918959837833960585053312453516705480478976, 16876918959837833960585053312453723699107578611⟩
  | 0, 3 => ⟨38872522685435747964269955379807725042054635534, 38872522685435747964269955379808098373352321041⟩
  | 1, 2 => ⟨53526303733758504971518871808987347933798058173, 53526303733758504971518871808987984404685639691⟩
  | 2, 1 => ⟨54208686376756871275921602123007261086491433576, 54208686376756871275921602123008381256542096833⟩
  | 0, 4 => ⟨75504316633377177278984837355655930650346859890, 75504316633377177278984837355657137305001956987⟩
  | 1, 3 => ⟨116399418316990464775534656372254359228842805578, 116399418316990464775534656372256466031010352088⟩
  | 2, 2 => ⟨157705639778620306871292212387831852162501691030, 157705639778620306871292212387835630791244977251⟩
  | 3, 1 => ⟨159442006003746700612305896929630481204968372561, 159442006003746700612305896929637339435079619950⟩
  | 0, 5 => ⟨-152654146407680440788745434372969434551768508770400, 153857544796423725692673457641818734667912172349904⟩
  | 1, 4 => ⟨-294593866413975061854139540517292249319655058625278, 296357965916108440547871442046387320708398685627158⟩
  | 2, 3 => ⟨-569669980845625806974969595104078279383864090482835, 572168615247495678825763074624709394167081279604613⟩
  | 3, 2 => ⟨-1102817576090266390298115516848848747345171298525705, 1106070875149578101105333860436175820316252509035917⟩
  | 4, 1 => ⟨-2136357359862166450021546302198322333362947359369123, 2139697109209309185906144748360050530971493639606921⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0525Geometry.ds, E8TAxisProd0525Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4523583337296463149535539366433926410717150090 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0525CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0526GraphCenterA.qJetBox,
   E8TAxisProd0526GraphCenterB.qJetBox,
   E8TAxisProd0526GraphCenterC.qJetBox,
   E8TAxisProd0526GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0526GraphWholeA.qJetBox,
   E8TAxisProd0526GraphWholeB.qJetBox,
   E8TAxisProd0526GraphWholeC.qJetBox,
   E8TAxisProd0526GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5476235397258993438057182283826612419526706963, 5476235397258993438057182283826653341363268100⟩
  | 0, 2 => ⟨18610112660787954751311086303512319220300179477, 18610112660787954751311086303512453449990513339⟩
  | 1, 1 => ⟨18857085226523569734573419515378687276405383858, 18857085226523569734573419515378916898679711403⟩
  | 0, 3 => ⟨43158612171242075468454313560255388202336164836, 43158612171242075468454313560255802462180491073⟩
  | 1, 2 => ⟨59310417657490723355642023838270260736466145462, 59310417657490723355642023838270970117922692170⟩
  | 2, 1 => ⟨60001283757599917740865102677131601265231849485, 60001283757599917740865102677132853093724641261⟩
  | 0, 4 => ⟨83123017986269497320223989254415003495369850114, 83123017986269497320223989254416348413807039893⟩
  | 1, 3 => ⟨127797834869725418657355084189349603965675382477, 127797834869725418657355084189351960816926822249⟩
  | 2, 2 => ⟨172882280738140833451001454086803930523038854357, 172882280738140833451001454086808167269050639534⟩
  | 3, 1 => ⟨174619274843050986103294734921932404636167151766, 174619274843050986103294734921940108539888518204⟩
  | 0, 5 => ⟨-179265579782658874776585119923744369231787086386316, 180621649820341452774323109421921186139769737403969⟩
  | 1, 4 => ⟨-346421437603801220725718019815843957485102993355805, 348415168848692952754695767871470704380329189263168⟩
  | 2, 3 => ⟨-670708459719671486043730424480369169487578011294230, 673537342308374491431601238674389449282697757741082⟩
  | 3, 2 => ⟨-1299913663016424505169315678377489749023830276086747, 1303599418419355260799782535959810658645556250818936⟩
  | 4, 1 => ⟨-2520999249783979916996281932660532136457065547699453, 2524778558853673603151390312621023441168178481862349⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0526Geometry.ds, E8TAxisProd0526Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5103441880988207131216214970641927990855288785 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0526CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0527GraphCenterA.qJetBox,
   E8TAxisProd0527GraphCenterB.qJetBox,
   E8TAxisProd0527GraphCenterC.qJetBox,
   E8TAxisProd0527GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0527GraphWholeA.qJetBox,
   E8TAxisProd0527GraphWholeB.qJetBox,
   E8TAxisProd0527GraphWholeC.qJetBox,
   E8TAxisProd0527GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4835985165605196649860454739626649713680358998, 4835985165605196649860454739626687267670604468⟩
  | 0, 2 => ⟨16586864481309180616563761621590714291338982197, 16586864481309180616563761621590835668607921050⟩
  | 1, 1 => ⟨16810101949604525688183473962867549459719632340, 16810101949604525688183473962867755988454643159⟩
  | 0, 3 => ⟨38778242730178755572320132608945976001826510454, 38778242730178755572320132608946348496562752216⟩
  | 1, 2 => ⟨53380966703169261666284776588196128854958060243, 53380966703169261666284776588196763866392544827⟩
  | 2, 1 => ⟨54011797723734319754498968974941836860867968985, 54011797723734319754498968974942954417663894339⟩
  | 0, 4 => ⟨75343661290411506283443486697686622232059198207, 75343661290411506283443486697687826078482953170⟩
  | 1, 3 => ⟨116139912857834909098296374972539481427303979057, 116139912857834909098296374972541583252765097900⟩
  | 2, 2 => ⟨157316333377159386091349793643866081917276549838, 157316333377159386091349793643869851502606792623⟩
  | 3, 1 => ⟨158921865108100396541406260993083104117921589235, 158921865108100396541406260993089945723939042062⟩
  | 0, 5 => ⟨-152153532257186325820498438627497916491008825359330, 153354122516593813190436692158044673169155235041665⟩
  | 1, 4 => ⟨-293619758373286906102810151060245335282639838977915, 295379614084198562270337306008754739946139726031338⟩
  | 2, 3 => ⟨-567771474299923680016959571876525511256646802712310, 570263967915897197872776025370545329444726410264403⟩
  | 3, 2 => ⟨-1099113744437882502084843096433368713975357323132793, 1102358848591546573795406810577130971439386068606092⟩
  | 4, 1 => ⟨-2129126548090251058660516720362474059085737259947535, 2132457289247062544134369451543520182296031867266077⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0527Geometry.ds, E8TAxisProd0527Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4504118117934811243070203660068669432232143752 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0527CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0528GraphCenterA.qJetBox,
   E8TAxisProd0528GraphCenterB.qJetBox,
   E8TAxisProd0528GraphCenterC.qJetBox,
   E8TAxisProd0528GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0528GraphWholeA.qJetBox,
   E8TAxisProd0528GraphWholeB.qJetBox,
   E8TAxisProd0528GraphWholeC.qJetBox,
   E8TAxisProd0528GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4321170909782565835447956304779250511814191468, 4321170909782565835447956304779285210239956525⟩
  | 0, 2 => ⟨14897903296300064066219719863253075657467283474, 14897903296300064066219719863253186198312178394⟩
  | 1, 1 => ⟨15149200021116229830954697811698430459237307277, 15149200021116229830954697811698617536850266497⟩
  | 0, 3 => ⟨35056482373682916685598299848166393618328905918, 35056482373682916685598299848166730876079949925⟩
  | 1, 2 => ⟨48385238593543239760136399145996154151976731504, 48385238593543239760136399145996726481484325758⟩
  | 2, 1 => ⟨49102151052615849940942477781411376588019729351, 49102151052615849940942477781412381121077054954⟩
  | 0, 4 => ⟨68642199750139087120201772279435521882242289390, 68642199750139087120201772279436606787167381369⟩
  | 1, 3 => ⟨106128957999013056055112912311495311512037418237, 106128957999013056055112912311497198430487172875⟩
  | 2, 2 => ⟨144054534775276464925917423584829920958861376558, 144054534775276464925917423584833297229323435359⟩
  | 3, 1 => ⟨145900510909042169453512810336016052529839436737, 145900510909042169453512810336022168917294893514⟩
  | 0, 5 => ⟨-130125611709604823654920744894247800061570391035719, 131196255154485672484734722125745958463274735339104⟩
  | 1, 4 => ⟨-250759548482935743251865828684837970196161265357016, 252324034537497886772091709867769853423133703114363⟩
  | 2, 3 => ⟨-484292764701836552049586400087031826486320015213817, 486504394793653265570538312438858744866329192885098⟩
  | 3, 2 => ⟨-936423397511156093469230783933458359661200787039018, 939301067382923922235960476656578691082653494898709⟩
  | 4, 1 => ⟨-1811928171688660109222709490111412542596477035219489, 1814886845574104094649207500625077375020207561558524⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0528Geometry.ds, E8TAxisProd0528Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4022547840806054118601033654855564855960139299 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0528CertifiedArithmetic

end


