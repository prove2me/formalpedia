-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0306CertifiedArithmetic__17
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0306CertifiedArithmetic__17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:35:30.635617+00:00
-- url     : https://prove2.me/theorems/d895fe03-6e8f-4540-a1c9-cf62f1b1d765
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic (+16 modules: GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0306CertifiedArithmetic (+16 modules: GeneralCK/Certificates/E8TAxisProd0307CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0308CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0309CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0310CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0311CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0312CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0313CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0314CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0315CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0316CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0317CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0318CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0319CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0320CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0321CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0322CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0303GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0306GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0304GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0305GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0295GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0305GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0306GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0306GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0297Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0308GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0314GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0314GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0315GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0315GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0317GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0318GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0318GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0320GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0321Geometry__24

-- ===== source module GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0306GraphCenterA.qJetBox,
   E8TAxisProd0306GraphCenterB.qJetBox,
   E8TAxisProd0306GraphCenterC.qJetBox,
   E8TAxisProd0306GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0306GraphWholeA.qJetBox,
   E8TAxisProd0306GraphWholeB.qJetBox,
   E8TAxisProd0306GraphWholeC.qJetBox,
   E8TAxisProd0306GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42326609663176438066848897882827161536563106321, 42326609663176438066848897882827381221453385171⟩
  | 0, 2 => ⟨122623434066724945188567545116356560072464425795, 122623434066724945188567545116357437539682741263⟩
  | 1, 1 => ⟨123707517033435036644416712756030912209220112280, 123707517033435036644416712756032514539608517835⟩
  | 0, 3 => ⟨244865544577829370045604261199989133086949784531, 244865544577829370045604261199992040291248000857⟩
  | 1, 2 => ⟨328740393815276424428196023903718789910369873875, 328740393815276424428196023903724049365631436983⟩
  | 2, 1 => ⟨331295182754840366021865764310494550105234912333, 331295182754840366021865764310504187487954951510⟩
  | 0, 4 => ⟨406284125945606024504754088198209512234950711527, 406284125945606024504754088198219608095499072463⟩
  | 1, 3 => ⟨602452773120535930083043702014896726459275865806, 602452773120535930083043702014915205791597680769⟩
  | 2, 2 => ⟨799837368751987156119765985793334951599222937552, 799837368751987156119765985793369187742477347734⟩
  | 3, 1 => ⟨805302125578957298803232108768662761048885344923, 805302125578957298803232108768726669826907724188⟩
  | 0, 5 => ⟨-2072508280047033962719398103843371141602499688243978, 2083418498131936077501846603868142355572314394875812⟩
  | 1, 4 => ⟨-4064762289613633801142421841264780818152898806361846, 4081227801977694025019797061067181476995310263633321⟩
  | 2, 3 => ⟨-7979659191747238401410609683820467074299333472872954, 8003417694235803355291347638297581487705784378599930⟩
  | 3, 2 => ⟨-15675252274480670023318365711834084705752412502202517, 15706478373560016856359221949761199382358342188707736⟩
  | 4, 1 => ⟨-30808316363844610253657568810707326471724892764741885, 30840322285867087946328683979218847973055156827883054⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0306Geometry.ds, E8TAxisProd0306Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39825307032000467916176326270050420418650329035 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0306CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0307GraphCenterA.qJetBox,
   E8TAxisProd0307GraphCenterB.qJetBox,
   E8TAxisProd0307GraphCenterC.qJetBox,
   E8TAxisProd0307GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0307GraphWholeA.qJetBox,
   E8TAxisProd0307GraphWholeB.qJetBox,
   E8TAxisProd0307GraphWholeC.qJetBox,
   E8TAxisProd0307GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38088697356332681304138038007932662346712265892, 38088697356332681304138038007932861318554188074⟩
  | 0, 2 => ⟨111312426191798077722560289880147027894653407594, 111312426191798077722560289880147816085380227803⟩
  | 1, 1 => ⟨112308142456424443322367084165126342308253453461, 112308142456424443322367084165127778001363110006⟩
  | 0, 3 => ⟨224060439018152909453704979166784731541686917604, 224060439018152909453704979166787332054649338943⟩
  | 1, 2 => ⟨301107773620712143797520666271495024224505504955, 301107773620712143797520666271499718065924356156⟩
  | 2, 1 => ⟨303473048612504577904610414465562248566425279255, 303473048612504577904610414465570834087763546621⟩
  | 0, 4 => ⟨374349404853221565283259164233955979777319366568, 374349404853221565283259164233964962635513917638⟩
  | 1, 3 => ⟨555971312698568918289869849748554143473634514838, 555971312698568918289869849748570554771975657220⟩
  | 2, 2 => ⟨738727553395663184571471046884005458364766130470, 738727553395663184571471046884035818727076841967⟩
  | 3, 1 => ⟨743814145019561328698970493811353710027822804416, 743814145019561328698970493811410308365423839307⟩
  | 0, 5 => ⟨-1849973207258983810218400976078435569356642467962896, 1859922457370982158606618350547999303129420936641663⟩
  | 1, 4 => ⟨-3626447162163359590672711260893887195522185393128417, 3641466436866376432208238905494440631518198481882011⟩
  | 2, 3 => ⟨-7115631950378662329900134517488080467499445312110006, 7137309842019474837292000600788044022686891875019651⟩
  | 3, 2 => ⟨-13971025077005214283767928784200027564842718889411489, 13999523792394932578515917713238801929167947532613016⟩
  | 4, 1 => ⟨-27445169366751067137766364328955345337032991810238190, 27474386244321187339938058812026832408590769308738323⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0307Geometry.ds, E8TAxisProd0307Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35819848188379525232402544894931478499659437228 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0307CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0308GraphCenterA.qJetBox,
   E8TAxisProd0308GraphCenterB.qJetBox,
   E8TAxisProd0308GraphCenterC.qJetBox,
   E8TAxisProd0308GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0308GraphWholeA.qJetBox,
   E8TAxisProd0308GraphWholeB.qJetBox,
   E8TAxisProd0308GraphWholeC.qJetBox,
   E8TAxisProd0308GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34369306001626172939087465068372954624887336766, 34369306001626172939087465068373135301420070629⟩
  | 0, 2 => ⟨101212305837791763580568917958402049075132994555, 101212305837791763580568917958402758725387918838⟩
  | 1, 1 => ⟨102214767850700068416480693041100503329670516242, 102214767850700068416480693041101792609561879502⟩
  | 0, 3 => ⟨205296574722483886712946693864318624285538688809, 205296574722483886712946693864320955824506300967⟩
  | 1, 2 => ⟨276234015561137235761411913077270146365251163241, 276234015561137235761411913077274344831000522957⟩
  | 2, 1 => ⟨278634604250059530441083534154226391799650587228, 278634604250059530441083534154234057271379707000⟩
  | 0, 4 => ⟨345374993753110044353467355185125258083088933996, 345374993753110044353467355185133270262476861086⟩
  | 1, 3 => ⟨513809557674126241828975295597485268126660204522, 513809557674126241828975295597499877892646048942⟩
  | 2, 2 => ⟨683404608824440072314557899321728064941032734269, 683404608824440072314557899321755052560737676239⟩
  | 3, 1 => ⟨688596377666673339002434867963503149425409275995, 688596377666673339002434867963553392767062170717⟩
  | 0, 5 => ⟨-1649787844467215030432366065612033686539393475261907, 1658831887297745169823370023843613274098136689000004⟩
  | 1, 4 => ⟨-3232307429087270715871116677233927011376337758062781, 3245960795688767829692195569557185720084167757294854⟩
  | 2, 3 => ⟨-6338999591759932965643616758368561469937308999957731, 6358709010500725827005626423063743185277623456595669⟩
  | 3, 2 => ⟨-12439813889402078678846031118527084208137240428227462, 12465731807290191826402429211501804871828338649056594⟩
  | 4, 1 => ⟨-24424738778363968365256808459144405024527479237360804, 24451326314390879986411895048600224608760636595457660⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0308Geometry.ds, E8TAxisProd0308Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32306569786869793293057968013240166994732754856 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0308CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0309GraphCenterA.qJetBox,
   E8TAxisProd0309GraphCenterB.qJetBox,
   E8TAxisProd0309GraphCenterC.qJetBox,
   E8TAxisProd0309GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0309GraphWholeA.qJetBox,
   E8TAxisProd0309GraphWholeB.qJetBox,
   E8TAxisProd0309GraphWholeC.qJetBox,
   E8TAxisProd0309GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30870670098076615375388581178916119940788106973, 30870670098076615375388581178916283749669123632⟩
  | 0, 2 => ⟨91714872382651117794881219113340215719031906864, 91714872382651117794881219113340853761164235216⟩
  | 1, 1 => ⟨92634337024426740236447197554796286496633826797, 92634337024426740236447197554797442593891992739⟩
  | 0, 3 => ⟨187561605290858664788976273471103857570486912638, 187561605290858664788976273471105947112438476846⟩
  | 1, 2 => ⟨252635237947745892211564740869739981688304355224, 252635237947745892211564740869743735651679894786⟩
  | 2, 1 => ⟨254855787855992629382242844129794513011995818152, 254855787855992629382242844129801354806477729555⟩
  | 0, 4 => ⟨317870558031780971980477768443041397213607010211, 317870558031780971980477768443048550982255218276⟩
  | 1, 3 => ⟨473678395311444240360073146084464695709839748553, 473678395311444240360073146084477716439517861471⟩
  | 2, 2 => ⟨630569021513365394046423835675862489282904522049, 630569021513365394046423835675886508163048722882⟩
  | 3, 1 => ⟨635401057374077812140734389405947553255904831260, 635401057374077812140734389405992212806650293120⟩
  | 0, 5 => ⟨-1462277971788696716816459764919656316113538987408493, 1470435269354992989138272858141215540778306127529863⟩
  | 1, 4 => ⟨-2863277561568931238111479184238556999528796378711850, 2875588456007925898494701372269489825233710424259013⟩
  | 2, 3 => ⟨-5612149204746965390647510936653240978458017636779704, 5629917411473540931440244023376428419621739663423396⟩
  | 3, 2 => ⟨-11007360301545127361944785187259139650325537676362986, 11030722106993176050472611042778822829533148092701620⟩
  | 4, 1 => ⟨-21600332373169650921194476749793605363164910416300379, 21624288531620556724504798665859104257378015350386829⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0309Geometry.ds, E8TAxisProd0309Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 29003352651723064413522143707638564828690724828 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0309CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0310GraphCenterA.qJetBox,
   E8TAxisProd0310GraphCenterB.qJetBox,
   E8TAxisProd0310GraphCenterC.qJetBox,
   E8TAxisProd0310GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0310GraphWholeA.qJetBox,
   E8TAxisProd0310GraphWholeB.qJetBox,
   E8TAxisProd0310GraphWholeC.qJetBox,
   E8TAxisProd0310GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34242950894903287633870050089241592957506342359, 34242950894903287633870050089241773259898561905⟩
  | 0, 2 => ⟨100955954776870225906689422390360347114842479192, 100955954776870225906689422390361055199083454690⟩
  | 1, 1 => ⟨101869876486391861789629624274453357860085204211, 101869876486391861789629624274454644261869228605⟩
  | 0, 3 => ⟨204865256081590996547831566952676472273350090963, 204865256081590996547831566952678798553242828344⟩
  | 1, 2 => ⟨275592374101219975585278416771996686126312695057, 275592374101219975585278416772000875028767690559⟩
  | 2, 1 => ⟨277781253256343555566618765611746219503948943756, 277781253256343555566618765611753867362109916646⟩
  | 0, 4 => ⟨344735011574885595044686364626502871208317895702, 344735011574885595044686364626510864500505111853⟩
  | 1, 3 => ⟨512817065339622296348309373726642955538463373444, 512817065339622296348309373726657530700491106525⟩
  | 2, 2 => ⟨681957416376838889588195103705321468035542808822, 681957416376838889588195103705348391414443924876⟩
  | 3, 1 => ⟨686691809517427284334615364759548483027703294487, 686691809517427284334615364759598606125848372312⟩
  | 0, 5 => ⟨-1645840125511144366674147457934971530695098564948392, 1654864126869028839039795573983586730352587990934217⟩
  | 1, 4 => ⟨-3224545390946914046667976664252048909895358361243353, 3238167747891089156166155869593930827529986575248269⟩
  | 2, 3 => ⟨-6323721773256143242933427347317477850764881336919217, 6343384566166142432947970163210672471207915165142697⟩
  | 3, 2 => ⟨-12409721058427888609847549027810925195737754283772419, 12435572211262162266198675783659754446231112405034318⟩
  | 4, 1 => ⟨-24365431295511134067375831808265857973442642401375199, 24391932217408304557748058830419800569947389297167619⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0310Geometry.ds, E8TAxisProd0310Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32186995916837146006465229548107803180326289925 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0310CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0311GraphCenterA.qJetBox,
   E8TAxisProd0311GraphCenterB.qJetBox,
   E8TAxisProd0311GraphCenterC.qJetBox,
   E8TAxisProd0311GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0311GraphWholeA.qJetBox,
   E8TAxisProd0311GraphWholeB.qJetBox,
   E8TAxisProd0311GraphWholeC.qJetBox,
   E8TAxisProd0311GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30756172936677166053121763801279718993660365680, 30756172936677166053121763801279882463975338724⟩
  | 0, 2 => ⟨91480668558119941030445134426675626394832558421, 91480668558119941030445134426676263035960710144⟩
  | 1, 1 => ⟨92318912798531028047240781464276455430491385424, 92318912798531028047240781464277608959289087818⟩
  | 0, 3 => ⟨187164637339706459390736043669178538116281383382, 187164637339706459390736043669180623015160493942⟩
  | 1, 2 => ⟨252043715167905827353803943052565390361829225507, 252043715167905827353803943052569135905768213678⟩
  | 2, 1 => ⟨254068416376803484372640976217014437134274199684, 254068416376803484372640976217021263455801380214⟩
  | 0, 4 => ⟨317278330730574196424962093526828178003049623209, 317278330730574196424962093526835315372818648072⟩
  | 1, 3 => ⟨472758319209253028984661706251880242870072555528, 472758319209253028984661706251893233641706856246⟩
  | 2, 2 => ⟨629225749907774469708962600950381388048333108057, 629225749907774469708962600950405351429414749402⟩
  | 3, 1 => ⟨633632096604922747083231603886168150456711714932, 633632096604922747083231603886212706303996466241⟩
  | 0, 5 => ⟨-1458674893439212647580833576051120802918896478828515, 1466813623082133246849644176844270045648847052740420⟩
  | 1, 4 => ⟨-2856195589089146641266923297634574442817743650836306, 2868477859403471050544089225405816020900371094885956⟩
  | 2, 3 => ⟨-5598214710659071537322068288374998356050278346438443, 5615940186206749382418181512480677606573411577565193⟩
  | 3, 2 => ⟨-10979922857251010463308549597229647061569057414972132, 11003224321651558534036067173816778648215893005220380⟩
  | 4, 1 => ⟨-21546276899257905836318930647097078042380112757648999, 21570157119789066239765851181088147419070031796391516⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0311Geometry.ds, E8TAxisProd0311Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28895057523146441979425262131510201846282691516 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0311CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0312GraphCenterA.qJetBox,
   E8TAxisProd0312GraphCenterB.qJetBox,
   E8TAxisProd0312GraphCenterC.qJetBox,
   E8TAxisProd0312GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0312GraphWholeA.qJetBox,
   E8TAxisProd0312GraphWholeB.qJetBox,
   E8TAxisProd0312GraphWholeC.qJetBox,
   E8TAxisProd0312GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42173521539606480272235226161693896628636186009, 42173521539606480272235226161694115857083298854⟩
  | 0, 2 => ⟨122317669351270887320664073223009337669205497079, 122317669351270887320664073223010213204678771134⟩
  | 1, 1 => ⟨123297061907234399597933857512107505499619661970, 123297061907234399597933857512109104266529137310⟩
  | 0, 3 => ⟨244358155447635916734606305253006779841434260328, 244358155447635916734606305253009680501826833677⟩
  | 1, 2 => ⟨327988048130420809263158729866636490860482761539, 327988048130420809263158729866641738372977485956⟩
  | 2, 1 => ⟨330296433818537655147462423580902792819362040306, 330296433818537655147462423580912408144278180412⟩
  | 0, 4 => ⟨405538690844258455012169351535686469376143246588, 405538690844258455012169351535696541448557655400⟩
  | 1, 3 => ⟨601300654612502612538761430162531683704291320248, 601300654612502612538761430162550119310323216558⟩
  | 2, 2 => ⟨798161431767839252478744365458951056782192419372, 798161431767839252478744365458985211549968334615⟩
  | 3, 1 => ⟨803099571141825238036170155392525030290807398901, 803099571141825238036170155392588786423271692199⟩
  | 0, 5 => ⟨-2067815230382598010372687274586274823378845457061473, 2078702751339894640134451530624644909209587583100358⟩
  | 1, 4 => ⟨-4055528785285921834293885160627950822100603498133465, 4071959076212643984564786528113527598157226685298089⟩
  | 2, 3 => ⟨-7961473262905687846145328224860668939574278436173328, 7985178370429676688179161532543857704338329068957455⟩
  | 3, 2 => ⟨-15639407729175835489999902899902375383397555682782645, 15670555980227130203845016094210901244249129737700582⟩
  | 4, 1 => ⟨-30737626291216094992558401878955171875575099714172906, 30769527115404070604864479381986322146890892395069446⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0312Geometry.ds, E8TAxisProd0312Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39680287268729906770661238545341137124583169804 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0312CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0313GraphCenterA.qJetBox,
   E8TAxisProd0313GraphCenterB.qJetBox,
   E8TAxisProd0313GraphCenterC.qJetBox,
   E8TAxisProd0313GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0313GraphWholeA.qJetBox,
   E8TAxisProd0313GraphWholeB.qJetBox,
   E8TAxisProd0313GraphWholeC.qJetBox,
   E8TAxisProd0313GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37949731749008584782982551256841337779500164251, 37949731749008584782982551256841536338592845714⟩
  | 0, 2 => ⟨111032642923678269234796983378948176370226989596, 111032642923678269234796983378948962823619517182⟩
  | 1, 1 => ⟨111932191813606432803935314401992150282204789928, 111932191813606432803935314401993582776298376399⟩
  | 0, 3 => ⟨223592933768777722719493230114080860603337843328, 223592933768777722719493230114083455260939217331⟩
  | 1, 2 => ⟨300413477495809484465782406742552227943769022434, 300413477495809484465782406742556911118808230732⟩
  | 2, 1 => ⟨302550612017792805908087973326977687477876521526, 302550612017792805908087973326986253327497884694⟩
  | 0, 4 => ⟨373659187685204658611530155043837861812512880502, 373659187685204658611530155043846823551622253937⟩
  | 1, 3 => ⟨554902795665378184718313738168241924037800814275, 554902795665378184718313738168258296584696914669⟩
  | 2, 2 => ⟨737171465415320979121840789038445294694415171337, 737171465415320979121840789038475583036369973092⟩
  | 3, 1 => ⟨741767878750886063377208170591550026118789073642, 741767878750886063377208170591606489519153415730⟩
  | 0, 5 => ⟨-1845673304390800192035765562132103912499411209358260, 1855601137697153837985620765162155108313470651886828⟩
  | 1, 4 => ⟨-3617990054887236595109457742405835131210770921421243, 3632976114233727505258493791844909262746108488736540⟩
  | 2, 3 => ⟨-7098980893132939369164983741007085488986059919643939, 7120608578854110120127394318212477566128041568626027⟩
  | 3, 2 => ⟨-13938217116439123000444143254123142733271548104860787, 13966643163331024689814731064188009422815722344374725⟩
  | 4, 1 => ⟨-27380490410543549462784883278772004059103084260333238, 27409610796399938026119835463090178293779187966080390⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0313Geometry.ds, E8TAxisProd0313Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35688273522354325330937624971384736868051249078 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0313CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0314GraphCenterA.qJetBox,
   E8TAxisProd0314GraphCenterB.qJetBox,
   E8TAxisProd0314GraphCenterC.qJetBox,
   E8TAxisProd0314GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0314GraphWholeA.qJetBox,
   E8TAxisProd0314GraphWholeB.qJetBox,
   E8TAxisProd0314GraphWholeC.qJetBox,
   E8TAxisProd0314GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42020815225775634976293300095101980194925641321, 42020815225775634976293300095102198967872320390⟩
  | 0, 2 => ⟨122012538290184022369282456484586926855807121534, 122012538290184022369282456484587800463696966592⟩
  | 1, 1 => ⟨122887546313565731319637273120242394397419424639, 122887546313565731319637273120243989608557013314⟩
  | 0, 3 => ⟨243851697329922664672249240234141267297741908760, 243851697329922664672249240234144161428736387272⟩
  | 1, 2 => ⟨327237141349507589428650770865960793368539966967, 327237141349507589428650770865966028964811147592⟩
  | 2, 1 => ⟨329299777920387238169346221720073807426028318172, 329299777920387238169346221720083400742267034178⟩
  | 0, 4 => ⟨404794505653542528055842293252522454130208881300, 404794505653542528055842293252532502469362047783⟩
  | 1, 3 => ⟨600150526274817625836611899225063965391801007192, 600150526274817625836611899225082357372478690814⟩
  | 2, 2 => ⟨796488506864426252787098770614561113531036836356, 796488506864426252787098770614595187111255169301⟩
  | 3, 1 => ⟨800901333701338831750367007476477483678517342363, 800901333701338831750367007476541087518150309399⟩
  | 0, 5 => ⟨-2063130227473775891436172524155713447861686362672309, 2073995070827165677338575790995914291697560359335732⟩
  | 1, 4 => ⟨-4046311113035318869198355663093290307294947648923037, 4062706215956377209708559231862939043782654731331436⟩
  | 2, 3 => ⟨-7943318531053094942307367944917422635446626773410112, 7966970304012861895462567746168504904112155551833178⟩
  | 3, 2 => ⟨-15603624721543836853278036530578064260462801442653869, 15634695237472289007632706776031665602384616310319803⟩
  | 4, 1 => ⟨-30667057699350480298151082277504814621634603372000511, 30698853640592055431775812620628082243994380302257112⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0314Geometry.ds, E8TAxisProd0314Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39535631111351658313881747399187552217167592575 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0314CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0315GraphCenterA.qJetBox,
   E8TAxisProd0315GraphCenterB.qJetBox,
   E8TAxisProd0315GraphCenterC.qJetBox,
   E8TAxisProd0315GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0315GraphWholeA.qJetBox,
   E8TAxisProd0315GraphWholeB.qJetBox,
   E8TAxisProd0315GraphWholeC.qJetBox,
   E8TAxisProd0315GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37811115505755747544198385964764233326986980893, 37811115505755747544198385964764431474181905788⟩
  | 0, 2 => ⟨110753443498190302739264075590234829947927021708, 110753443498190302739264075590235614667730851394⟩
  | 1, 1 => ⟨111557108206647484602206304160516668442739431287, 111557108206647484602206304160518097744744472388⟩
  | 0, 3 => ⟨223126290565471528538855354266194691451139358341, 223126290565471528538855354266197280266355687234⟩
  | 1, 2 => ⟨299720515860876144582628402909544148514677719542, 299720515860876144582628402909548821047040572920⟩
  | 2, 1 => ⟨301630118781769160860979705014856934676451282104, 301630118781769160860979705014865480898171832050⟩
  | 0, 4 => ⟨372970130841357631604022300254012240988540142879, 372970130841357631604022300254021181657134619899⟩
  | 1, 3 => ⟨553836128246466352298261618376833984801959725753, 553836128246466352298261618376850318686589017351⟩
  | 2, 2 => ⟨735618178708300944304026446455579525794884389893, 735618178708300944304026446455609742282280569560⟩
  | 3, 1 => ⟨739725629035825361193649539263716282517368049362, 739725629035825361193649539263772611291322888989⟩
  | 0, 5 => ⟨-1841381024116699552751622880633101157261355340608931, 1851287480068866037050129064143885745075230516283220⟩
  | 1, 4 => ⟨-3609547952989933101648361757017922076358207210126123, 3624500860819662284733445586040221742927618922380571⟩
  | 2, 3 => ⟨-7082359414304088256239968133408922132963908947242495, 7103937000717212654368432727338342183551757275436783⟩
  | 3, 2 => ⟨-13905467513237809315749128732437571927103107994927581, 13933821075062416692675471663943432077277216839294749⟩
  | 4, 1 => ⟨-27315926668441767019355045649218164649098741581288852, 27344950886610695029037578353730869554025114306929134⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0315Geometry.ds, E8TAxisProd0315Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35557031404698802796038482939422782012699623130 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0315CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0316GraphCenterA.qJetBox,
   E8TAxisProd0316GraphCenterB.qJetBox,
   E8TAxisProd0316GraphCenterC.qJetBox,
   E8TAxisProd0316GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0316GraphWholeA.qJetBox,
   E8TAxisProd0316GraphWholeB.qJetBox,
   E8TAxisProd0316GraphWholeC.qJetBox,
   E8TAxisProd0316GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34116915890247105771110281188014293990420037804, 34116915890247105771110281188014473919442645761⟩
  | 0, 2 => ⟨100700142364544710571736186238241421029934215566, 100700142364544710571736186238242127551540153735⟩
  | 1, 1 => ⟨101525786398972398562897679842616077042963723339, 101525786398972398562897679842617360572881236339⟩
  | 0, 3 => ⟨204434736744149599822980818049922897577537687962, 204434736744149599822980818049925218610024861254⟩
  | 1, 2 => ⟨274951972180507381822146518800602345568233685602, 274951972180507381822146518800606524928681865888⟩
  | 2, 1 => ⟨276929709621895370941793121663531446193076591372, 276929709621895370941793121663539076476981123826⟩
  | 0, 4 => ⟨344096107949714416415392509983673591067028915457, 344096107949714416415392509983681565515531554234⟩
  | 1, 3 => ⟨511826294479174661921725310238866441460542552532, 511826294479174661921725310238880982098412234705⟩
  | 2, 2 => ⟨680512833262419242447636175492121233698614892661, 680512833262419242447636175492148092984943671383⟩
  | 3, 1 => ⟨684790984778572595339782411793510627227682934308, 684790984778572595339782411793560630360011822216⟩
  | 0, 5 => ⟨-1641899687836473364848120131283428611038262015043918, 1650903687453618582148345806108086406995016561588761⟩
  | 1, 4 => ⟨-3216797686660740187620832691767076304941664012167756, 3230389099793785890095270493077712476388792360751795⟩
  | 2, 3 => ⟨-6308472208984874570874893635195568451097765730811287, 6328088487357165522120699829575933544486983793720270⟩
  | 3, 2 => ⟨-12379683969876203522102276274570062805031470976730828, 12405468549852719877193538830510176504517958282281553⟩
  | 4, 1 => ⟨-24306233857698676944659223038934087000820262076437593, 24332648504628175717999604550832069832377810104447450⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0316Geometry.ds, E8TAxisProd0316Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32067726590344655566524292904775480242224031341 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0316CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0317GraphCenterA.qJetBox,
   E8TAxisProd0317GraphCenterB.qJetBox,
   E8TAxisProd0317GraphCenterC.qJetBox,
   E8TAxisProd0317GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0317GraphWholeA.qJetBox,
   E8TAxisProd0317GraphWholeB.qJetBox,
   E8TAxisProd0317GraphWholeC.qJetBox,
   E8TAxisProd0317GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30641968220119869710967812640303498919361050915, 30641968220119869710967812640303662051806692151⟩
  | 0, 2 => ⟨91246960481110833965902339275207603869919003038, 91246960481110833965902339275208239113049775122⟩
  | 1, 1 => ⟨92004227257717329479464844251722714325184604011, 92004227257717329479464844251723865291062038919⟩
  | 0, 3 => ⟨186768409047062045361015319349488367517724844697, 186768409047062045361015319349490447783688690318⟩
  | 1, 2 => ⟨251453341483325408750812295489058944384930639401, 251453341483325408750812295489062681527896670910⟩
  | 2, 1 => ⟨253282722470280787045393539603813682562336054168, 253282722470280787045393539603820493444908636875⟩
  | 0, 4 => ⟨316687104157882119812265244734937658476091088588, 316687104157882119812265244734944779483842241752⟩
  | 1, 3 => ⟨471839842460835736782046436868715162308554114971, 471839842460835736782046436868728123189455242712⟩
  | 2, 2 => ⟨627884904564175952254760160041659281296787203814, 627884904564175952254760160041683189303436520410⟩
  | 3, 1 => ⟨631866618469786453079852925690864318761788919170, 631866618469786453079852925690908771138479466085⟩
  | 0, 5 => ⟨-1455078735823826835480565241112653518437898565981734, 1463198937610056151770770017754472027173005406286116⟩
  | 1, 4 => ⟨-2849127240386222091256124569495611325227053886797507, 2861380953417669938097409333856395222996165949547647⟩
  | 2, 3 => ⟨-5584307069617280524884877891420135987493110831610118, 5601989927420446839744539335433619526210153111059848⟩
  | 3, 2 => ⟨-10952538386870844607563384896991423916182071556825184, 10975779706229999855378301162917137423352628325092030⟩
  | 4, 1 => ⟨-21492325995211315233384305092660610276728490874653730, 21516130622495318003860585465013295391982372703238979⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0317Geometry.ds, E8TAxisProd0317Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28787040480120109793461652643606343750127387302 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0317CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0318GraphCenterA.qJetBox,
   E8TAxisProd0318GraphCenterB.qJetBox,
   E8TAxisProd0318GraphCenterC.qJetBox,
   E8TAxisProd0318GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0318GraphWholeA.qJetBox,
   E8TAxisProd0318GraphWholeB.qJetBox,
   E8TAxisProd0318GraphWholeC.qJetBox,
   E8TAxisProd0318GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33991200314970987190046853412579803054976275908, 33991200314970987190046853412579982611398574752⟩
  | 0, 2 => ⟨100444867602528083862600423063039040587628793085, 100444867602528083862600423063039745549971365286⟩
  | 1, 1 => ⟨101182496040361844338533261724558436122121530772, 101182496040361844338533261724559716786399998356⟩
  | 0, 3 => ⟨204005015363021663678479043540347029303588886545, 204005015363021663678479043540349345100314064667⟩
  | 1, 2 => ⟨274312807648909075402970339993720252944933874193, 274312807648909075402970339993724422784615887979⟩
  | 2, 1 => ⟨276079970087797886389537975683604756727987082135, 276079970087797886389537975683612369476860411852⟩
  | 0, 4 => ⟨343458281192733839233382195058346012508696426172, 343458281192733839233382195058353968156931416279⟩
  | 1, 3 => ⟨510837242289979946442626478345133941061606345786, 510837242289979946442626478345148447254936436591⟩
  | 2, 2 => ⟨679070855083321922738440368022437503414882248073, 679070855083321922738440368022464298756533516395⟩
  | 3, 1 => ⟨682893896856568693741138399771958385804375979022, 682893896856568693741138399772008269247950860237⟩
  | 0, 5 => ⟨-1637966527457787156740367664796737401298000720229151, 1646950565741650424168216879941852499366712182602733⟩
  | 1, 4 => ⟨-3209064308482503356306494217758673228448359550721980, 3222624843934612363037506453341030672873573545628109⟩
  | 2, 3 => ⟨-6293250883973961130878913012028427312225194581342800, 6312820759144187472186633346362769557671193271170612⟩
  | 3, 2 => ⟨-12349702594835407822467782979825104052669520032709630, 12375420794246869272617882379638023477314050403321382⟩
  | 4, 1 => ⟨-24247146409010794703626641229290701160655723467627221, 24273475120322038371504405174299248371565083311227609⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0318Geometry.ds, E8TAxisProd0318Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31948761163963980922891485846745942648666509091 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0318CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0319GraphCenterA.qJetBox,
   E8TAxisProd0319GraphCenterB.qJetBox,
   E8TAxisProd0319GraphCenterC.qJetBox,
   E8TAxisProd0319GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0319GraphWholeA.qJetBox,
   E8TAxisProd0319GraphWholeB.qJetBox,
   E8TAxisProd0319GraphWholeC.qJetBox,
   E8TAxisProd0319GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30528055329297856340650733277516500395367465776, 30528055329297856340650733277516663190639042649⟩
  | 0, 2 => ⟨91013747227832072668638725471462302238237481544, 91013747227832072668638725471462936086371256972⟩
  | 1, 1 => ⟨91690278966865385408333995252947997479432952654, 91690278966865385408333995252949145887918509090⟩
  | 0, 3 => ⟨186372919162994694153965318524688313526390616885, 186372919162994694153965318524690389169574203284⟩
  | 1, 2 => ⟨250864114896443500011137939060015013897452664098, 250864114896443500011137939060018742657869086453⟩
  | 2, 1 => ⟨252498703106156461658524699451605189942793963400, 252498703106156461658524699451611985420338132843⟩
  | 0, 4 => ⟨316096876746207058598311454915764213015441248397, 316096876746207058598311454915771317697953168816⟩
  | 1, 3 => ⟨470922962457121263914751243500103058605960321368, 470922962457121263914751243500115989663288392249⟩
  | 2, 2 => ⟨626546481388593554121469497383589497339599966518, 626546481388593554121469497383613350096169314807⟩
  | 3, 1 => ⟨630104616832490952120092487521673354976121894975, 630104616832490952120092487521717704114567004831⟩
  | 0, 5 => ⟨-1451489490734615589302065293833008641967819511522842, 1459591205361157696280349787934910389238977963553305⟩
  | 1, 4 => ⟨-2842072499257795085299411471356333113921738968497573, 2854297722091603691196927492877594776692222402920231⟩
  | 2, 3 => ⟨-5570426249717876502591325076051434115844578855038669, 5588066603197389454039281937092879458843888536886283⟩
  | 3, 2 => ⟨-10925206827596138822419330332290990265736347101486948, 10948388197905270435584640448976453087942525040046312⟩
  | 4, 1 => ⟨-21438479537261114170021019028338879887514829191728222, 21462208915938472228770691535999989372568403843115095⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0319Geometry.ds, E8TAxisProd0319Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28679300930996857519080220720063314326925906789 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0319CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0320GraphCenterA.qJetBox,
   E8TAxisProd0320GraphCenterB.qJetBox,
   E8TAxisProd0320GraphCenterC.qJetBox,
   E8TAxisProd0320GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0320GraphWholeA.qJetBox,
   E8TAxisProd0320GraphWholeB.qJetBox,
   E8TAxisProd0320GraphWholeC.qJetBox,
   E8TAxisProd0320GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27701379718010119011192140841028094313871983824, 27701379718010119011192140841028242910907646726⟩
  | 0, 2 => ⟨83032226433944152368764641267535643693837535231, 83032226433944152368764641267536217496287152151⟩
  | 1, 1 => ⟨83874936946956327113275941910821212335709942703, 83874936946956327113275941910822249155152507136⟩
  | 0, 3 => ⟨171216386765142039823003637400834054712204959711, 171216386765142039823003637400835927914303233636⟩
  | 1, 2 => ⟨230866768036364367299675774071194074482954940822, 230866768036364367299675774071197431743340892387⟩
  | 2, 1 => ⟨232919759259032767640664200154744694226138847091, 232919759259032767640664200154750802019991452457⟩
  | 0, 4 => ⟨292375847297366344793681716453697327266522678677, 292375847297366344793681716453703717433440482107⟩
  | 1, 3 => ⟨436432184940208071445604419139075591553510515377, 436432184940208071445604419139087200727007848552⟩
  | 2, 2 => ⟨581498884362629847282947292052475158771421603158, 581498884362629847282947292052496543665738615128⟩
  | 3, 1 => ⟨585995807969337230603800444711454662481960720799, 585995807969337230603800444711494373513191444072⟩
  | 0, 5 => ⟨-1291394322628128351791209731593273718062909082476781, 1298713850608731939938691325836412631334945849300392⟩
  | 1, 4 => ⟨-2527121901551450160965586566120604660507243627159824, 2538159661208636026345010913227469842404295897774239⟩
  | 2, 3 => ⟨-4950352965124950743744536566012591762579412329761310, 4966275238684266348650451355953175455610711377486426⟩
  | 3, 2 => ⟨-9703721389786049178993445545872481270125045392197718, 9724648509166640168113964956874043378105606041039869⟩
  | 4, 1 => ⟨-19031131138736010899649194427392778448736768310830790, 19052578888186731211450859494785741311907225316285080⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0320Geometry.ds, E8TAxisProd0320Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26012707454364745424163313102171250657191018815 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0320CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0321GraphCenterA.qJetBox,
   E8TAxisProd0321GraphCenterB.qJetBox,
   E8TAxisProd0321GraphCenterC.qJetBox,
   E8TAxisProd0321GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0321GraphWholeA.qJetBox,
   E8TAxisProd0321GraphWholeB.qJetBox,
   E8TAxisProd0321GraphWholeC.qJetBox,
   E8TAxisProd0321GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24833090253878558214270267286698209212260940819, 24833090253878558214270267286698344086802376068⟩
  | 0, 2 => ⟨75100965620386672379430289925381500064129216324, 75100965620386672379430289925382016176505214234⟩
  | 1, 1 => ⟨75872732260217828068987530356790550827945512286, 75872732260217828068987530356791480708104993110⟩
  | 0, 3 => ⟨156160895076984149143348094575008253572213568784, 156160895076984149143348094575009932847269474443⟩
  | 1, 2 => ⟨210798034149199449250902039829017511243932690680, 210798034149199449250902039829020513464569244685⟩
  | 2, 1 => ⟨212695093711071382840204861815176295154545993432, 212695093711071382840204861815181746959355117887⟩
  | 0, 4 => ⟨268749784319523739444697444936047787875098630562, 268749784319523739444697444936053495410787967545⟩
  | 1, 3 => ⟨401870015054641642571542918920758111102605712884, 401870015054641642571542918920768459966036057088⟩
  | 2, 2 => ⟨535933067889334562090470138142516723065094397796, 535933067889334562090470138142535758753102753827⟩
  | 3, 1 => ⟨540117752848967495630994890023269596395840085753, 540117752848967495630994890023304898586627452375⟩
  | 0, 5 => ⟨-1139861658252427031296496621423453574878009528737553, 1146392321117562972425316867693476606091729464832784⟩
  | 1, 4 => ⟨-2229191845067058828627057331755011936905040034247304, 2239027756551135697179176609267851121755460548427140⟩
  | 2, 3 => ⟨-4364117249088733650144093240806079122126539849666322, 4378293502423001293563591111379894792468820150496733⟩
  | 3, 2 => ⟨-8549518071224659212955290523237383709352977191811253, 8568140161696880527777974633852513191672623277813582⟩
  | 4, 1 => ⟨-16757595779358083963909425811887994466268671380768654, 16776673999169771221526831516350823551422793469353466⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0321Geometry.ds, E8TAxisProd0321Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23307310618592673973449902437601426202528759869 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0321CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0322GraphCenterA.qJetBox,
   E8TAxisProd0322GraphCenterB.qJetBox,
   E8TAxisProd0322GraphCenterC.qJetBox,
   E8TAxisProd0322GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0322GraphWholeA.qJetBox,
   E8TAxisProd0322GraphWholeB.qJetBox,
   E8TAxisProd0322GraphWholeC.qJetBox,
   E8TAxisProd0322GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27597723102640027521994464747155572841700752415, 27597723102640027521994464747155721132248453659⟩
  | 0, 2 => ⟨82818434226385268783647885772687846087510377386, 82818434226385268783647885772688418628651858229⟩
  | 1, 1 => ⟨83586694227390254908554046892087232406096295129, 83586694227390254908554046892088266917849321525⟩
  | 0, 3 => ⟨170851259467202726739474772769815890453197344864, 170851259467202726739474772769817759486109939390⟩
  | 1, 2 => ⟨230321760923975979513955766058327604994276516141, 230321760923975979513955766058330954707983001898⟩
  | 2, 1 => ⟨232193665007229876023790205238520441024152898941, 232193665007229876023790205238526534967292601716⟩
  | 0, 4 => ⟨291827984244094284170407289562698070843195837780, 291827984244094284170407289562704446328216914549⟩
  | 1, 3 => ⟨435579442700556776123811314143470478949134751726, 435579442700556776123811314143482061340065205340⟩
  | 2, 2 => ⟨580252294828832972199612754019833999038602424804, 580252294828832972199612754019855334367615538345⟩
  | 3, 1 => ⟨584353046219758557429846616765457422172851423500, 584353046219758557429846616765497040672106859720⟩
  | 0, 5 => ⟨-1288127813126359077865851553715552139469445310615084, 1295430474874472011094762154191369970669069232863883⟩
  | 1, 4 => ⟨-2520704171189418993516644066833811790006449999244294, 2531715952749372659670349610638636782886983369463862⟩
  | 2, 3 => ⟨-4937730679365834127763524837908650377516592776669024, 4953614401352066969259858748730058771894643852230462⟩
  | 3, 2 => ⟨-9678878010731497297199866095651132900368046652755284, 9699751474667960719499181218469963055664166686587009⟩
  | 4, 1 => ⟨-18982206619654931458766845624096010885282806917926267, 19003589187393145997606259465433846734164794238658535⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0322Geometry.ds, E8TAxisProd0322Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25914717195951264327981811779143016141623785061 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0322CertifiedArithmetic

end


