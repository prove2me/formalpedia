-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0388CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0388CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:31:47.164061+00:00
-- url     : https://prove2.me/theorems/eceffef7-9424-4226-a368-abc87378ee35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0388CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0389CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0390CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0391CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0392CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0393CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0394CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0395CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0396CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0397CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0398CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0399CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0400CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0401CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0402CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0382GraphCenterA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0388GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0382GraphCenterC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0388GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0383GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0378GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0387GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0376GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0369Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0390GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0390GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0391GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0393Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0396GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0399GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0400GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0400GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0401GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0402GraphWholeB__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0388GraphCenterA.qJetBox,
   E8TAxisProd0388GraphCenterB.qJetBox,
   E8TAxisProd0388GraphCenterC.qJetBox,
   E8TAxisProd0388GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0388GraphWholeA.qJetBox,
   E8TAxisProd0388GraphWholeB.qJetBox,
   E8TAxisProd0388GraphWholeC.qJetBox,
   E8TAxisProd0388GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨61971834661933856430620249937246139682836201111, 61971834661933856430620249937246461554133932914⟩
  | 0, 2 => ⟨175218812784826886125867885186180943294996278660, 175218812784826886125867885186182266212122194125⟩
  | 1, 1 => ⟨175432272993552952856247532528986152108263492153, 175432272993552952856247532528988589489526830871⟩
  | 0, 3 => ⟨340548838210555684021573455535738764041070990345, 340548838210555684021573455535743215261778390435⟩
  | 1, 2 => ⟨454638855944906087321736303691962883154753998962, 454638855944906087321736303691971002900680549573⟩
  | 2, 1 => ⟨455127964696887020520590239834987661234837885275, 455127964696887020520590239835002638870577365391⟩
  | 0, 4 => ⟨551872990208000478699322765666647257770932253971, 551872990208000478699322765666663033904670603811⟩
  | 1, 3 => ⟨813017986549092532665923307981378696716577240755, 813017986549092532665923307981407771980636909985⟩
  | 2, 2 => ⟨1074390080202277969255825051039126410722917285451, 1074390080202277969255825051039180572371801353809⟩
  | 3, 1 => ⟨1075418177978543097986193958428311790988124575951, 1075418177978543097986193958428413403166433623922⟩
  | 0, 5 => ⟨-3137597305842636669887173290880089228560638144911460, 3152753326469706215330659671009713642270887660523404⟩
  | 1, 4 => ⟨-6164731037457259488301882414431818626519530398375416, 6187566222871042810671626138338315105702148709679796⟩
  | 2, 3 => ⟨-12123394649059075007760841385867089450955752993939922, 12156275169181681485517707129869139039142055712710406⟩
  | 3, 2 => ⟨-23856754653516971004807015532606860499787268866386210, 23899827272423163910542667153419587480715116384965458⟩
  | 4, 1 => ⟨-46970390244799703888017714274481307714983878469010123, 47014140580507507176606195183491879597426742658738972⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0388Geometry.ds, E8TAxisProd0388Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 58411178824111299665186355754570528868623687893 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0388CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0389GraphCenterA.qJetBox,
   E8TAxisProd0389GraphCenterB.qJetBox,
   E8TAxisProd0389GraphCenterC.qJetBox,
   E8TAxisProd0389GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0389GraphWholeA.qJetBox,
   E8TAxisProd0389GraphWholeB.qJetBox,
   E8TAxisProd0389GraphWholeC.qJetBox,
   E8TAxisProd0389GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨55952977442391433249529144371830306663905734814, 55952977442391433249529144371830597662115491708⟩
  | 0, 2 => ⟨159556368269392738403216686641466224948199123613, 159556368269392738403216686641467412728316118573⟩
  | 1, 1 => ⟨159752899468674386505320281250967017114584203201, 159752899468674386505320281250969200835857848360⟩
  | 0, 3 => ⟨312449098333769753688840012180582070666549352562, 312449098333769753688840012180586052144253700939⟩
  | 1, 2 => ⟨417492481527913329063356569960787567473879387057, 417492481527913329063356569960794815795282289243⟩
  | 2, 1 => ⟨417945934308114462248886531475820454025494340776, 417945934308114462248886531475833802425124118044⟩
  | 0, 4 => ⟨509439686753496513051494070852323829467615088296, 509439686753496513051494070852337868064675308312⟩
  | 1, 3 => ⟨751547978797069176621949664726417773891837874463, 751547978797069176621949664726443604436835614051⟩
  | 2, 2 => ⟨993868040424442684941407120911583657908200571507, 993868040424442684941407120911631711331763656349⟩
  | 3, 1 => ⟨994825116607896085302892149918363230613608983946, 994825116607896085302892149918453272054491604969⟩
  | 0, 5 => ⟨-2823306250286450366617774034778848247330559247235106, 2837213897015672813710228337211237984605652071914304⟩
  | 1, 4 => ⟨-5544783487826810296712681127940941826883169174576492, 5565743365232405147949969797305410758275330211851848⟩
  | 2, 3 => ⟨-10899520530339756432306771587976820373400545050270617, 10929708157600172433018562418013006929761823377843834⟩
  | 3, 2 => ⟨-21439149235229009288064215256125118085713762666568207, 21478702304593649437461953907046879649922925570623515⟩
  | 4, 1 => ⟨-42192227102928368774760430505673364704054567376267858, 42232413638251335185226876459051706813557523702087190⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0389Geometry.ds, E8TAxisProd0389Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 52712633622195064133569003873028735717411895625 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0389CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0390GraphCenterA.qJetBox,
   E8TAxisProd0390GraphCenterB.qJetBox,
   E8TAxisProd0390GraphCenterC.qJetBox,
   E8TAxisProd0390GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0390GraphWholeA.qJetBox,
   E8TAxisProd0390GraphWholeB.qJetBox,
   E8TAxisProd0390GraphWholeC.qJetBox,
   E8TAxisProd0390GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨50474199533795171327388560921382413161832803265, 50474199533795171327388560921382676361939536218⟩
  | 0, 2 => ⟨145178119837648193251220726929382114502229427520, 145178119837648193251220726929383181056622825887⟩
  | 1, 1 => ⟨145358958619863154724036006033931218083708282589, 145358958619863154724036006033933174566755677791⟩
  | 0, 3 => ⟨286479011564418944334513339729273333875001251306, 286479011564418944334513339729276895084152353064⟩
  | 1, 2 => ⟨383136508096765313734915828787830069253211657232, 383136508096765313734915828787836539026850730042⟩
  | 2, 1 => ⟨383556768586876918090238597487757207649007194147, 383556768586876918090238597487769102327395912539⟩
  | 0, 4 => ⟨470058985673669298567573832638291869762626786134, 470058985673669298567573832638304360439127415317⟩
  | 1, 3 => ⟨694445920799554650729385372714318600214604117922, 694445920799554650729385372714341543517553130926⟩
  | 2, 2 => ⟨919030352543113235753056129398968381586602027076, 919030352543113235753056129399011005448333447278⟩
  | 3, 1 => ⟨919921283936588760925457388651747893387369955341, 919921283936588760925457388651827660148933836266⟩
  | 0, 5 => ⟨-2532922110981643276357275631691574425393620285160367, 2545660553003613380956391193410468051486993616216699⟩
  | 1, 4 => ⟨-4972214957385527650712381784710111979778962469561194, 4991416505734396890753854438748034383193637653895421⟩
  | 2, 3 => ⟨-9769630697006009915362003712876389003402624496188970, 9797291043358105419179364432641144258765483384589420⟩
  | 3, 2 => ⟨-19208108605993483715062260838802605880236194400558343, 19244356041415407119723871548669337198579868880271374⟩
  | 4, 1 => ⟨-37784629087098681620400414310423459794388257865527780, 37821465057805117046967910104657066904509533394168766⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0390Geometry.ds, E8TAxisProd0390Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 47528052339113856145967417609316918034048873754 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0390CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0391GraphCenterA.qJetBox,
   E8TAxisProd0391GraphCenterB.qJetBox,
   E8TAxisProd0391GraphCenterC.qJetBox,
   E8TAxisProd0391GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0391GraphWholeA.qJetBox,
   E8TAxisProd0391GraphWholeB.qJetBox,
   E8TAxisProd0391GraphWholeC.qJetBox,
   E8TAxisProd0391GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨45491065964813596320208464655686940410736942302, 45491065964813596320208464655687178575108156133⟩
  | 0, 2 => ⟨131987372015694352180988298456499835283291676262, 131987372015694352180988298456500793084160987425⟩
  | 1, 1 => ⟨132153669511238349582177051767030240427318610697, 132153669511238349582177051767031993337353278009⟩
  | 0, 3 => ⟨262487108473975586349017145314199102970169361477, 262487108473975586349017145314202288181310435350⟩
  | 1, 2 => ⟨351373801878324503567490510927371305939985629982, 351373801878324503567490510927377080183895979154⟩
  | 2, 1 => ⟨351763164530337882340420456532302203752040650059, 351763164530337882340420456532312801431771596247⟩
  | 0, 4 => ⟨433518467032069674061780188794212331514457883755, 433518467032069674061780188794223443337683028815⟩
  | 1, 3 => ⟨641409044127482981535630912978329555372264625616, 641409044127482981535630912978349929877627330378⟩
  | 2, 2 => ⟨849483826263523920394995345470155347295832510864, 849483826263523920394995345470193145637029933697⟩
  | 3, 1 => ⟨850313157636623591431855292067034352084604621536, 850313157636623591431855292067104996738682268083⟩
  | 0, 5 => ⟨-2268155303405350744022997296834991417858022982786924, 2279828291940706537849274171894162351564773796710372⟩
  | 1, 4 => ⟨-4450351778738938823205588429772571744193673516552954, 4467952123794321082158329476217703940580948570392552⟩
  | 2, 3 => ⟨-8740185446002282150686560258447565800105337060483350, 8765546041129310200403711177843114115358484275773298⟩
  | 3, 2 => ⟨-17176165957921152107407587878743493226630885615050058, 17209408298403481635747760907425347750328878887045240⟩
  | 4, 1 => ⟨-33771886197907703662824116266323118111092134323088577, 33805683409609999334708303808293600056268411825496501⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0391Geometry.ds, E8TAxisProd0391Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 42814720216063984754119777915328854325790604688 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0391CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0392GraphCenterA.qJetBox,
   E8TAxisProd0392GraphCenterB.qJetBox,
   E8TAxisProd0392GraphCenterC.qJetBox,
   E8TAxisProd0392GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0392GraphWholeA.qJetBox,
   E8TAxisProd0392GraphWholeB.qJetBox,
   E8TAxisProd0392GraphWholeC.qJetBox,
   E8TAxisProd0392GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41868489930342889974117515565487521927854237852, 41868489930342889974117515565487740246241253379⟩
  | 0, 2 => ⟨121708039720674737092443299263057209838199182567, 121708039720674737092443299263058081522658291629⟩
  | 1, 1 => ⟨122478968455353084265877364146078607547022627422, 122478968455353084265877364146080199210078876094⟩
  | 0, 3 => ⟨243346168663514795900567987285852833605170735950, 243346168663514795900567987285855721221242652254⟩
  | 1, 2 => ⟨326487670986839901519482011401292327717616178652, 326487670986839901519482011401297551424148627434⟩
  | 2, 1 => ⟨328305211298451139820246592771598648875408992589, 328305211298451139820246592771608220231988728986⟩
  | 0, 4 => ⟨404051568432350802334541450805440024063710777473, 404051568432350802334541450805450048724350105448⟩
  | 1, 3 => ⟨599002384882565265296109644938977305058338517500, 599002384882565265296109644938995653514367591619⟩
  | 2, 2 => ⟨794818588982355730461056244180505458149553472523, 794818588982355730461056244180539450729707571285⟩
  | 3, 1 => ⟨798707405668699181150221127728355342687291673483, 798707405668699181150221127728418794586019148286⟩
  | 0, 5 => ⟨-2058453311815554739565610260387471439250415706199384, 2069295447192980682560021444320963620936070810739867⟩
  | 1, 4 => ⟨-4037109307652312463246687710787131823319432273527473, 4053469204936971507881993000139232148921598700896361⟩
  | 2, 3 => ⟨-7925195022659987518723611626710244306187989206148348, 7948793464155849821053995106600656100161861563843785⟩
  | 3, 2 => ⟨-15567903262892483683987006875700398537614217161801767, 15598896084762000146309348231503013743824437799384931⟩
  | 4, 1 => ⟨-30596610554277342421446812456585889105752309574120938, 30628301742406448319485703795990180559969250931415230⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0392Geometry.ds, E8TAxisProd0392Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39391337802740636824626808714511227172538605747 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0392CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0393GraphCenterA.qJetBox,
   E8TAxisProd0393GraphCenterB.qJetBox,
   E8TAxisProd0393GraphCenterC.qJetBox,
   E8TAxisProd0393GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0393GraphWholeA.qJetBox,
   E8TAxisProd0393GraphWholeB.qJetBox,
   E8TAxisProd0393GraphWholeC.qJetBox,
   E8TAxisProd0393GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37672847897443975714169148874996681937615853321, 37672847897443975714169148874996879673762736003⟩
  | 0, 2 => ⟨110474826838682624360274763167483013586957110659, 110474826838682624360274763167483796576909810682⟩
  | 1, 1 => ⟨111182889968879365404282275645523709630400532834, 111182889968879365404282275645525135747229723899⟩
  | 0, 3 => ⟨222660507958959126455627263871595317635539635700, 222660507958959126455627263871597900621318310333⟩
  | 1, 2 => ⟨299028886405772806983450931971581185938755665089, 299028886405772806983450931971585847852093265340⟩
  | 2, 1 => ⟨300711565405789292762069917697998009341474943907, 300711565405789292762069917698006535979014482701⟩
  | 0, 4 => ⟨372282232514079384432741760059315881942666489409, 372282232514079384432741760059324801589205723666⟩
  | 1, 3 => ⟨552771307436932061938646667186517729835734601566, 552771307436932061938646667186534025147072584084⟩
  | 2, 2 => ⟨734067688560153595335714403820262547839890281784, 734067688560153595335714403820292692638149007213⟩
  | 3, 1 => ⟨737687388804772923687879142960775881648442964338, 737687388804772923687879142960832076106111856894⟩
  | 0, 5 => ⟨-1837096381631313821243761536122862469044788493285515, 1846981475150235449338018877352124792077909045620285⟩
  | 1, 4 => ⟨-3601120854660979372640031865867581395142445277228554, 3616040660371531364634762723191168968562876497937326⟩
  | 2, 3 => ⟨-7065767489919566923927414374380877587532113598763282, 7087295076744475813991212414464316435655935443185250⟩
  | 3, 2 => ⟨-13872776211979193604657799429046365339177347591246941, 13901057466941809082047402116900852423251895509163381⟩
  | 4, 1 => ⟨-27251478020623774546266068243572552840449147862560269, 27280406395624212777032421100686878291404400990163801⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0393Geometry.ds, E8TAxisProd0393Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35426121138057946856620995711300593347190946595 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0393CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0394GraphCenterA.qJetBox,
   E8TAxisProd0394GraphCenterB.qJetBox,
   E8TAxisProd0394GraphCenterC.qJetBox,
   E8TAxisProd0394GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0394GraphWholeA.qJetBox,
   E8TAxisProd0394GraphWholeB.qJetBox,
   E8TAxisProd0394GraphWholeC.qJetBox,
   E8TAxisProd0394GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41716544863419501041180862033047481995896879342, 41716544863419501041180862033047699860663043727⟩
  | 0, 2 => ⟨121404172481903370978824960804059292036809149005, 121404172481903370978824960804060161801981314821⟩
  | 1, 1 => ⟨122071326538625113755687524071064885294343721804, 122071326538625113755687524071066473416992715575⟩
  | 0, 3 => ⟨242841567889662200775759968147673574914972623627, 242841567889662200775759968147676456030565565201⟩
  | 1, 2 => ⟨325739634560749029920611845143034614979293465893, 325739634560749029920611845143039826822513640514⟩
  | 2, 1 => ⟨327312730197110689063790703590280037361931290585, 327312730197110689063790703590289586807762698430⟩
  | 0, 4 => ⟨403309877242256873569310735916072699657302780582, 403309877242256873569310735916082700694050642443⟩
  | 1, 3 => ⟨597856227215623718158247288511746435876828459170, 597856227215623718158247288511764740908684936291⟩
  | 2, 2 => ⟨793151673070131524029128314820557689809574180890, 793151673070131524029128314820591601576730787506⟩
  | 3, 1 => ⟨796517779467485074120571583189738514834189838138, 796517779467485074120571583189801815143138528165⟩
  | 0, 5 => ⟨-2053784429545611540112151079382815249689320323543465, 2064603872385508379364858559332980626195226824083620⟩
  | 1, 4 => ⟨-4027923290533572175322397657713240724632109209059516, 4044248027422618018864596278323596857571583761287348⟩
  | 2, 3 => ⟨-7907102622342494538271870502205540204103527848752981, 7930647820029858243951944427507658191050009489744059⟩
  | 3, 2 => ⟨-15532243179734980559182100916649638080672215018576738, 15563158461562686392475080980734028654196172209599340⟩
  | 4, 1 => ⟨-30526284594998248109135517385208510568392422249336330, 30557871301819731638515183197872594160115790975828324⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0394Geometry.ds, E8TAxisProd0394Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39247406587165953662718975514047261898795631227 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0394CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0395GraphCenterA.qJetBox,
   E8TAxisProd0395GraphCenterB.qJetBox,
   E8TAxisProd0395GraphCenterC.qJetBox,
   E8TAxisProd0395GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0395GraphWholeA.qJetBox,
   E8TAxisProd0395GraphWholeB.qJetBox,
   E8TAxisProd0395GraphWholeC.qJetBox,
   E8TAxisProd0395GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37534928196287758203580496570949838133520795264, 37534928196287758203580496570950035459467584063⟩
  | 0, 2 => ⟨110196791870313862687173992326414683254758191951, 110196791870313862687173992326415464518589321424⟩
  | 1, 1 => ⟨110809535436519169634433807843084974093766879392, 110809535436519169634433807843086397032318118344⟩
  | 0, 3 => ⟨222195584502223250773930755367973315548228929830, 222195584502223250773930755367975892717488792356⟩
  | 1, 2 => ⟨298338586824113473749204671740437886072697160431, 298338586824113473749204671740442537390608537985⟩
  | 2, 1 => ⟨299794948397097284882030459116053958431218311673, 299794948397097284882030459116062465528200564117⟩
  | 0, 4 => ⟨371595490898274903318279963378162495265219154454, 371595490898274903318279963378171393938052421178⟩
  | 1, 3 => ⟨551708330236364903252789051486767435537872953036, 551708330236364903252789051486783692364692849535⟩
  | 2, 2 => ⟨732519990263833486147731837960153296777559194628, 732519990263833486147731837960183370051726360447⟩
  | 3, 1 => ⟨735653150999732042429404958894154206541828289284, 735653150999732042429404958894210266992632734937⟩
  | 0, 5 => ⟨-1832819362809872237267764191377491860823011027479264, 1842683114895292439623452486757237367505622533893141⟩
  | 1, 4 => ⟨-3592708740476569336622369152488784949216059027754047, 3607595497152709554984629887098408813171654080147780⟩
  | 2, 3 => ⟨-7049205087178916242793636460957580586634471455367065, 7070682776071169712330051979117551901970372630431175⟩
  | 3, 2 => ⟨-13840143148734690129702110121833004885042207367944266, 13868352278319642395837694332588872761817162090616577⟩
  | 4, 1 => ⟨-27187144347267176268731385411971008962384091296007337, 27215977204104201870891302356979572951149053808676887⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0395Geometry.ds, E8TAxisProd0395Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35295542026367478820896205338302258224676839571 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0395CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0396GraphCenterA.qJetBox,
   E8TAxisProd0396GraphCenterB.qJetBox,
   E8TAxisProd0396GraphCenterC.qJetBox,
   E8TAxisProd0396GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0396GraphWholeA.qJetBox,
   E8TAxisProd0396GraphWholeB.qJetBox,
   E8TAxisProd0396GraphWholeC.qJetBox,
   E8TAxisProd0396GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33865803497635098743738558175642709392903260709, 33865803497635098743738558175642888577492956026⟩
  | 0, 2 => ⟨100190129494215818919509605296276703258639195034, 100190129494215818919509605296277406665082848225⟩
  | 1, 1 => ⟨100840003865165789100114989775071095090734477309, 100840003865165789100114989775072372895588032829⟩
  | 0, 3 => ⟨203576090593173766801801976555444321067852415127, 203576090593173766801801976555446631640433481472⟩
  | 1, 2 => ⟨273674878359835547437411966055200895278835324675, 273674878359835547437411966055205055618945024049⟩
  | 2, 1 => ⟨275232031400626989303817094093494160051359026137, 275232031400626989303817094093501755304340112614⟩
  | 0, 4 => ⟨342821529621427599579529230125161261137542096067, 342821529621427599579529230125169198028827380805⟩
  | 1, 3 => ⟨509849905973448346906068007404297704466676470745, 509849905973448346906068007404312176294904236675⟩
  | 2, 2 => ⟨677631477448640437622691028456333227626640891620, 677631477448640437622691028456359959171173575518⟩
  | 3, 1 => ⟨681000539168779809543683967337288863362910824604, 681000539168779809543683967337338627394165862102⟩
  | 0, 5 => ⟨-1634040657915054070908983945928476749928620489140620, 1643004749435119624400007459993570468174393370978098⟩
  | 1, 4 => ⟨-3201345249389857158831450296187695625062570056484413, 3214874958031740299120820571654171536425582316638960⟩
  | 2, 3 => ⟨-6278057762590856151141154497606154876326126800258063, 6297581338536259508396455607032772786875957426422454⟩
  | 3, 2 => ⟨-12319776853955805423435321192123544044006400867162915, 12345428859505632877069077386451362363206978435556240⟩
  | 4, 1 => ⟨-24188168781224107937423318266056324873947310228869956, 24214411896511159988194781024992268961492995057523451⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0396Geometry.ds, E8TAxisProd0396Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31830098995985740645279825643680818957505010416 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0396CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0397GraphCenterA.qJetBox,
   E8TAxisProd0397GraphCenterB.qJetBox,
   E8TAxisProd0397GraphCenterC.qJetBox,
   E8TAxisProd0397GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0397GraphWholeA.qJetBox,
   E8TAxisProd0397GraphWholeB.qJetBox,
   E8TAxisProd0397GraphWholeC.qJetBox,
   E8TAxisProd0397GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30414433646258019590503084910200637108721456517, 30414433646258019590503084910200799567512795161⟩
  | 0, 2 => ⟨90781027876053122580931553556565874189582891972, 90781027876053122580931553556566506645713653476⟩
  | 1, 1 => ⟨91377066493349850821349482163162566648051977022, 91377066493349850821349482163163712504662262173⟩
  | 0, 3 => ⟨185978166439531677201526696786274371967705590185, 185978166439531677201526696786276442998221787967⟩
  | 1, 2 => ⟨250276033412957835257279696769179726428234410168, 250276033412957835257279696769183446824484411526⟩
  | 2, 1 => ⟨251716355259275827168145328323958481780468367188, 251716355259275827168145328323965261886836520295⟩
  | 0, 4 => ⟨315507646930246310346322082771281725014182710749, 315507646930246310346322082771288813408151559049⟩
  | 1, 3 => ⟨470007676592987040253880199247784539388061856401, 470007676592987040253880199247797440688826810753⟩
  | 2, 2 => ⟨625210476293570558300920633736346990216215117975, 625210476293570558300920633736370787846779609212⟩
  | 3, 1 => ⟨628346085567084882048323852776150165992605884646, 628346085567084882048323852776194412124637754209⟩
  | 0, 5 => ⟨-1447907175745735763211255658008365234563610387512543, 1455990416871663226069063843090799617886937741959789⟩
  | 1, 4 => ⟨-2835031365006014811263074174115943280188805802809167, 2847228148712301314436689712729104557218791132335912⟩
  | 2, 3 => ⟨-5556572226844705607624453897427997386747464070447715, 5574170181620889448330535769614958507437166751197708⟩
  | 3, 2 => ⟨-10897928122553248586433458045378912852885011216535562, 10921049733854057172913757486914025968435165187637666⟩
  | 4, 1 => ⟨-21384737401641419045684660311312801972480311857210387, 21408391876315401920086699007049079592020469875167421⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0397Geometry.ds, E8TAxisProd0397Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28571838285236569738661681193913066880411017261 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0397CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0398GraphCenterA.qJetBox,
   E8TAxisProd0398GraphCenterB.qJetBox,
   E8TAxisProd0398GraphCenterC.qJetBox,
   E8TAxisProd0398GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0398GraphWholeA.qJetBox,
   E8TAxisProd0398GraphWholeB.qJetBox,
   E8TAxisProd0398GraphWholeC.qJetBox,
   E8TAxisProd0398GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33740724768044312683961803752021142838515207302, 33740724768044312683961803752021321652038411178⟩
  | 0, 2 => ⟨99935927044683366804008081277357089530018658127, 99935927044683366804008081277357791383920630355⟩
  | 1, 1 => ⟨100498308330670874415274728631687454907843463483, 100498308330670874415274728631688729859472936157⟩
  | 0, 3 => ⟨203147961091674168135261988574658738197987355761, 203147961091674168135261988574661043558016564297⟩
  | 1, 2 => ⟨273038182170192895635227215504888537602524908032, 273038182170192895635227215504892688464209450785⟩
  | 2, 1 => ⟨274385890312442859705178668440990034927696253601, 274385890312442859705178668440997612723837966242⟩
  | 0, 4 => ⟨342185851555623097015353320817678284539719661423, 342185851555623097015353320817686202717274424888⟩
  | 1, 3 => ⟨508864282735198198313573877024701504780994092628, 508864282735198198313573877024715942323376017421⟩
  | 2, 2 => ⟨676194695974411492324961904548955080950541625731, 676194695974411492324961904548981748845179505812⟩
  | 3, 1 => ⟨679110905143459450293518378433326193364962834641, 679110905143459450293518378433375838259705575985⟩
  | 0, 5 => ⟨-1630122059612989816884110707047132344516187117204892, 1639066229150377618590950214791077929211859729322187⟩
  | 1, 4 => ⟨-3193640484813047954647452258965034042390267302648059, 3207139423658435909367032765720575380825004220463509⟩
  | 2, 3 => ⟨-6262892805455067286118233719258172327676836691297549, 6282370189265288481133433180643714150732161380821560⟩
  | 3, 2 => ⟨-12289906671839230648302644688468165224530161458360319, 12315492674134446965560244767080035897496307920238974⟩
  | 4, 1 => ⟨-24129300833030698456796020132318720290608443882836391, 24155458692103327251073204376634475576928649086242277⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0398Geometry.ds, E8TAxisProd0398Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31711739445769970372381374814226469510765771346 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0398CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0399GraphCenterA.qJetBox,
   E8TAxisProd0399GraphCenterB.qJetBox,
   E8TAxisProd0399GraphCenterC.qJetBox,
   E8TAxisProd0399GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0399GraphWholeA.qJetBox,
   E8TAxisProd0399GraphWholeB.qJetBox,
   E8TAxisProd0399GraphWholeC.qJetBox,
   E8TAxisProd0399GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30301102554199066807720542469836538778005174011, 30301102554199066807720542469836700901008662308⟩
  | 0, 2 => ⟨90548801505102192734147819209483892161034318747, 90548801505102192734147819209484523228149662736⟩
  | 1, 1 => ⟨91064588407036224313621596890990814470701100557, 91064588407036224313621596890991957780940965374⟩
  | 0, 3 => ⟨185584149630655523766986314318586226710600810898, 185584149630655523766986314318588293138540404602⟩
  | 1, 2 => ⟨249689095041820086640764883368448285323507893364, 249689095041820086640764883368451997373934591741⟩
  | 2, 1 => ⟨250935675909589453341358122864372303554603657419, 250935675909589453341358122864379068323574566935⟩
  | 0, 4 => ⟨314919413146889626421474211414646243484709386797, 314919413146889626421474211414653315626749023001⟩
  | 1, 3 => ⟨469093982267253943001772413315316996040062785004, 469093982267253943001772413315329867651124718352⟩
  | 2, 2 => ⟨623876885198160898598594727849781030278747172133, 623876885198160898598594727849804772907105290023⟩
  | 3, 1 => ⟨626591018557828899432543069506796462579793044510, 626591018557828899432543069506840605936728454964⟩
  | 0, 5 => ⟨-1444331768506872524261790072286531657627282165179915, 1452396563857480320422015690035668480442581201861759⟩
  | 1, 4 => ⟨-2828003812957539366171145806934045563606589717750924, 2840172217039087837175424650885046251019155305450156⟩
  | 2, 3 => ⟨-5542744964873801450715072963977387706917423562858600, 5560300630774833510194605786045573426105299172888115⟩
  | 3, 2 => ⟨-10870702204438204365167988234883811972862277571244909, 10893764251253002485174797157578549048196059161754834⟩
  | 4, 1 => ⟨-21331099464589293595763078322616251643796245770874201, 21354679379820775097506581021270573559525821717165692⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0399Geometry.ds, E8TAxisProd0399Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28464651953404350754511834242649366269651980170 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0399CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0400GraphCenterA.qJetBox,
   E8TAxisProd0400GraphCenterB.qJetBox,
   E8TAxisProd0400GraphCenterC.qJetBox,
   E8TAxisProd0400GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0400GraphWholeA.qJetBox,
   E8TAxisProd0400GraphWholeB.qJetBox,
   E8TAxisProd0400GraphWholeC.qJetBox,
   E8TAxisProd0400GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41564979236566556385852502380925618563438135437, 41564979236566556385852502380925835975520307406⟩
  | 0, 2 => ⟨121100935414977187456083083838523028904411284187, 121100935414977187456083083838523896754431418699⟩
  | 1, 1 => ⟨121664618772510046529629545505763048973504437606, 121664618772510046529629545505764633563403835849⟩
  | 0, 3 => ⟨242337893452036128706671322888814354447128889880, 242337893452036128706671322888817229076654571969⟩
  | 1, 2 => ⟨324993029593588418389640129023013790411773818997, 324993029593588418389640129023018990418049953148⟩
  | 2, 1 => ⟨326322330867056655579425588565816315576638170103, 326322330867056655579425588565825843160524346365⟩
  | 0, 4 => ⟨402569430147512119829635756357944507923447483379, 402569430147512119829635756357954485390801516320⟩
  | 1, 3 => ⟨596712050058658749442629350631134832918012234831, 596712050058658749442629350631153094625943070632⟩
  | 2, 2 => ⟨791487754084142833837434427262503605853069210348, 791487754084142833837434427262537436993869441281⟩
  | 3, 1 => ⟨794332447533635294566001587474035801390242941390, 794332447533635294566001587474098950459742251618⟩
  | 0, 5 => ⟨-2049123554208154759378299972549184749072666368522136, 2059920339644187829125330171723091432562072134898099⟩
  | 1, 4 => ⟨-4018753035821686809702945906046999829333824167105737, 4035042669170204080402838994281895959358535237398230⟩
  | 2, 3 => ⟨-7889041295054690208850177530622875173269779739886873, 7912533342285790314434636810795825689543867196745785⟩
  | 3, 2 => ⟨-15496644409569332187262864850919463933948597466979303, 15527482308361800848460456604378867842904359464711515⟩
  | 4, 1 => ⟨-30456079701953081365219945561672623974694152173189226, 30487562199889844075725056775408163128963100967409848⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0400Geometry.ds, E8TAxisProd0400Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39103836710287527378085691202175757602165857690 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0400CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0401GraphCenterA.qJetBox,
   E8TAxisProd0401GraphCenterB.qJetBox,
   E8TAxisProd0401GraphCenterC.qJetBox,
   E8TAxisProd0401GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0401GraphWholeA.qJetBox,
   E8TAxisProd0401GraphWholeB.qJetBox,
   E8TAxisProd0401GraphWholeC.qJetBox,
   E8TAxisProd0401GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37397355675844005742534836712395397203803713236, 37397355675844005742534836712395594120396594167⟩
  | 0, 2 => ⟨109919337520050008312991350977834195138902766617, 109919337520050008312991350977834974680333892809⟩
  | 1, 1 => ⟨110437042948664631312071240756496068314102428704, 110437042948664631312071240756497488081258847900⟩
  | 0, 3 => ⟨221731518750501439813898516333843884159993945442, 221731518750501439813898516333846455525625354116⟩
  | 1, 2 => ⟨297649614813259856180821822005680765984159524740, 297649614813259856180821822005685406730191754120⟩
  | 2, 1 => ⟨298880264268816405071243697782756068278275189362, 298880264268816405071243697782764555878228014850⟩
  | 0, 4 => ⟨370909904191352280093419436853300147567127461955, 370909904191352280093419436853309025314493918120⟩
  | 1, 3 => ⟨550647193648839559581809686627518627139862169927, 550647193648839559581809686627534845570735395053⟩
  | 2, 2 => ⟨730975079119689041962472570921181757525537210782, 730975079119689041962472570921211759440284297509⟩
  | 3, 1 => ⟨733622908574299054539378126233230363418367557701, 733622908574299054539378126233286290171028598243⟩
  | 0, 5 => ⟨-1828549944061487441633952564750653429904364048923879, 1838392392449375333937344379184383826874529853238914⟩
  | 1, 4 => ⟨-3584311586234801481101922676282798862685405392001587, 3599165356797213058133214888505010818059138278866010⟩
  | 2, 3 => ⟨-7032672171789429814719370559795200917756455910595647, 7054100069193532384139457799548212852008256678710427⟩
  | 3, 2 => ⟨-13807568261417706057205147287906880177017703038647916, 13835705449483775925791551208004925108339739661479819⟩
  | 4, 1 => ⟨-27122925528636457584318906897127634301612988240428255, 27151663192787971568891697952316793674113438743637150⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0401Geometry.ds, E8TAxisProd0401Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35165293374850716964157885242813406640005461694 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0401CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0402GraphCenterA.qJetBox,
   E8TAxisProd0402GraphCenterB.qJetBox,
   E8TAxisProd0402GraphCenterC.qJetBox,
   E8TAxisProd0402GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0402GraphWholeA.qJetBox,
   E8TAxisProd0402GraphWholeB.qJetBox,
   E8TAxisProd0402GraphWholeC.qJetBox,
   E8TAxisProd0402GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41413792262792544885289401793241668578590891899, 41413792262792544885289401793241885538923980618⟩
  | 0, 2 => ⟨120798327362947349283205782510828940744578842749, 120798327362947349283205782510829806683572996168⟩
  | 1, 1 => ⟨121258843369230656789230624534555931486730213607, 121258843369230656789230624534557512551521285166⟩
  | 0, 3 => ⟨241835143796725842958071951143876794358442434209, 241835143796725842958071951143879662516280768250⟩
  | 1, 2 => ⟨324247853611727689525661557967932203776962705633, 324247853611727689525661557967937391972604936984⟩
  | 2, 1 => ⟨325334009565279399865947261095965279564769018025, 325334009565279399865947261095974785335405741374⟩
  | 0, 4 => ⟨401830225215042452541940081798783267251395568644, 401830225215042452541940081798793221203728954526⟩
  | 1, 3 => ⟨595569850201117397904195616406655482644334282266, 595569850201117397904195616406673701128357894059⟩
  | 2, 2 => ⟨789826826988653335566389753961637595690793103271, 789826826988653335566389753961671346391453414403⟩
  | 3, 1 => ⟨792151402315430958619554946108599100372921914628, 792151402315430958619554946108662098552505751029⟩
  | 0, 5 => ⟨-2044470676448158515443875825004174926689060287711421, 2055244840178950316256483718787513951286458091239021⟩
  | 1, 4 => ⟨-4009598526298333098289204111436133191944784320250471, 4025853113492862101176859356263707806218730860617170⟩
  | 2, 3 => ⟨-7871011008457995258457588052814067219615330276662883, 7894449999093357202314145807825390710287103914714461⟩
  | 3, 2 => ⟨-15461106890610900604667890206594822679861205931144906, 15491867563903024887409117335721095728577643096862629⟩
  | 4, 1 => ⟨-30385995755363493761448173387631448481618941952352299, 30417374317465556607109938854715091090753823099444286⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0402Geometry.ds, E8TAxisProd0402Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38960627419156824217662628423786291702150496492 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0402CertifiedArithmetic

end


