-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0323CertifiedArithmetic__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0323CertifiedArithmetic__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:49:59.735232+00:00
-- url     : https://prove2.me/theorems/ed4f5a4c-0fe4-4935-bf51-f9d6285dabe2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0323CertifiedArithmetic (+11 modules: GeneralCK/Certificates/E8TAxisProd0324CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0325CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0326CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0327CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0328CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0329CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0330CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0331CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0332CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0333CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0334CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0315GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0314GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0318GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0318GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0315GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0314GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0317GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0320GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0321Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0324GraphCenterA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0324GraphWholeB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0324GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0325GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0325GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0328GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0328GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0330GraphCenterD__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0331GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphWholeB__10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0323GraphCenterA.qJetBox,
   E8TAxisProd0323GraphCenterB.qJetBox,
   E8TAxisProd0323GraphCenterC.qJetBox,
   E8TAxisProd0323GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0323GraphWholeA.qJetBox,
   E8TAxisProd0323GraphWholeB.qJetBox,
   E8TAxisProd0323GraphWholeC.qJetBox,
   E8TAxisProd0323GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24739335960109952622905374901202202375602082380, 24739335960109952622905374901202336972588281247⟩
  | 0, 2 => ⟨74905974330312327410526444889291087083018898780, 74905974330312327410526444889291602059733078204⟩
  | 1, 1 => ⟨75609548472626163379754125947453379257201745209, 75609548472626163379754125947454307063937947131⟩
  | 0, 3 => ⟨155825274594776556823887163683337553814064100720, 155825274594776556823887163683339229345291113732⟩
  | 1, 2 => ⟨210296190609060586609797005530222306242642185177, 210296190609060586609797005530225301699047986848⟩
  | 2, 1 => ⟨212025900493824685345840170536670762400964078136, 212025900493824685345840170536676201807973363201⟩
  | 0, 4 => ⟨268243130814889467807843812776775188322386050464, 268243130814889467807843812776780882713004693581⟩
  | 1, 3 => ⟨401079879353605359461479432758395063736943834815, 401079879353605359461479432758405388657219938840⟩
  | 2, 2 => ⟨534776429592724910509207113583952474375508954841, 534776429592724910509207113583971465799634965781⟩
  | 3, 1 => ⟨538592443439046374482001807142162276350944532568, 538592443439046374482001807142197495983166821576⟩
  | 0, 5 => ⟨-1137046805593860047430134495461648271408237913151573, 1143562139218698979985395451082879282118577894272982⟩
  | 1, 4 => ⟨-2223664764425539048023998824084604154586443937144389, 2233477154999003246518525427731894523135450000458745⟩
  | 2, 3 => ⟨-4353252500188827359873931233243131569901616955317126, 4367394105294354042823575441293693971440712300111720⟩
  | 3, 2 => ⟨-8528144573912548881131924291452511404185912329455801, 8546719188793938363425174716450362260663637022456260⟩
  | 4, 1 => ⟨-16715524462528853970572003476971475710567825764839072, 16734547289121543835166787387853131747514019366794632⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0323Geometry.ds, E8TAxisProd0323Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23218718886433076389837398695080418979513100840 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0323CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0324GraphCenterA.qJetBox,
   E8TAxisProd0324GraphCenterB.qJetBox,
   E8TAxisProd0324GraphCenterC.qJetBox,
   E8TAxisProd0324GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0324GraphWholeA.qJetBox,
   E8TAxisProd0324GraphWholeB.qJetBox,
   E8TAxisProd0324GraphWholeC.qJetBox,
   E8TAxisProd0324GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22239668310461948280104584786165932970614578404, 22239668310461948280104584786166055464314576198⟩
  | 0, 2 => ⟨67862215397811934621351373347667184961620660571, 67862215397811934621351373347667649271082906589⟩
  | 1, 1 => ⟨68568444986638659764170329441009586011530070862, 68568444986638659764170329441010420026547919297⟩
  | 0, 3 => ⟨142302069423410705463344869113015672981903523354, 142302069423410705463344869113017178446743388579⟩
  | 1, 2 => ⟨192307514155555174434837469380647015848192421846, 192307514155555174434837469380649700361102000513⟩
  | 2, 1 => ⟨194059476772289550039137900155219994699945478342, 194059476772289550039137900155224860324024427287⟩
  | 0, 4 => ⟨246861182152963010440516930914385373045621880368, 246861182152963010440516930914390470419063159859⟩
  | 1, 3 => ⟨369805122143109323544489925049064832156323844623, 369805122143109323544489925049074055879805167140⟩
  | 2, 2 => ⟨493628873392441961303275453658603444828169655189, 493628873392441961303275453658620385518430521563⟩
  | 3, 1 => ⟨497522557987440827745383148029704588470869194815, 497522557987440827745383148029735963077013571827⟩
  | 0, 5 => ⟨-1008400378486140211346820266515485392757944166946432, 1014209767941944971634213333605258445439422749512727⟩
  | 1, 4 => ⟨-1970874148001280222910521376030104598435038409658303, 1979610664349101990493605778077637996419135776929340⟩
  | 2, 3 => ⟨-3856103775303168068145574777062097341258970691578482, 3868681961607791720403151851088935445938948926272672⟩
  | 3, 2 => ⟨-7549846158460404940290398029076773930637179886701837, 7566357241397016183586983899909739264377107577440793⟩
  | 4, 1 => ⟨-14789457788960320331513362820786537580263821788496142, 14806364207887848048345405326192108167390103979690209⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0324Geometry.ds, E8TAxisProd0324Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20862106356122081994539108797984684597950566539 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0324CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0325GraphCenterA.qJetBox,
   E8TAxisProd0325GraphCenterB.qJetBox,
   E8TAxisProd0325GraphCenterC.qJetBox,
   E8TAxisProd0325GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0325GraphWholeA.qJetBox,
   E8TAxisProd0325GraphWholeB.qJetBox,
   E8TAxisProd0325GraphWholeC.qJetBox,
   E8TAxisProd0325GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19897033665890215378159861265095613263754431703, 19897033665890215378159861265095724584933129891⟩
  | 0, 2 => ⟨61261315476259129676304825733245993533925318548, 61261315476259129676304825733246411330354802706⟩
  | 1, 1 => ⟨61907038843627130500178799803127437340440243899, 61907038843627130500178799803128185424097365593⟩
  | 0, 3 => ⟨129553320157636182379724544152349623043252995702, 129553320157636182379724544152350972747202600840⟩
  | 1, 2 => ⟨175282094438367128202250480277491418899353672118, 175282094438367128202250480277493819146302173813⟩
  | 2, 1 => ⟨176899059358610341001462819224519781428242623068, 176899059358610341001462819224524123311840358252⟩
  | 0, 4 => ⟨226588117026555085571300265983775301279933333326, 226588117026555085571300265983779853330794769351⟩
  | 1, 3 => ⟨340063989424635640376367723958453005974148456027, 340063989424635640376367723958461225340055798222⟩
  | 2, 2 => ⟨454360856368609414812644070308868250953581364104, 454360856368609414812644070308883323539834878929⟩
  | 3, 1 => ⟨457983249977991000120765216472201531225923182636, 457983249977991000120765216472229407319257872803⟩
  | 0, 5 => ⟨-890723594074293013756776267945590695769205933179261, 895890220949726052233691739005395218158283328597745⟩
  | 1, 4 => ⟨-1739754306275080472678464726492769006376819932741256, 1747512397697889654675821177000713324964850685800853⟩
  | 2, 3 => ⟨-3401794030872086764984148920045373751410061268715736, 3412951369792007017770305164167455575360072707478098⟩
  | 3, 2 => ⟨-6656275639825876797350807228579260595676132929645388, 6670910813478450629976429704180127900796325666222849⟩
  | 4, 1 => ⟨-13031045319866701635289611282161675180827507579545557, 13046021745865051548018252853974092426611199931805771⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0325Geometry.ds, E8TAxisProd0325Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18654502854026591402128364390488824969775912311 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0325CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0326GraphCenterA.qJetBox,
   E8TAxisProd0326GraphCenterB.qJetBox,
   E8TAxisProd0326GraphCenterC.qJetBox,
   E8TAxisProd0326GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0326GraphWholeA.qJetBox,
   E8TAxisProd0326GraphWholeB.qJetBox,
   E8TAxisProd0326GraphWholeC.qJetBox,
   E8TAxisProd0326GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22154951634386098838231046630386654269794242942, 22154951634386098838231046630386776512202947207⟩
  | 0, 2 => ⟨67684530549305893453878984190925522681423478926, 67684530549305893453878984190925985968954809264⟩
  | 1, 1 => ⟨68328349313507209808418856461121314222083122416, 68328349313507209808418856461122146374930131016⟩
  | 0, 3 => ⟨141993785764904934702809533446134627184802811267, 141993785764904934702809533446136129290069975910⟩
  | 1, 2 => ⟨191845715338887662409848996909952891245569410945, 191845715338887662409848996909955569698533304199⟩
  | 2, 1 => ⟨193443111472703532454193864699534308731488479729, 193443111472703532454193864699539163262213534875⟩
  | 0, 4 => ⟨246392804613059771529725699317059010460584221724, 246392804613059771529725699317064096072818303147⟩
  | 1, 3 => ⟨369073198318136760058120143502787171965535361981, 369073198318136760058120143502796374294344599630⟩
  | 2, 2 => ⟨492555931278909680307075087573718516759919502664, 492555931278909680307075087573735417933927089334⟩
  | 3, 1 => ⟨496106573950617029809145860638403428461999648927, 496106573950617029809145860638434729426527285964⟩
  | 0, 5 => ⟨-1005909733838243476287588228717600612120372456615277, 1011705631144724748856230744045725847810262212015922⟩
  | 1, 4 => ⟨-1965985820889305461477099899021984558124451399767030, 1974701738058921993202702423653994233155968695183079⟩
  | 2, 3 => ⟨-3846498549194402218127495301098261280656460990731211, 3859046606052464795126120860086391254755546939565970⟩
  | 3, 2 => ⟨-7530957725946853753753772039742871999285350258957872, 7547428010233082752537801237980162792068316818649675⟩
  | 4, 1 => ⟨-14752291885633948694392513782146363774881307462801761, 14769151951865178368658269881499843948998764941283607⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0326Geometry.ds, E8TAxisProd0326Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20782094569593140349697670678557179926777448210 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0326CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0327GraphCenterA.qJetBox,
   E8TAxisProd0327GraphCenterB.qJetBox,
   E8TAxisProd0327GraphCenterC.qJetBox,
   E8TAxisProd0327GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0327GraphWholeA.qJetBox,
   E8TAxisProd0327GraphWholeB.qJetBox,
   E8TAxisProd0327GraphWholeC.qJetBox,
   E8TAxisProd0327GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19820558161352353665936983166848822578991437779, 19820558161352353665936983166848933672415863563⟩
  | 0, 2 => ⟨61099550735264640189316155630414466285051163689, 61099550735264640189316155630414883161150359093⟩
  | 1, 1 => ⟨61688201723984179240809156286662931272286141267, 61688201723984179240809156286663677682793108122⟩
  | 0, 3 => ⟨129270355606059225338686300840708451345687294386, 129270355606059225338686300840709798032576248517⟩
  | 1, 2 => ⟨174857438197678512328342956685532507867581554787, 174857438197678512328342956685534902683278325443⟩
  | 2, 1 => ⟨176331730387064387529303292616778823210184194926, 176331730387064387529303292616783155165625783685⟩
  | 0, 4 => ⟨226155288948368295085976508797537335562711607328, 226155288948368295085976508797541877083077769365⟩
  | 1, 3 => ⟨339386194238708199778218239288408722403653060656, 339386194238708199778218239288416922644710447993⟩
  | 2, 2 => ⟨453365800630864028086107767686857266491283251032, 453365800630864028086107767686872303792951874325⟩
  | 3, 1 => ⟨456669044193284279682027127665484744022589240346, 456669044193284279682027127665512554423862107621⟩
  | 0, 5 => ⟨-888457938381466916165420170518417670127318607805076, 893612583909657806736630904846602033972387266906179⟩
  | 1, 4 => ⟨-1735309353836647052486057017912878292832679732028933, 1743049224222572405042775516673099317941685859776680⟩
  | 2, 3 => ⟨-3393063512422052533090506429369377461615322528872524, 3404194343769280512226215835563888530720154993960300⟩
  | 3, 2 => ⟨-6639114230283506753795747804056639085434966493881975, 6653713827374158928535378817744040562112068181467743⟩
  | 4, 1 => ⟨-12997291387580440784582185857556470322501453138791247, 13012228216217403850041696686499027856510512324479716⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0327Geometry.ds, E8TAxisProd0327Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18582315929646713860570835124385978578852741405 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0327CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0328GraphCenterA.qJetBox,
   E8TAxisProd0328GraphCenterB.qJetBox,
   E8TAxisProd0328GraphCenterC.qJetBox,
   E8TAxisProd0328GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0328GraphWholeA.qJetBox,
   E8TAxisProd0328GraphWholeB.qJetBox,
   E8TAxisProd0328GraphWholeC.qJetBox,
   E8TAxisProd0328GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27494333442451948378825769672697344145528573118, 27494333442451948378825769672697492130218170758⟩
  | 0, 2 => ⟨82605098000172639231873770707356017328111921239, 82605098000172639231873770707356588610654236032⟩
  | 1, 1 => ⟨83299132100896852974164321640962224038334785118, 83299132100896852974164321640963256247382514447⟩
  | 0, 3 => ⟨170486816417739354559767003836545310793969071115, 170486816417739354559767003836547175666824363002⟩
  | 1, 2 => ⟨229777818810570868451266045725668612645343409263, 229777818810570868451266045725671954828940972346⟩
  | 2, 1 => ⟨231469127581988036337471909185986561246227648015, 231469127581988036337471909185992641369138791242⟩
  | 0, 4 => ⟨291281049492769680917549060901908139700516497340, 291281049492769680917549060901914500536673454701⟩
  | 1, 3 => ⟨434728186162085543969734307035994946662053414658, 434728186162085543969734307036006502330662960074⟩
  | 2, 2 => ⟨579007961229597400738760629773816837718606566642, 579007961229597400738760629773838123593772715268⟩
  | 3, 1 => ⟨582713524560598942386084060992298752172365294383, 582713524560598942386084060992338278347755610915⟩
  | 0, 5 => ⟨-1284867820917719400472947400065154134912057322663670, 1292153654725921052111012737807397595334514611848499⟩
  | 1, 4 => ⟨-2514299262187982981557866208237004402188939911412224, 2525285128477917611159345862971826205029879576716320⟩
  | 2, 3 => ⟨-4925133652843079397985163684747246570828090946334827, 4940978928306721584859533554997501330194528041314680⟩
  | 3, 2 => ⟨-9654084442106407077330958255726609217976866739374676, 9674904429321799484010378639237990916736132805299841⟩
  | 4, 1 => ⟨-18933380393385028932321518891947649027648202084527777, 18954698088049176416999878008883409446391503895565534⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0328Geometry.ds, E8TAxisProd0328Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25816980652218537656178671035561904438501921564 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0328CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0329GraphCenterA.qJetBox,
   E8TAxisProd0329GraphCenterB.qJetBox,
   E8TAxisProd0329GraphCenterC.qJetBox,
   E8TAxisProd0329GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0329GraphWholeA.qJetBox,
   E8TAxisProd0329GraphWholeB.qJetBox,
   E8TAxisProd0329GraphWholeC.qJetBox,
   E8TAxisProd0329GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24645825143415294412885350285826280885239774527, 24645825143415294412885350285826415205240336701⟩
  | 0, 2 => ⟨74711402170241981701882169409571134274085081578, 74711402170241981701882169409571648117578483746⟩
  | 1, 1 => ⟨75346991372525674446233952765373538217340124992, 75346991372525674446233952765374463955137592985⟩
  | 0, 3 => ⟨155490286891223726626348777156798541317191186079, 155490286891223726626348777156800213112794111397⟩
  | 1, 2 => ⟨209795333875821020270073354143853156586058018812, 209795333875821020270073354143856145293105809387⟩
  | 2, 1 => ⟨211358151763109962351545432050834937452731786080, 211358151763109962351545432050840364489274755259⟩
  | 0, 4 => ⟨267737338245996538425757265501937552256414653072, 267737338245996538425757265501943233531568498061⟩
  | 1, 3 => ⟨400291123639282139857299121651507854571646370699, 400291123639282139857299121651518155602697137757⟩
  | 2, 2 => ⟨533621888847366131047834332837184084491160318533, 533621888847366131047834332837203031751089968016⟩
  | 3, 1 => ⟨537070148660557160295252683281622501241984510139, 537070148660557160295252683281657638501644380999⟩
  | 0, 5 => ⟨-1134237321665718759794617259940639308630287691818829, 1140737363963189414043573626653110277619428845591811⟩
  | 1, 4 => ⟨-2218148242857411870165990890758574565377820462560612, 2227937174634202660253419517676944856689850083438272⟩
  | 2, 3 => ⟨-4342408547157863556273539416645981819681121243244819, 4356515605348955410241965678740579273613302954797290⟩
  | 3, 2 => ⟨-8506812071734990993277195557585029806528505556300304, 8525339374933866146803374042739287518161540683351400⟩
  | 4, 1 => ⟨-16673534015636080858787887302553147512333501745517921, 16692501710133347784311964575926824477507416769754091⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0329Geometry.ds, E8TAxisProd0329Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23130358483117786430318641895365625256473939587 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0329CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0330GraphCenterA.qJetBox,
   E8TAxisProd0330GraphCenterB.qJetBox,
   E8TAxisProd0330GraphCenterC.qJetBox,
   E8TAxisProd0330GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0330GraphWholeA.qJetBox,
   E8TAxisProd0330GraphWholeB.qJetBox,
   E8TAxisProd0330GraphWholeC.qJetBox,
   E8TAxisProd0330GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27391210168003465823013118135990176124193821701, 27391210168003465823013118135990323803653869755⟩
  | 0, 2 => ⟨82392216900720524987544035102705670262669480168, 82392216900720524987544035102706240289315821406⟩
  | 1, 1 => ⟨83012249237387463877582204090826763821320990161, 83012249237387463877582204090827793732637040539⟩
  | 0, 3 => ⟨170123056457285652858807347734572929533080465576, 170123056457285652858807347734574790254986896789⟩
  | 1, 2 => ⟨229234939840540086696818567544848597724796797165, 229234939840540086696818567544851932394819855343⟩
  | 2, 1 => ⟨230746144165770332511036149213991003673146535609, 230746144165770332511036149213997070006247139692⟩
  | 0, 4 => ⟨290735041585872758308132567891989264882497675003, 290735041585872758308132567891995611102749047174⟩
  | 1, 3 => ⟨433878412897367134170032325814365597888332466415, 433878412897367134170032325814377126894732369718⟩
  | 2, 2 => ⟨577765879755885584749302066558736881132365825694, 577765879755885584749302066558758117664893460360⟩
  | 3, 1 => ⟨581077237284455333927955100838200490033782980152, 581077237284455333927955100838239924092955656388⟩
  | 0, 5 => ⟨-1281614408897620495099795712626862706796242711511151, 1288883466916526448844470608045522542605754365680887⟩
  | 1, 4 => ⟨-2507907244712289457545457373321175737265405689871230, 2518867269921637302583735492207771426073073140389172⟩
  | 2, 3 => ⟨-4912561958779418916820568593017962186545687692677801, 4928368900943760675682405293591341931700462150450976⟩
  | 3, 2 => ⟨-9629340748724646423721767048791359862944177400013740, 9650107442453187963994883456915436826476301958799694⟩
  | 4, 1 => ⟨-18884652490257674851620766833215624367547869556355446, 18905905620695140718330803537019041668917294332872270⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0330Geometry.ds, E8TAxisProd0330Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25719497278462950606974853086718737208541894483 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0330CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0331GraphCenterA.qJetBox,
   E8TAxisProd0331GraphCenterB.qJetBox,
   E8TAxisProd0331GraphCenterC.qJetBox,
   E8TAxisProd0331GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0331GraphWholeA.qJetBox,
   E8TAxisProd0331GraphWholeB.qJetBox,
   E8TAxisProd0331GraphWholeC.qJetBox,
   E8TAxisProd0331GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24552557280376156766923060400960784490046909381, 24552557280376156766923060400960918533630256855⟩
  | 0, 2 => ⟨74517248349874569992995621436758533292226418870, 74517248349874569992995621436759046004934879640⟩
  | 1, 1 => ⟨75085059727485263734994718941588929712337105511, 75085059727485263734994718941589853385670825402⟩
  | 0, 3 => ⟨155155930891002735604450911516309174376569586599, 155155930891002735604450911516310842444735312024⟩
  | 1, 2 => ⟨209295462225908456594325412647524843158395988440, 209295462225908456594325412647527825130926079912⟩
  | 2, 1 => ⟨210691844899202490613192565098299370675711274668, 210691844899202490613192565098304785369061962893⟩
  | 0, 4 => ⟨267232405258359340845724134045851025057280247441, 267232405258359340845724134045856693246508812294⟩
  | 1, 3 => ⟨399503745654493635565952579035945266071562293593, 399503745654493635565952579035955543267196063845⟩
  | 2, 2 => ⟨532469442111268822122512025356270544046315401877, 532469442111268822122512025356289447241512455874⟩
  | 3, 1 => ⟨535550863207839251118501690402207616616575415815, 535550863207839251118501690402242671689262001555⟩
  | 0, 5 => ⟨-1131433200495501875866700730347459190989394103575827, 1137917989883188726441934009142492478540953055718111⟩
  | 1, 4 => ⟨-2212642268567198797887501334326474871239707559229893, 2222407803756353880174960246018557862477178277382476⟩
  | 2, 3 => ⟨-4331585366785471876143429087506444685328138843640915, 4345657979134491313909774877196723090245536197864531⟩
  | 3, 2 => ⟨-8485520519194279041687072246660304617884829503815873, 8504000674042450402855725121672261364595495283040388⟩
  | 4, 1 => ⟨-16631624348795936256149878218802021431158477532703339, 16650537171569882894766836094477116512258489498853550⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0331Geometry.ds, E8TAxisProd0331Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23042228908737832546794409751417391106777218055 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0331CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0332GraphCenterA.qJetBox,
   E8TAxisProd0332GraphCenterB.qJetBox,
   E8TAxisProd0332GraphCenterC.qJetBox,
   E8TAxisProd0332GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0332GraphWholeA.qJetBox,
   E8TAxisProd0332GraphWholeB.qJetBox,
   E8TAxisProd0332GraphWholeC.qJetBox,
   E8TAxisProd0332GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22070456823676675389820906555531980565771021723, 22070456823676675389820906555532102557403135292⟩
  | 0, 2 => ⟨67507230689661006947297933664498574658944482482, 67507230689661006947297933664499036926742314422⟩
  | 1, 1 => ⟨68088830317415021175462114332088192229856231055, 68088830317415021175462114332089022524564917092⟩
  | 0, 3 => ⟨141686087079248427550383897181207001495024414314, 141686087079248427550383897181208500248085386962⟩
  | 1, 2 => ⟨191384830625714260833004611882804199210914557226, 191384830625714260833004611882806871617272292914⟩
  | 2, 1 => ⟨192828086131444560674296734025525854969911113202, 192828086131444560674296734025530698431779983311⟩
  | 0, 4 => ⟨245925225384324844155751944046509958897020847624, 245925225384324844155751944046515032774553844013⟩
  | 1, 3 => ⟨368342556202644563053019646035747038565570072537, 368342556202644563053019646035756219547949933001⟩
  | 2, 2 => ⟨491484939520072788080362689962408485344724843786, 491484939520072788080362689962425347091603894823⟩
  | 3, 1 => ⟨494693395082423525865308558094288755345055759144, 494693395082423525865308558094319982834176969823⟩
  | 0, 5 => ⟨-1003423850907599032356094251377551240389122799393147, 1009206290254626136633042113862354960252731058184312⟩
  | 1, 4 => ⟨-1961106856384345109372068376105210918058493450287661, 1969802228859853368196977279064741926727792890759850⟩
  | 2, 3 => ⟨-3836911758380298100310306344106990940328115701698670, 3849429771091002101679724014243130882144945402738072⟩
  | 3, 2 => ⟨-7512105628231086308593500760687847399124918262557705, 7528535243573050061195476954256260449363308978944785⟩
  | 4, 1 => ⟨-14715197647156589320644108367783347407844555576895300, 14732011547990138359850048127181084512986770066479124⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0332Geometry.ds, E8TAxisProd0332Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20702293481300672797935006936458486031678650658 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0332CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0333GraphCenterA.qJetBox,
   E8TAxisProd0333GraphCenterB.qJetBox,
   E8TAxisProd0333GraphCenterC.qJetBox,
   E8TAxisProd0333GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0333GraphWholeA.qJetBox,
   E8TAxisProd0333GraphWholeB.qJetBox,
   E8TAxisProd0333GraphWholeC.qJetBox,
   E8TAxisProd0333GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19744284641815513442607394343206092585381318623, 19744284641815513442607394343206203451517227361⟩
  | 0, 2 => ⟨60938139362005503137477152742309509612878207360, 60938139362005503137477152742309925570627787097⟩
  | 1, 1 => ⟨61469894895424725183101638137680238994021806320, 61469894895424725183101638137680983735007480455⟩
  | 0, 3 => ⟨128987931626879298966701394403430277968555219699, 128987931626879298966701394403431621645006267934⟩
  | 1, 2 => ⟨174433628456772832281698306770089706815404292207, 174433628456772832281698306770092096211823683355⟩
  | 2, 1 => ⟨175765644101356107184368370175394648677560241462, 175765644101356107184368370175398970726813074482⟩
  | 0, 4 => ⟨225723200996547949995447437008721217067117673147, 225723200996547949995447437008725748080752061581⟩
  | 1, 3 => ⟨338709589446943055580989028904098731606543667111, 338709589446943055580989028904106912765945226643⟩
  | 2, 2 => ⟨452372558518263069073523552732445620306074669363, 452372558518263069073523552732460622402886788703⟩
  | 3, 1 => ⟨455357449075196003153129488853690692173252299553, 455357449075196003153129488853718437031044750890⟩
  | 0, 5 => ⟨-886196807775350765305729351542882555274777894104898, 891339501792931801948042577278282716247724803842230⟩
  | 1, 4 => ⟨-1730873297981304045877600596792234260355444440168423, 1738594994409758477113926692996612653769697018850447⟩
  | 2, 3 => ⟨-3384350509447482058611413065735480595822921729745757, 3395454906012165124344539680837564950870399605514220⟩
  | 3, 2 => ⟨-6621987337363435459980301945290055561921456781157639, 6636551466667209615451325910570983466823162341050104⟩
  | 4, 1 => ⟨-12963605522369856605968365211538285770531147728900039, 12978502906428278141614900883150271240544373090523700⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0333Geometry.ds, E8TAxisProd0333Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18510320709991094010914603172478852169107149131 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0333CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0334GraphCenterA.qJetBox,
   E8TAxisProd0334GraphCenterB.qJetBox,
   E8TAxisProd0334GraphCenterC.qJetBox,
   E8TAxisProd0334GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0334GraphWholeA.qJetBox,
   E8TAxisProd0334GraphWholeB.qJetBox,
   E8TAxisProd0334GraphWholeC.qJetBox,
   E8TAxisProd0334GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21986183397554351765538622952564557245226577657, 21986183397554351765538622952564678986595740792⟩
  | 0, 2 => ⟨67330315088284566401280673843623240925529367790, 67330315088284566401280673843623702175786434385⟩
  | 1, 1 => ⟨67849886856733515270124335484269299333987425188, 67849886856733515270124335484270127774581709661⟩
  | 0, 3 => ⟨141378972369338660533696706808007631918375192132, 141378972369338660533696706808009127326580400331⟩
  | 1, 2 => ⟨190924858415209522907198465460365397763633630896, 190924858415209522907198465460368064136695650389⟩
  | 2, 1 => ⟨192214398312627256782392277236386970430996739093, 192214398312627256782392277236391802848453800301⟩
  | 0, 4 => ⟨245458443208758739504227692020317657093293192041, 245458443208758739504227692020322719262571824399⟩
  | 1, 3 => ⟨367613193698927936175701872022325439528609074215, 367613193698927936175701872022334599212694459474⟩
  | 2, 2 => ⟨490415894824039524983377824623824074231131775935, 490415894824039524983377824623840896639808414816⟩
  | 3, 1 => ⟨493283016453294029168481430387331243478605147619, 493283016453294029168481430387362397658160770865⟩
  | 0, 5 => ⟨-1000942724420830312358989992934848635234530334849063, 1006711740453572071127768508024490056140418599982167⟩
  | 1, 4 => ⟨-1956237244062696416955561270754375272003506444746214, 1964912126374475797056070962099825278775087430456703⟩
  | 2, 3 => ⟨-3827343382343984646255954621467292149235262404441314, 3839831435900539499995998029840230350276936207300743⟩
  | 3, 2 => ⟨-7493289825282010330555217076084007034435150286889724, 7509678900530361845972003870296055807954820392972965⟩
  | 4, 1 => ⟨-14678174994049368295452227068627013255751492941294628, 14694942915871440955811346675999277753151835834382486⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0334Geometry.ds, E8TAxisProd0334Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20622702632226705099610696672033613526928385682 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0334CertifiedArithmetic

end


