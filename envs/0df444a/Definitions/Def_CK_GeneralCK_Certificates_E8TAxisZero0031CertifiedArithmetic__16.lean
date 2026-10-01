-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0031CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0031CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:56:26.395913+00:00
-- url     : https://prove2.me/theorems/9b3e17a9-2433-416a-b2c8-62aa993d575f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0031CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisZero0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0045CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0046CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0022GraphCenterA__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0029GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0025GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0031GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0021GraphWholeA__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0030GraphWholeC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphWholeD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0023Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0034GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0034GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0036GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043Geometry__25
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0044GraphCenterA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0045GraphWholeC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0046GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0046GraphWholeD__15

-- ===== source module GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0031GraphCenterA.qJetBox,
   E8TAxisZero0031GraphCenterB.qJetBox,
   E8TAxisZero0031GraphCenterC.qJetBox,
   E8TAxisZero0031GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0031GraphWholeA.qJetBox,
   E8TAxisZero0031GraphWholeB.qJetBox,
   E8TAxisZero0031GraphWholeC.qJetBox,
   E8TAxisZero0031GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2161912557531344799021080752153736474198558, 2161912557531344799021080752155203062500030⟩
  | 0, 2 => ⟨18537741444952031813211798075128339927550797, 18537741444952031813211798075131962887578407⟩
  | 1, 1 => ⟨18599304086412739901513232325656629418636923, 18599304086412739901513232325661917603111190⟩
  | 0, 3 => ⟨82703526166693358307235876250984309544920281, 82703526166693358307235876250991880673411828⟩
  | 1, 2 => ⟨132124018491368697430276266623584011960075662, 132124018491368697430276266623594938546906856⟩
  | 2, 1 => ⟨132464946639639294461476033463770022649511030, 132464946639639294461476033463786691572220171⟩
  | 0, 4 => ⟨212615058671446241512365385045174299543548347, 212615058671446241512365385046001185467006359⟩
  | 1, 3 => ⟨485516792907893385361725598047363945825013213, 485516792907893385361725598047394413854571088⟩
  | 2, 2 => ⟨758985484590094319791447232275059666559828055, 758985484590094319791447232275106569040954926⟩
  | 3, 1 => ⟨760438101092906497802882284806724573429807649, 760438101092906497802882284806798984510347247⟩
  | 0, 5 => ⟨-603143323404462080673624598571616852543010737257, 611472050537005753703085801088969291385685932176⟩
  | 1, 4 => ⟨-1026125500404687565076086241622038009258533752862, 1028824193754928319116682938264009821101208785635⟩
  | 2, 3 => ⟨-1773687884205076016770268412552033416837135580823, 1769402842261742647119018018868911910037005013583⟩
  | 3, 2 => ⟨-3078427555102739087757892292252462171443856472389, 3067586040575898259344467898386872898709805130053⟩
  | 4, 1 => ⟨-5326443933561759585618105463758187958657206325456, 5317644393617185083395797165608281335954087262374⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0031Geometry.ds, E8TAxisZero0031Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1812856447979990489490000727745501302203072 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0031CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0032GraphCenterA.qJetBox,
   E8TAxisZero0032GraphCenterB.qJetBox,
   E8TAxisZero0032GraphCenterC.qJetBox,
   E8TAxisZero0032GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0032GraphWholeA.qJetBox,
   E8TAxisZero0032GraphWholeB.qJetBox,
   E8TAxisZero0032GraphWholeC.qJetBox,
   E8TAxisZero0032GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1641630972384551100815289747196114387309415, 1641630972384551100815289747197498173185898⟩
  | 0, 2 => ⟨14762395640051085964580051970976057555352938, 14762395640051085964580051970979506720754652⟩
  | 1, 1 => ⟨14813989524922817709052603782559478975609365, 14813989524922817709052603782564497101094739⟩
  | 0, 3 => ⟨68604735050075876218201350126008718360850204, 68604735050075876218201350126015813494958690⟩
  | 1, 2 => ⟨110028673962884476020940092207743313558749436, 110028673962884476020940092207753508343448513⟩
  | 2, 1 => ⟨110326497348270270595390252260138785189893806, 110326497348270270595390252260154282408301262⟩
  | 0, 4 => ⟨179791776904480715222042591931296379223148421, 179791776904480715222042591932078657446502600⟩
  | 1, 3 => ⟨418183818372988767688592049430504042594414114, 418183818372988767688592049430532530655160771⟩
  | 2, 2 => ⟨657096580195467030772746227763540811279778295, 657096580195467030772746227763584471155093057⟩
  | 3, 1 => ⟨658404959608077816271847637791518558588498888, 658404959608077816271847637791587562368386543⟩
  | 0, 5 => ⟨-563854646425689653101517882716094628263483439457, 571886111382872246902229795497202172514130824815⟩
  | 1, 4 => ⟨-956267362552128709299577475962576542485253239542, 958874105520308801220227051524888835012548700206⟩
  | 2, 3 => ⟨-1647849649950070631641859327808789297244842812101, 1643731238969849584281335798127295443329875409612⟩
  | 3, 2 => ⟨-2850477007514890017354823068090894555070819043588, 2840030354019425962202759801230006975843737239727⟩
  | 4, 1 => ⟨-4913001522256272301819558776977046149872611072723, 4904454438186522035580625545452415511862116720557⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0032Geometry.ds, E8TAxisZero0032Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1360886162307321766103065219334419343987752 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0032CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0033GraphCenterA.qJetBox,
   E8TAxisZero0033GraphCenterB.qJetBox,
   E8TAxisZero0033GraphCenterC.qJetBox,
   E8TAxisZero0033GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0033GraphWholeA.qJetBox,
   E8TAxisZero0033GraphWholeB.qJetBox,
   E8TAxisZero0033GraphWholeC.qJetBox,
   E8TAxisZero0033GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1229334836574179560119703482677166633874013, 1229334836574179560119703482678471356769450⟩
  | 0, 2 => ⟨11629662200940449613585854378549783618894271, 11629662200940449613585854378553069807467789⟩
  | 1, 1 => ⟨11672566105957888732779103547633184973946227, 11672566105957888732779103547637950821422382⟩
  | 0, 3 => ⟨56485592546086920727723326818373288745633468, 56485592546086920727723326818379937572786856⟩
  | 1, 2 => ⟨90938149361370115182259873527409393809657668, 90938149361370115182259873527418905501293547⟩
  | 2, 1 => ⟨91197167779556987115758765118230928821706781, 91197167779556987115758765118245335967283554⟩
  | 0, 4 => ⟨151347245836910923442170509150962800756365533, 151347245836910923442170509151700894058268830⟩
  | 1, 3 => ⟨358672765686126731237702788015209803162710849, 358672765686126731237702788015236455807609313⟩
  | 2, 2 => ⟨566475965221273630818861340343888543535698835, 566475965221273630818861340343929206748006066⟩
  | 3, 1 => ⟨567653169252182668145532314699684509431656037, 567653169252182668145532314699748529864373558⟩
  | 0, 5 => ⟨-527392380943022466468641248888732333258658570222, 535187424976198647866181215308664473221611256091⟩
  | 1, 4 => ⟨-891591092173265414113325686614494384126053721648, 894182572780946225635327927097760827883127858684⟩
  | 2, 3 => ⟨-1531599829771964739114049477027452446702756894999, 1527744824958798119277011090204840022453606423821⟩
  | 3, 2 => ⟨-2640348524495383782166399717878873444386065510458, 2630415780572259849285882541597111770395709448327⟩
  | 4, 1 => ⟨-4532748034143292472825237006545437750169503812238, 4524582589453003287466830406409326523416505530767⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0033Geometry.ds, E8TAxisZero0033Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1005503183185808556244489151581699597606618 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0033CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0034GraphCenterA.qJetBox,
   E8TAxisZero0034GraphCenterB.qJetBox,
   E8TAxisZero0034GraphCenterC.qJetBox,
   E8TAxisZero0034GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0034GraphWholeA.qJetBox,
   E8TAxisZero0034GraphWholeB.qJetBox,
   E8TAxisZero0034GraphWholeC.qJetBox,
   E8TAxisZero0034GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨906315971955636419150222257964988753148700, 906315971955636419150222257966217917130179⟩
  | 0, 2 => ⟨9050951426635469479812697594544592420701721, 9050951426635469479812697594547725718773515⟩
  | 1, 1 => ⟨9086315922321264305911471518196672373085463, 9086315922321264305911471518201202471242681⟩
  | 0, 3 => ⟨46114912946073458448610183635154034263631755, 46114912946073458448610183635160264230043050⟩
  | 1, 2 => ⟨74518500175784818195831281510403571467259190, 74518500175784818195831281510412444973227205⟩
  | 2, 1 => ⟨74742625766801165089391359851123196799137487, 74742625766801165089391359851136588959555050⟩
  | 0, 4 => ⟨126759239598073882283318178947605155988757214, 126759239598073882283318178948299459153102435⟩
  | 1, 3 => ⟨306150949116831522931915347627397436177377819, 306150949116831522931915347627422386501788843⟩
  | 2, 2 => ⟨485980182433697470268409715328546711332173769, 485980182433697470268409715328584603815258193⟩
  | 3, 1 => ⟨487037978882451122239068598420779344753182881, 487037978882451122239068598420838770523614897⟩
  | 0, 5 => ⟨-493524531083334017771778766209515117590935300142, 501122406320243477381649105508873593869018969836⟩
  | 1, 4 => ⟨-831664104606048269178379229994440819230723115633, 834291579861694115139063424919222109569989498765⟩
  | 2, 3 => ⟨-1424125906213691950471684822617267036102820777669, 1420600711650607584876286733064703348486455596414⟩
  | 3, 2 => ⟨-2446510154755456873077440288947362534848618971048, 2437174817837751879292528710440583757447954136280⟩
  | 4, 1 => ⟨-4182790429428244837560339003020980021702619263438, 4175098601834038706040265913431967838395034921130⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0034Geometry.ds, E8TAxisZero0034Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 729553196792827974960821373704724913692827 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0034CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0035GraphCenterA.qJetBox,
   E8TAxisZero0035GraphCenterB.qJetBox,
   E8TAxisZero0035GraphCenterC.qJetBox,
   E8TAxisZero0035GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0035GraphWholeA.qJetBox,
   E8TAxisZero0035GraphWholeB.qJetBox,
   E8TAxisZero0035GraphWholeC.qJetBox,
   E8TAxisZero0035GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2305807803440893993259961271782829929221399374, 2305807803440893993259961271782850530264955814⟩
  | 0, 2 => ⟨8465482244413585960938003360529906779324019007, 8465482244413585960938003360529971982139123165⟩
  | 1, 1 => ⟨8475467087710472718421054361075916953937831243, 8475467087710472718421054361076028995356397967⟩
  | 0, 3 => ⟨20756526991740663174875093578887021211866195826, 20756526991740663174875093578887217804027821624⟩
  | 1, 2 => ⟨28759296073898121265403511770132544962810745090, 28759296073898121265403511770132881553499278087⟩
  | 2, 1 => ⟨28789084459396943064789535347702845241690943072, 28789084459396943064789535347703432159124090124⟩
  | 0, 4 => ⟨42291577648938750415298244453000831692680812040, 42291577648938750415298244453004967472564211247⟩
  | 1, 3 => ⟨66143174778376886869357443907216502132404069150, 66143174778376886869357443907217588346737971260⟩
  | 2, 2 => ⟨90014449876210011858327932334708405992044988533, 90014449876210011858327932334710335703530791626⟩
  | 3, 1 => ⟨90095579975890707712588130952480341204828851065, 90095579975890707712588130952483806476190208506⟩
  | 0, 5 => ⟨-737460022877964515296751131626184386205000196351361, 739115651211401876420276411554223980147860964208851⟩
  | 1, 4 => ⟨-1437260567568437411905713780333594324701115577247344, 1439508606167921240286976574616935800374250910559405⟩
  | 2, 3 => ⟨-2803452666398732107827646711261949270934438549213174, 2806470904788526701528628877236018575814157754446270⟩
  | 3, 2 => ⟨-5470683942732597372546034022905557973910236321818767, 5474544221756106741204576738515638154302827092295530⟩
  | 4, 1 => ⟨-10678209029619596488491344491724666151790942292109473, 10682386800745635071716168733877557442623931356465132⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0035Geometry.ds, E8TAxisZero0035Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1554284558247200698038838720629433244436402247 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0035CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0036GraphCenterA.qJetBox,
   E8TAxisZero0036GraphCenterB.qJetBox,
   E8TAxisZero0036GraphCenterC.qJetBox,
   E8TAxisZero0036GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0036GraphWholeA.qJetBox,
   E8TAxisZero0036GraphWholeB.qJetBox,
   E8TAxisZero0036GraphWholeC.qJetBox,
   E8TAxisZero0036GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1828811560661898641528227423674087226492449399, 1828811560661898641528227423674104980094124749⟩
  | 0, 2 => ⟨6833823808167856875010183645664242754867826252, 6833823808167856875010183645664297525376148297⟩
  | 1, 1 => ⟨6842097665566567260320792371704530735014609743, 6842097665566567260320792371704624163363076421⟩
  | 0, 3 => ⟨16976186613133925697926654142162543415832707543, 16976186613133925697926654142162706375871331027⟩
  | 1, 2 => ⟨23607813764591779665854518870569679645931415006, 23607813764591779665854518870569956781853702768⟩
  | 2, 1 => ⟨23632895912218162676770848531762975384349056606, 23632895912218162676770848531763456113442452886⟩
  | 0, 4 => ⟨35037492286413783923302043446298295094879312359, 35037492286413783923302043446302127625734599464⟩
  | 1, 3 => ⟨55121018917360596153815139505013926794125624795, 55121018917360596153815139505014810573205140417⟩
  | 2, 2 => ⟨75221591089860703412268531185662493006411731454, 75221591089860703412268531185664055204695113683⟩
  | 3, 1 => ⟨75291296548244541856293868081597229183098347395, 75291296548244541856293868081600022476190183763⟩
  | 0, 5 => ⟨-510000394158222282333385745987975215892301175689233, 511555771131475429124088647675237791495319700360867⟩
  | 1, 4 => ⟨-991434701877169668824423960608400418882082721925104, 993577358219781817309602868639311661782974043663113⟩
  | 2, 3 => ⟨-1929300456456881121638374192169947660517883982521350, 1932207684634114504220638532069576559538001441362001⟩
  | 3, 2 => ⟨-3756324759451196317634615914150830917777979747054562, 3760045585550452237550297996940890309202512308562869⟩
  | 4, 1 => ⟨-7315593578379141308106824245159741836453212108536470, 7319534164465836303502276980549754446401649125429368⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0036Geometry.ds, E8TAxisZero0036Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1278043446085374403982333801631627214291511111 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0036CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0037GraphCenterA.qJetBox,
   E8TAxisZero0037GraphCenterB.qJetBox,
   E8TAxisZero0037GraphCenterC.qJetBox,
   E8TAxisZero0037GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0037GraphWholeA.qJetBox,
   E8TAxisZero0037GraphWholeB.qJetBox,
   E8TAxisZero0037GraphWholeC.qJetBox,
   E8TAxisZero0037GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1444409480377801554843553955905506422096047561, 1444409480377801554843553955905521769569233955⟩
  | 0, 2 => ⟨5496710836136714110315275605972484848916183292, 5496710836136714110315275605972531020925526511⟩
  | 1, 1 => ⟨5503546435029504682279031808013154727302562972, 5503546435029504682279031808013232901476900360⟩
  | 0, 3 => ⟨13832072806326188701152799196177503193136445907, 13832072806326188701152799196177638817821951959⟩
  | 1, 2 => ⟨19311075509236394022743808475344640106845996101, 19311075509236394022743808475344869168226852352⟩
  | 2, 1 => ⟨19332122520236811602643912060511871014801241399, 19332122520236811602643912060512266255076737205⟩
  | 0, 4 => ⟨28894563178127365574760213593018403455775189841, 28894563178127365574760213593021965738789358921⟩
  | 1, 3 => ⟨45747281284662792949747037376098711679260692833, 45747281284662792949747037376099434353104564473⟩
  | 2, 2 => ⟨62614708364733205490339785600164846037510454663, 62614708364733205490339785600166116928936031527⟩
  | 3, 1 => ⟨62674342762444628994070038298277597216656332644, 62674342762444628994070038298279859754464939429⟩
  | 0, 5 => ⟨-354054991713207233280115536578054103320532411535689, 355555985906043973953963545769677325394148532911934⟩
  | 1, 4 => ⟨-686376372031698819277936855810360626551524651699285, 688478196411910910318152525414884438650771240886485⟩
  | 2, 3 => ⟨-1332286714963592889013970432769987799975421937710025, 1335173013210224791431218379442860679134800971372492⟩
  | 3, 2 => ⟨-2587656575799501353824528918064212626294257487853195, 2591360774920078609848458379750159208230077805722101⟩
  | 4, 1 => ⟨-5027560165726834011839797423135864475112052113683797, 5031416679263148833085092247376318446184388744967548⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0037Geometry.ds, E8TAxisZero0037Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1038067654292331296927994986070545521113700987 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0037CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0038GraphCenterA.qJetBox,
   E8TAxisZero0038GraphCenterB.qJetBox,
   E8TAxisZero0038GraphCenterC.qJetBox,
   E8TAxisZero0038GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0038GraphWholeA.qJetBox,
   E8TAxisZero0038GraphWholeB.qJetBox,
   E8TAxisZero0038GraphWholeC.qJetBox,
   E8TAxisZero0038GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1135760026545027930786306513997470281829335331, 1135760026545027930786306513997483667914981195⟩
  | 0, 2 => ⟨4404808540103436018220448492284000896279694936, 4404808540103436018220448492284040420112091635⟩
  | 1, 1 => ⟨4410439229402929919678595794157212568840775028, 4410439229402929919678595794157279046521091045⟩
  | 0, 3 => ⟨11227807552718843153030614629994899236802159505, 11227807552718843153030614629995014413039221313⟩
  | 1, 2 => ⟨15741160072273015778584005922730894894960289846, 15741160072273015778584005922731088293987668580⟩
  | 2, 1 => ⟨15758762186730928002282588379603794820971978989, 15758762186730928002282588379604126996894235593⟩
  | 0, 4 => ⟨23718275933542914083538376263595023317776399853, 23718275933542914083538376263598349744762495807⟩
  | 1, 3 => ⟨37812722606856739846341265422787581843529939301, 37812722606856739846341265422788188776063863790⟩
  | 2, 2 => ⟨51919814423376675114832946670072567288228668808, 51919814423376675114832946670073630138856908054⟩
  | 3, 1 => ⟨51970613204342887326870123098855271125043430082, 51970613204342887326870123098857156116802684265⟩
  | 0, 5 => ⟨-247345740167065250245284381935882615971652489046569, 248747414942489826575640728182110393738440286255615⟩
  | 1, 4 => ⟨-478082458231347973955004663188688795388655563245836, 480064285028319294819945930169881322363142517769893⟩
  | 2, 3 => ⟨-925487061988095907831202179317264578017602909011704, 928228012488829758803404798305899573184941245918520⟩
  | 3, 2 => ⟨-1792951984586236984912668164649859429524501832995401, 1796475326303244500274911604788193763005405786758058⟩
  | 4, 1 => ⟨-3474817682724749086927120881950905932035217471405309, 3478448765625950339817327971870336292690830904861390⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0038Geometry.ds, E8TAxisZero0038Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 833810647086669794550998367609219279692773405 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0038CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0039GraphCenterA.qJetBox,
   E8TAxisZero0039GraphCenterB.qJetBox,
   E8TAxisZero0039GraphCenterC.qJetBox,
   E8TAxisZero0039GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0039GraphWholeA.qJetBox,
   E8TAxisZero0039GraphWholeB.qJetBox,
   E8TAxisZero0039GraphWholeC.qJetBox,
   E8TAxisZero0039GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨888868428142665900760756052645863337953762879, 888868428142665900760756052645875043773584095⟩
  | 0, 2 => ⟨3516259266662532900378037248189207843156762979, 3516259266662532900378037248189241749729830749⟩
  | 1, 1 => ⟨3520883845111155291957012230347730758781315487, 3520883845111155291957012230347787398195912356⟩
  | 0, 3 => ⟨9079450852617858151826774405598745930071706422, 9079450852617858151826774405598843825674282914⟩
  | 1, 2 => ⟨12786450455180460368666853603185873646425684812, 12786450455180460368666853603186037015527874183⟩
  | 2, 1 => ⟨12801124192548179919811161386720369696430116443, 12801124192548179919811161386720648929471503880⟩
  | 0, 4 => ⟨19378607204339025664569109658191632004764753831, 19378607204339025664569109658194741368826698278⟩
  | 1, 3 => ⟨31128309671098429124680403881888427630431971398, 31128309671098429124680403881888936845328867233⟩
  | 2, 2 => ⟨42888844129088144331885564175825337043561671665, 42888844129088144331885564175826224680437383863⟩
  | 3, 1 => ⟨42931931909226192954644640407312760681399438427, 42931931909226192954644640407314328471275285608⟩
  | 0, 5 => ⟨-173893109565745559866088401830525324843260345983945, 175139390947284954385114641686838718375025232649697⟩
  | 1, 4 => ⟨-335011196538409142356086899243109696315569853419126, 336777203743403473018122545339010460648018452600578⟩
  | 2, 3 => ⟨-646633191994419212382668415753482984345564325919881, 649080021757188571982115208897248984992786997939070⟩
  | 3, 2 => ⟨-1249271266138621509249514656701124517807544668393221, 1252415588578636788408117520770902249538949431296523⟩
  | 4, 1 => ⟨-2414618351843175390999521216244893289370523422337455, 2417840959797657365795578261224491225004016727759221⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0039Geometry.ds, E8TAxisZero0039Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 663153004662131620964969819837335808674789715 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0039CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0040GraphCenterA.qJetBox,
   E8TAxisZero0040GraphCenterB.qJetBox,
   E8TAxisZero0040GraphCenterC.qJetBox,
   E8TAxisZero0040GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0040GraphWholeA.qJetBox,
   E8TAxisZero0040GraphWholeB.qJetBox,
   E8TAxisZero0040GraphWholeC.qJetBox,
   E8TAxisZero0040GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨692149877866458041343323217372827060347062156, 692149877866458041343323217372837323318483964⟩
  | 0, 2 => ⟨2795712958231914571195097752738438602260379232, 2795712958231914571195097752738467758649805962⟩
  | 1, 1 => ⟨2799500069093660037784198827773446085704565626, 2799500069093660037784198827773494445186323735⟩
  | 0, 3 => ⟨7314281778464867339658271103310560647513736751, 7314281778464867339658271103310643953269482388⟩
  | 1, 2 => ⟨10350067864069252326641306809103563666333901893, 10350067864069252326641306809103701781328735504⟩
  | 2, 1 => ⟨10362262780737064033550273077951923896907578948, 10362262780737064033550273077952158754775400232⟩
  | 0, 4 => ⟨15758984217317000466596625132768418526018231326, 15758984217317000466596625132771327516673110729⟩
  | 1, 3 => ⟨25523867899725153850333677343842319046949506109, 25523867899725153850333677343842746091332294669⟩
  | 2, 2 => ⟨35297999616527224166235014843698311701484980686, 35297999616527224166235014843699052414610745999⟩
  | 3, 1 => ⟨35334395344806985576416344182907884150248650495, 35334395344806985576416344182909186676193670825⟩
  | 0, 5 => ⟨-129752826770435082012235201671282318330109319571718, 130750422388634626112372238239596376570494977128524⟩
  | 1, 4 => ⟨-249212602494129092198287606959179936800905067685023, 250608488494020730734744115659504382572844521215281⟩
  | 2, 3 => ⟨-479701506984594545499704097658888967833359442384786, 481618908950869592851528474852799363088160250716981⟩
  | 3, 2 => ⟨-924320750267594700257760637529435941646766823175227, 926773719875515502381076370868188420087516277742314⟩
  | 4, 1 => ⟨-1781884275974615364022498918640937964658749746976474, 1784402983735331944923059000253778314442320588411610⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0040Geometry.ds, E8TAxisZero0040Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 518514896320297000700601130438778179997497151 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0040CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0041GraphCenterA.qJetBox,
   E8TAxisZero0041GraphCenterB.qJetBox,
   E8TAxisZero0041GraphCenterC.qJetBox,
   E8TAxisZero0041GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0041GraphWholeA.qJetBox,
   E8TAxisZero0041GraphWholeB.qJetBox,
   E8TAxisZero0041GraphWholeC.qJetBox,
   E8TAxisZero0041GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨536050357950281247779880384091114154832465782, 536050357950281247779880384091123175703273347⟩
  | 0, 2 => ⟨2213452517832990269700381990874214432052435886, 2213452517832990269700381990874239568500557186⟩
  | 1, 1 => ⟨2216544630509516839114760514806055448242370227, 2216544630509516839114760514806096836329705919⟩
  | 0, 3 => ⟨5869654661082172471971061894807520546738895464, 5869654661082172471971061894807591555605412212⟩
  | 1, 2 => ⟨8348397292085448497099678855799553658964530649, 8348397292085448497099678855799670582737154777⟩
  | 2, 1 => ⟨8358502452391509546921191756999029031626523648, 8358502452391509546921191756999226791269280167⟩
  | 0, 4 => ⟨12755428862549491315759968772565999822943897744, 12755428862549491315759968772568723305300828041⟩
  | 1, 3 => ⟨20846995891161667262058235219237434181998206767, 20846995891161667262058235219237792528604867743⟩
  | 2, 2 => ⟨28946435095220568249893641868293206564254315166, 28946435095220568249893641868293824840662848836⟩
  | 3, 1 => ⟨28977056234630640841928906386599238360810610795, 28977056234630640841928906386600320507195949320⟩
  | 0, 5 => ⟨-100168273339334687067623758595517074311973326193125, 100945642766892189455749067837736310088793671036443⟩
  | 1, 4 => ⟨-191827862804796208833695589027034035868381578307007, 192895037160800456014559619480743406686394722917750⟩
  | 2, 3 => ⟨-368256701368074278779629113181977666508123014273305, 369702965079055268618421235539878965783826981068246⟩
  | 3, 2 => ⟨-707746767837837737063112150531610976898771080600802, 709584462798171964142433709059347334990600540611221⟩
  | 4, 1 => ⟨-1360852750416697242650559662711687998835874133943620, 1362747776947196251873650258210829767760189973471718⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0041Geometry.ds, E8TAxisZero0041Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 400633811147193763161238914692628986245769281 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0041CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0042GraphCenterA.qJetBox,
   E8TAxisZero0042GraphCenterB.qJetBox,
   E8TAxisZero0042GraphCenterC.qJetBox,
   E8TAxisZero0042GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0042GraphWholeA.qJetBox,
   E8TAxisZero0042GraphWholeB.qJetBox,
   E8TAxisZero0042GraphWholeC.qJetBox,
   E8TAxisZero0042GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨412719327834891878144280943909356774459832260, 412719327834891878144280943909364723197948769⟩
  | 0, 2 => ⟨1744608874118017888312265953688845624742735109, 1744608874118017888312265953688867352207893570⟩
  | 1, 1 => ⟨1747125869306568627444397465267976500516985772, 1747125869306568627444397465268012007689970867⟩
  | 0, 3 => ⟨4691918972725218554440408641930001828350705903, 4691918972725218554440408641930062446002293207⟩
  | 1, 2 => ⟨6709690108735705283469326966050713128248822093, 6709690108735705283469326966050812225363582012⟩
  | 2, 1 => ⟨6718040301645094724454518745887236625852728182, 6718040301645094724454518745887403294048178494⟩
  | 0, 4 => ⟨10275786958154408166052804489120943504722989970, 10275786958154408166052804489123494405776831427⟩
  | 1, 3 => ⟨16962091136305958037341668459764077792119549343, 16962091136305958037341668459764378520530821530⟩
  | 2, 2 => ⟨23655079049250649455109286748691551051306967608, 23655079049250649455109286748692066979334614718⟩
  | 3, 1 => ⟨23680745653701338165383760396042980865660524410, 23680745653701338165383760396043879375050911492⟩
  | 0, 5 => ⟨-77470448370263479850963888385998551005397778391017, 78077902239808274947440031170258795173652669793206⟩
  | 1, 4 => ⟨-147889511223272008630895297335890218614119825961270, 148705016454075814628863148596035634644586790819319⟩
  | 2, 3 => ⟨-283086773282581882150325675354162415317523175182272, 284174059045591901159960936412837939250524706277414⟩
  | 3, 2 => ⟨-542539741155483711883478761781464489621757843403639, 543909433948240554077451469204354271269507396534400⟩
  | 4, 1 => ⟨-1040276382786665816993760580521547429858788934835733, 1041695220089808012513843824384210912868018430087618⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0042Geometry.ds, E8TAxisZero0042Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 307298268966973173085136288112609168840898699 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0042CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0043GraphCenterA.qJetBox,
   E8TAxisZero0043GraphCenterB.qJetBox,
   E8TAxisZero0043GraphCenterC.qJetBox,
   E8TAxisZero0043GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0043GraphWholeA.qJetBox,
   E8TAxisZero0043GraphWholeB.qJetBox,
   E8TAxisZero0043GraphWholeC.qJetBox,
   E8TAxisZero0043GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨315728812851632756285857050861437786525682994, 315728812851632756285857050861444807250405465⟩
  | 0, 2 => ⟨1368461099943555785603063203507613971529053270, 1368461099943555785603063203507632803638274527⟩
  | 1, 1 => ⟨1370503474442701060375999936744692323057294555, 1370503474442701060375999936744722862756003885⟩
  | 0, 3 => ⟨3735399488749853047958917335035712489731948448, 3735399488749853047958917335035764323334275832⟩
  | 1, 2 => ⟨5372739806361514957892543869413520199835379111, 5372739806361514957892543869413604300309990643⟩
  | 2, 1 => ⟨5379621495295553659782369128048673225146394739, 5379621495295553659782369128048813842187370715⟩
  | 0, 4 => ⟨8238973431144725771839704503893467589337476119, 8238973431144725771839704503895857322811303879⟩
  | 1, 3 => ⟨13749381773378930968280862281608187980795149047, 13749381773378930968280862281608440471149365029⟩
  | 2, 2 => ⟨19265452738391452478745080393536821163128463628, 19265452738391452478745080393537251717328209312⟩
  | 3, 1 => ⟨19286891981746315832129382836290284120915941233, 19286891981746315832129382836291029977641999969⟩
  | 0, 5 => ⟨-60066241611413699144536498599987286660720547169746, 60544689811214192375527927683520634459535612464903⟩
  | 1, 4 => ⟨-114271953423631946594052397905858477326775792906894, 114898368880480182174003584125729380135688293319285⟩
  | 2, 3 => ⟨-218055928024497468086337329878253990638368862413295, 218875312019285407308770136990425831659176678106617⟩
  | 3, 2 => ⟨-416649802040535279842186759112122659626680159236813, 417671165830783377404794092448382641744923232603050⟩
  | 4, 1 => ⟨-796483294772934890318207448426667909735435111275668, 797546229426260965480619419026258024007861299091158⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0043Geometry.ds, E8TAxisZero0043Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 233808457571725037090838526029112454590083804 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0043CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0044GraphCenterA.qJetBox,
   E8TAxisZero0044GraphCenterB.qJetBox,
   E8TAxisZero0044GraphCenterC.qJetBox,
   E8TAxisZero0044GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0044GraphWholeA.qJetBox,
   E8TAxisZero0044GraphWholeB.qJetBox,
   E8TAxisZero0044GraphWholeC.qJetBox,
   E8TAxisZero0044GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨239833721052322912002854221758796579461563164, 239833721052322912002854221758802794571908271⟩
  | 0, 2 => ⟨1067816943328909545124537483158346060840013132, 1067816943328909545124537483158362429594223818⟩
  | 1, 1 => ⟨1069468652267940203438341665943658279440618257, 1069468652267940203438341665943684616997504253⟩
  | 0, 3 => ⟨2961438440648465733419759807373833936804593075, 2961438440648465733419759807373878340150244146⟩
  | 1, 2 => ⟨4285633939723215741040821345210323452828282697, 4285633939723215741040821345210394933603222082⟩
  | 2, 1 => ⟨4291290907692455527665021418861524151873351456, 4291290907692455527665021418861642940047021381⟩
  | 0, 4 => ⟨6574194022854218859005853396053425405381227065, 6574194022854218859005853396055664043636699489⟩
  | 1, 3 => ⟨11103904655554158266025900627084105551339135564, 11103904655554158266025900627084317713102071764⟩
  | 2, 2 => ⟨15638404865789096729336973879873938607727098008, 15638404865789096729336973879874298069640578201⟩
  | 3, 1 => ⟨15656256285137361326432151973946109040791239952, 15656256285137361326432151973946728254041489845⟩
  | 0, 5 => ⟨-46702751668970675832192838688234795550455729307794, 47079785790585234409118499756510360308745228968283⟩
  | 1, 4 => ⟨-88518911582532202804859403980422455090034045671372, 88998191120263611328143779888086844047892632003435⟩
  | 2, 3 => ⟨-168346005335066607128379059911433811073237365946107, 168958321853111023887633699024206494229105694865005⟩
  | 3, 2 => ⟨-320622160215960515070042826065024197978754330613034, 321375081343671937646127436178527254443825516304786⟩
  | 4, 1 => ⟨-610914382157039043940233360059770666627999922924365, 611702082089488987901681317301744886363840430292542⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0044Geometry.ds, E8TAxisZero0044Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 176308059183287931061383048458604672720117913 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0044CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0045GraphCenterA.qJetBox,
   E8TAxisZero0045GraphCenterB.qJetBox,
   E8TAxisZero0045GraphCenterC.qJetBox,
   E8TAxisZero0045GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0045GraphWholeA.qJetBox,
   E8TAxisZero0045GraphWholeB.qJetBox,
   E8TAxisZero0045GraphWholeC.qJetBox,
   E8TAxisZero0045GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨180768513872112484677146473491983077975715582, 180768513872112484677146473491988591606191548⟩
  | 0, 2 => ⟨828468819165521977916145876880320360878750128, 828468819165521977916145876880334629870892217⟩
  | 1, 1 => ⟨829799776146973885306927988863912057775445385, 829799776146973885306927988863934834725270936⟩
  | 0, 3 => ⟨2337503850610525901954014260329728358881243107, 2337503850610525901954014260329766471250918138⟩
  | 1, 2 => ⟨3404588615417585922645510861826389844144577026, 3404588615417585922645510861826450699207163794⟩
  | 2, 1 => ⟨3409227258906934846585303620453099859576792146, 3409227258906934846585303620453200350897404436⟩
  | 0, 4 => ⟨5220129484126512513393257178955931816127994683, 5220129484126512513393257178958028246260936064⟩
  | 1, 3 => ⟨8934408675633754651443145716227688604701994763, 8934408675633754651443145716227867083318545574⟩
  | 2, 2 => ⟨12652734275564723644062677854810796274068532404, 12652734275564723644062677854811096612811705708⟩
  | 3, 1 => ⟨12667555756958659877806705931702499127605634352, 12667555756958659877806705931703013440023136444⟩
  | 0, 5 => ⟨-36489066423462749257109444511443735782770522121078, 36785303304329609459062934005648658930145247945095⟩
  | 1, 4 => ⟨-68882899372137640329604013124628848422737971240203, 69246322063842802121566634324847998878562015687246⟩
  | 2, 3 => ⟨-130528317971574140062071598120522154587218892061012, 130978892804418025858055859889074928992671375627243⟩
  | 3, 2 => ⟨-247727861707485156596119143217541684168779264885977, 248271948837850653359802725193671655027832160616718⟩
  | 4, 1 => ⟨-470360758189694606970404389391042364066353248335070, 470933773429677451148339328595930704994700960709625⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0045Geometry.ds, E8TAxisZero0045Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 131587462190313154053157381956725946970436913 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0045CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0046GraphCenterA.qJetBox,
   E8TAxisZero0046GraphCenterB.qJetBox,
   E8TAxisZero0046GraphCenterC.qJetBox,
   E8TAxisZero0046GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0046GraphWholeA.qJetBox,
   E8TAxisZero0046GraphWholeB.qJetBox,
   E8TAxisZero0046GraphWholeC.qJetBox,
   E8TAxisZero0046GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨135075678736674666216844844270599558011643566, 135075678736674666216844844270604461479372457⟩
  | 0, 2 => ⟨638719885164700175202471284204200265294773671, 638719885164700175202471284204212754775416315⟩
  | 1, 1 => ⟨639788143657792821352716774962178011967686638, 639788143657792821352716774962197790525183117⟩
  | 0, 3 => ⟨1836368606683417677742100485791089941702557840, 1836368606683417677742100485791122770516094280⟩
  | 1, 2 => ⟨2692872370657790333430013029652474769794761401, 2692872370657790333430013029652526756579535325⟩
  | 2, 1 => ⟨2696666599333227790300377420467721845052801013, 2696666599333227790300377420467807138938239199⟩
  | 0, 4 => ⟨4124086821107364809868260281904326264600555588, 4124086821107364809868260281906288489265315945⟩
  | 1, 3 => ⟨7162190766766175444377426117029605698615500077, 7162190766766175444377426117029756345507538761⟩
  | 2, 2 => ⟨10203710916247803546602423184360150932909065825, 10203710916247803546602423184360402649686819329⟩
  | 3, 1 => ⟨10215985291371732857651250180504364404277899003, 10215985291371732857651250180504792806415962167⟩
  | 0, 5 => ⟨-28656145202713598659861525057870194381248723585140, 28890338943130554376496971246418354124830814568199⟩
  | 1, 4 => ⟨-53861672546577351063628641917552163548296201988421, 54137174825333273631993999730109531715762839280733⟩
  | 2, 3 => ⟨-101667080038225084353655047158185259533451832198765, 101995907743965575195899118687780235745350331550710⟩
  | 3, 2 => ⟨-192227962411194147140607393897850134141284527221343, 192615536583313745081027652783753366727017085560809⟩
  | 4, 1 => ⟨-363601702078916035734014082953199880509200881972019, 364013772467867977969621155541388754216162585039375⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0046Geometry.ds, E8TAxisZero0046Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 97073491086109428360971994198858139551165138 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0046CertifiedArithmetic

end


