-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0290CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0290CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:37:36.399461+00:00
-- url     : https://prove2.me/theorems/5dff2142-f36c-45a6-9802-35226c49ed3e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0290CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0291CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0292CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0293CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0294CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0295CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0296CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0297CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0298CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0299CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0300CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0301CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0302CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0303CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0304CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0305CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0286GraphCenterA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0289GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0274GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0290GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0282GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0278GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0285GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0285GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0280Geometry__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0291GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0292GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0293GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0295GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0295GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0297Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0303GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0304GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0305GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0305GraphWholeB__9

-- ===== source module GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0290GraphCenterA.qJetBox,
   E8TAxisProd0290GraphCenterB.qJetBox,
   E8TAxisProd0290GraphCenterC.qJetBox,
   E8TAxisProd0290GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0290GraphWholeA.qJetBox,
   E8TAxisProd0290GraphWholeB.qJetBox,
   E8TAxisProd0290GraphWholeC.qJetBox,
   E8TAxisProd0290GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨28013957005684592300852073532867958810537429953, 28013957005684592300852073532868108330829207794⟩
  | 0, 2 => ⟨83676347512326482232171680517896078433170375718, 83676347512326482232171680517896656035856182618⟩
  | 1, 1 => ⟨84743761999821065977447477722289552516260987180, 84743761999821065977447477722290596288784181149⟩
  | 0, 3 => ⟨172315885771841526260521145734200456618276128373, 172315885771841526260521145734202342382901714895⟩
  | 1, 2 => ⟨232508197969095455947546326398156383313636899248, 232508197969095455947546326398159763313846949723⟩
  | 2, 1 => ⟨235107411220699677373966390566817444875553584220, 235107411220699677373966390566823594405116354503⟩
  | 0, 4 => ⟨294025020874917900193033970291616740144978142524, 294025020874917900193033970291623174556524997557⟩
  | 1, 3 => ⟨438999350196111038813172801046456297165995238815, 438999350196111038813172801046467987050020637363⟩
  | 2, 2 => ⟨585252226753618367575236524878930136882282033994, 585252226753618367575236524878951671143745546092⟩
  | 3, 1 => ⟨590943590978714384372198425772006249259867554881, 590943590978714384372198425772046239140327604151⟩
  | 0, 5 => ⟨-1301232990864215509180889896491331640976778851822240, 1308603351925133753657864364872119782490383692090169⟩
  | 1, 4 => ⟨-2546452124455030193635917657196411589665435597785396, 2557568192892058162652114526098583484097603591038339⟩
  | 2, 3 => ⟨-4988371624692855272489884687257351097198733423278522, 5004410178225365408119958587482318472190691020391965⟩
  | 3, 2 => ⟨-9778550929691029385463808329785062538672613458637927, 9799640085638377622104541238678015842462283638265669⟩
  | 4, 1 => ⟨-19178495583925442896716174879025032742036743412658235, 19200140732148104547551421068117252105209227334519470⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0290Geometry.ds, E8TAxisProd0290Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26308205973096323296649923164904494971753201979 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0290CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0291GraphCenterA.qJetBox,
   E8TAxisProd0291GraphCenterB.qJetBox,
   E8TAxisProd0291GraphCenterC.qJetBox,
   E8TAxisProd0291GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0291GraphWholeA.qJetBox,
   E8TAxisProd0291GraphWholeB.qJetBox,
   E8TAxisProd0291GraphWholeC.qJetBox,
   E8TAxisProd0291GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨25115819246653180169032730945673789130643649413, 25115819246653180169032730945673924841280206412⟩
  | 0, 2 => ⟨75688462193835259990021897258596579528971386373, 75688462193835259990021897258597099063031309034⟩
  | 1, 1 => ⟨76666056104615496380546515353981455608463027052, 76666056104615496380546515353982391735895513742⟩
  | 0, 3 => ⟨157171563974193795822725634705958175688744815450, 157171563974193795822725634705959866244696001166⟩
  | 1, 2 => ⟨212309502889115416837331095488419429106293656321, 212309502889115416837331095488422451709184278125⟩
  | 2, 1 => ⟨214711366545759659282569605686226322740201458891, 214711366545759659282569605686231811903008083787⟩
  | 0, 4 => ⟨270274924021592538131123280828367188582860491002, 270274924021592538131123280828372935732063297004⟩
  | 1, 3 => ⟨404248724701889043501008133513566421072878439341, 404248724701889043501008133513576842090554612334⟩
  | 2, 2 => ⟨539415603592633432287986044547025270036928073488, 539415603592633432287986044547044439116929010989⟩
  | 3, 1 => ⟨544711822058934853733326978345690103716920884790, 544711822058934853733326978345725654703568575858⟩
  | 0, 5 => ⟨-1148338490776249561669938652387875777751067315999431, 1154915382437607543717957606132302812175231896410075⟩
  | 1, 4 => ⟨-2245836560115291920482090983441979457135738964050640, 2255743412945786422294181388842596375152239288774401⟩
  | 2, 3 => ⟨-4396836503026486746104890139629331399143883794509052, 4411117311339511840595590285379303514529549151312277⟩
  | 3, 2 => ⟨-8613884990252236325292600886941794429179059349610938, 8632650495207395480692461480947973708486340372269404⟩
  | 4, 1 => ⟨-16884295847856326341066106076716042184345580084608719, 16903541821608596477967974375466608560188388133674663⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0291Geometry.ds, E8TAxisProd0291Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23574478801464288597588411678746504407198316344 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0291CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0292GraphCenterA.qJetBox,
   E8TAxisProd0292GraphCenterB.qJetBox,
   E8TAxisProd0292GraphCenterC.qJetBox,
   E8TAxisProd0292GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0292GraphWholeA.qJetBox,
   E8TAxisProd0292GraphWholeB.qJetBox,
   E8TAxisProd0292GraphWholeC.qJetBox,
   E8TAxisProd0292GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22580763316039625541347331123467291069285401225, 22580763316039625541347331123467414573318931056⟩
  | 0, 2 => ⟨68576819336000826943111881944490703296416043140, 68576819336000826943111881944491171715670161583⟩
  | 1, 1 => ⟨69534617352291119853991396577411454782239592106, 69534617352291119853991396577412296286438542451⟩
  | 0, 3 => ⟨143541073783100961068877820339202145683536498349, 143541073783100961068877820339203664660655125624⟩
  | 1, 2 => ⟨194163882565606257446607160367198329307494730487, 194163882565606257446607160367201038194166295175⟩
  | 2, 1 => ⟨196538386415890462081170343171661487548950548276, 196538386415890462081170343171666397792492896615⟩
  | 0, 4 => ⟨248742700647238742432419202201460053110532031574, 248742700647238742432419202201465197795055746246⟩
  | 1, 3 => ⟨372745676605684289952686092346967840547100060478, 372745676605684289952686092346977150333861393397⟩
  | 2, 2 => ⟨497940211419462495468843122468520760742700896612, 497940211419462495468843122468537860393210336896⟩
  | 3, 1 => ⟨503214644707339890707978626372683598267167645889, 503214644707339890707978626372715269109300588356⟩
  | 0, 5 => ⟨-1018410683242005480749853633265006272388408028524766, 1024274400873473107645848884612592420242973518487378⟩
  | 1, 4 => ⟨-1990521292021652078250881616999680791882268357520416, 1999340758985551063821017089205380539097036946719063⟩
  | 2, 3 => ⟨-3894709442781019304432270682693231973891607994642554, 3907409006002291730090223231310889788643408772236326⟩
  | 3, 2 => ⟨-7625764043080087515021589643882329601937185794990270, 7642439628349090845151577044210151930178863823171169⟩
  | 4, 1 => ⟨-14938839639173098337456575037532492192021553747829968, 14955933360283686203804088326753932054762747228252610⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0292Geometry.ds, E8TAxisProd0292Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 21184269695677501984441386112884976827236461365 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0292CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0293GraphCenterA.qJetBox,
   E8TAxisProd0293GraphCenterB.qJetBox,
   E8TAxisProd0293GraphCenterC.qJetBox,
   E8TAxisProd0293GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0293GraphWholeA.qJetBox,
   E8TAxisProd0293GraphWholeB.qJetBox,
   E8TAxisProd0293GraphWholeC.qJetBox,
   E8TAxisProd0293GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨20204964389396590201932052282339601472521583337, 20204964389396590201932052282339713709394200021⟩
  | 0, 2 => ⟨61911921660856204585532529912613548413941947755, 61911921660856204585532529912613969911584081892⟩
  | 1, 1 => ⟨62787711442102485521843466046357261731362898764, 62787711442102485521843466046358016544064611954⟩
  | 0, 3 => ⟨130690602627641785876955479336551700235688876331, 130690602627641785876955479336553062074398833624⟩
  | 1, 2 => ⟨176989214219834141739509097205145779334728821497, 176989214219834141739509097205148201426952124473⟩
  | 2, 1 => ⟨179180847539590461104982957661044504192063226855, 179180847539590461104982957661048886008920088379⟩
  | 0, 4 => ⟨228326854016000176559307336156358699452056246082, 228326854016000176559307336156363293863602711135⟩
  | 1, 3 => ⟨342787113185462345881535127927925081156516547912, 342787113185462345881535127927933377455702760523⟩
  | 2, 2 => ⟨458359276905108319582402770185176730076929469134, 458359276905108319582402770185191944602373632144⟩
  | 3, 1 => ⟨463266271616570891657833283832838066480435064853, 463266271616570891657833283832866206834462629789⟩
  | 0, 5 => ⟨-899831580108357685745749356942419688264026188498069, 905046447350367717001385516620145342178743141428736⟩
  | 1, 4 => ⟨-1757623298343985997129273437719930258645891256821039, 1765454752904790648889485258669898581139230530250554⟩
  | 2, 3 => ⟨-3436891683643333062580081967903535791762882470517613, 3448155785777083114120952306245621086341929896703216⟩
  | 3, 2 => ⟨-6725267279228552565432304962112422830491079904657020, 6740045855471185079547188985338821223720539979514247⟩
  | 4, 1 => ⟨-13166743365275982128727324246636224664481924767552433, 13181879723091020436482210848357026411365289123372963⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0293Geometry.ds, E8TAxisProd0293Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18945176049065297519467738647563394229792212254 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0293CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0294GraphCenterA.qJetBox,
   E8TAxisProd0294GraphCenterB.qJetBox,
   E8TAxisProd0294GraphCenterC.qJetBox,
   E8TAxisProd0294GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0294GraphWholeA.qJetBox,
   E8TAxisProd0294GraphWholeB.qJetBox,
   E8TAxisProd0294GraphWholeC.qJetBox,
   E8TAxisProd0294GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22495154352400983540893065530899490148279533556, 22495154352400983540893065530899613398952288134⟩
  | 0, 2 => ⟨68397587201146308033316058831142518056682475817, 68397587201146308033316058831142985445168965727⟩
  | 1, 1 => ⟨69292203514614137333238730681049318556268385972, 69292203514614137333238730681050158182080096217⟩
  | 0, 3 => ⟨143230440230666681029265045621626965238417295683, 143230440230666681029265045621628480826335662305⟩
  | 1, 2 => ⟨193698411274163638584293642314789637536302039662, 193698411274163638584293642314792340309377664083⟩
  | 2, 1 => ⟨195916636841677269306922998741314285811402481914, 195916636841677269306922998741319184863064439915⟩
  | 0, 4 => ⟨248271117246667034920106781972725664400302301718, 248271117246667034920106781972730797216997770353⟩
  | 1, 3 => ⟨372008604900709573648362288690409373841674102439, 372008604900709573648362288690418662039709609164⟩
  | 2, 2 => ⟨496859434860721501588391519043171743500218404599, 496859434860721501588391519043188803275980456190⟩
  | 3, 1 => ⟨501787390531737641558542991747505960419351573864, 501787390531737641558542991747537556951315202369⟩
  | 0, 5 => ⟨-1015900937864314435246336042518576606361854376755683, 1021751022118401535178106021192442747967401644066065⟩
  | 1, 4 => ⟨-1985595409925191555409870264193704041503406005892791, 1994394056809965151263431111235534002979896209370933⟩
  | 2, 3 => ⟨-3885030270471541306351766850995542120183428877638668, 3897699359970218564867240885551312900234016577406063⟩
  | 3, 2 => ⟨-7606729868121799008584726822878879556225224846123531, 7623364130574890947806714501197612954832517446394245⟩
  | 4, 1 => ⟨-14901386282325356590523115947738693445629702875426893, 14918432892327602063821875564307678865532010948650778⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0294Geometry.ds, E8TAxisProd0294Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 21103410508466743213731621488897188181271533992 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0294CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0295GraphCenterA.qJetBox,
   E8TAxisProd0295GraphCenterB.qJetBox,
   E8TAxisProd0295GraphCenterC.qJetBox,
   E8TAxisProd0295GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0295GraphWholeA.qJetBox,
   E8TAxisProd0295GraphWholeB.qJetBox,
   E8TAxisProd0295GraphWholeC.qJetBox,
   E8TAxisProd0295GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨20127676515064158718307946491576561305351040799, 20127676515064158718307946491576673312596720926⟩
  | 0, 2 => ⟨61748736674388161044354442535244347693012502549, 61748736674388161044354442535244768262359250741⟩
  | 1, 1 => ⟨62566742548927544970811987872508974794501400009, 62566742548927544970811987872509727919459792751⟩
  | 0, 3 => ⟨130405466512951792004551867719157898282639570233, 130405466512951792004551867719159257077652668080⟩
  | 1, 2 => ⟨176561157063461408640330925779952331508881780587, 176561157063461408640330925779954748121693621706⟩
  | 2, 1 => ⟨178608525096891928297448396878101647489941782727, 178608525096891928297448396878106019290292355457⟩
  | 0, 4 => ⟨227891053721620409696467376874097803204384383918, 227891053721620409696467376874102386989846806033⟩
  | 1, 3 => ⟨342104536877524355454960899923438441696813895833, 342104536877524355454960899923446718697404207308⟩
  | 2, 2 => ⟨457356935987158993327390724282111226676121634083, 457356935987158993327390724282126405596282746308⟩
  | 3, 1 => ⟨461941577228869944579577946915261416180989004638, 461941577228869944579577946915289490245311498228⟩
  | 0, 5 => ⟨-897547768494516074156237927321377774190189104283461, 902750530900357036198972770215017321285497059676802⟩
  | 1, 4 => ⟨-1753142651520244865268155106327195082796823107364575, 1760955694120073015739174886748393664114335301866761⟩
  | 2, 3 => ⟨-3428090891203440530789116989286068904894277350347881, 3439328192083794918146417767455665419776681462951397⟩
  | 3, 2 => ⟨-6707967385720759242301171839108407669078872270369458, 6722709946000169456569928588098785114339198266106036⟩
  | 4, 1 => ⟨-13132716341993658780813807739885390201342768568410557, 13147812484034919540661737053851538377375842337463649⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0295Geometry.ds, E8TAxisProd0295Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18872218078618967609153262276247415076667249601 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0295CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0296GraphCenterA.qJetBox,
   E8TAxisProd0296GraphCenterB.qJetBox,
   E8TAxisProd0296GraphCenterC.qJetBox,
   E8TAxisProd0296GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0296GraphWholeA.qJetBox,
   E8TAxisProd0296GraphWholeB.qJetBox,
   E8TAxisProd0296GraphWholeC.qJetBox,
   E8TAxisProd0296GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27909496097413508982731447386145629681528230502, 27909496097413508982731447386145778893434620776⟩
  | 0, 2 => ⟨83461182218698277432948864086520249300367956873, 83461182218698277432948864086520825633583928150⟩
  | 1, 1 => ⟨84453469497271953588835094271589166268638057496, 84453469497271953588835094271590207718455025800⟩
  | 0, 3 => ⟨171948698753432063897256568601405015808232211000, 171948698753432063897256568601406897376166935452⟩
  | 1, 2 => ⟨231959984695714390694322776188264290336473390507, 231959984695714390694322776188267662740074800094⟩
  | 2, 1 => ⟨234376629536302632709793910669599470659482751514, 234376629536302632709793910669605606246480204288⟩
  | 0, 4 => ⟨293474364150113885999306354808008507752044957075, 293474364150113885999306354808014927382151158651⟩
  | 1, 3 => ⟨438142136251287144232398389488074830264988595198, 438142136251287144232398389488086493184897935624⟩
  | 2, 2 => ⟨583998846500667487861118569978918589543745363277, 583998846500667487861118569978940073904037692452⟩
  | 3, 1 => ⟨589291074617382245494204292410367118524268397442, 589291074617382245494204292410407015245636139271⟩
  | 0, 5 => ⟨-1297946903589810709994319929816098771117580650204445, 1305300283736441163780875454791411016066096058971014⟩
  | 1, 4 => ⟨-2539995862101967906024586171907647575019304148469614, 2551085766080683340276717376404572592912450917417544⟩
  | 2, 3 => ⟨-4975673405960407968639492125412030112799786855579267, 4991673095233896669051154340942420988706003110866078⟩
  | 3, 2 => ⟨-9753557786574752112874227507229073524536244984733904, 9774592751859538693126183900496706477171309859728194⟩
  | 4, 1 => ⟨-19129275497290740407336375753923275842556694904332408, 19150854536778630767830997265879169474629253832554554⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0296Geometry.ds, E8TAxisProd0296Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26209451296419741114903130661631354819222905165 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0296CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0297GraphCenterA.qJetBox,
   E8TAxisProd0297GraphCenterB.qJetBox,
   E8TAxisProd0297GraphCenterC.qJetBox,
   E8TAxisProd0297GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0297GraphWholeA.qJetBox,
   E8TAxisProd0297GraphWholeB.qJetBox,
   E8TAxisProd0297GraphWholeC.qJetBox,
   E8TAxisProd0297GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨25021331371256585993315648736023200763413694206, 25021331371256585993315648736023336194779124591⟩
  | 0, 2 => ⟨75492208758479802260503266095039236311683492297, 75492208758479802260503266095039754702727128363⟩
  | 1, 1 => ⟨76400984838383755566848999972950795349217698274, 76400984838383755566848999972951729389715710910⟩
  | 0, 3 => ⟨156834038687129261442159716022997754438433633355, 156834038687129261442159716022999441225833608562⟩
  | 1, 2 => ⟨211804688558586784332790514183720179935814955466, 211804688558586784332790514183723195729661311351⟩
  | 2, 1 => ⟨214037824106222118961800218406692255944640269980, 214037824106222118961800218406697732627288248871⟩
  | 0, 4 => ⟨269765679563577178670067196877288140002951703699, 269765679563577178670067196877293873917866368688⟩
  | 1, 3 => ⟨403454435462921212327570966120390523491909495510, 403454435462921212327570966120400920403918629820⟩
  | 2, 2 => ⟨538252651332946379782077223237254840593531391478, 538252651332946379782077223237273965109253740330⟩
  | 3, 1 => ⟨543177436830736993781186492152271634317743375036, 543177436830736993781186492152307102185327591294⟩
  | 0, 5 => ⟨-1145507495144333454623293889366011911421726745197615, 1152068939359038943118911065758090392440235686793161⟩
  | 1, 4 => ⟨-2240277731199215082318080022880237833218598754385784, 2250160874545259918197950462336571371815696709217305⟩
  | 2, 3 => ⟨-4385909227317303070688368319444511408691627446374666, 4400155082008633772676695949774433104326261453791160⟩
  | 3, 2 => ⟨-8592388233780342867802143381336126802810338929542322, 8611105768862389464712958204553461360795868917071204⟩
  | 4, 1 => ⟨-16841981382212513548185254968072526595811917439600853, 16861171174847940633090064988378370835203487865908585⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0297Geometry.ds, E8TAxisProd0297Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23485190073824812115827455534086379396026750762 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0297CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0298GraphCenterA.qJetBox,
   E8TAxisProd0298GraphCenterB.qJetBox,
   E8TAxisProd0298GraphCenterC.qJetBox,
   E8TAxisProd0298GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0298GraphWholeA.qJetBox,
   E8TAxisProd0298GraphWholeB.qJetBox,
   E8TAxisProd0298GraphWholeC.qJetBox,
   E8TAxisProd0298GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨27805303859073777086143184076906781005553206434, 27805303859073777086143184076906929909707995841⟩
  | 0, 2 => ⟨83246475478885500773722220477966966504277469796, 83246475478885500773722220477967541570749982755⟩
  | 1, 1 => ⟨84163861592005135597061632994535811016537944029, 84163861592005135597061632994536850148664933003⟩
  | 0, 3 => ⟨171582199472846748661627132396462816970248421711, 171582199472846748661627132396464694350680731184⟩
  | 1, 2 => ⟨231412842006381578098366877915700364107126025277, 231412842006381578098366877915703728930798190199⟩
  | 2, 1 => ⟨233647413159698748491345358968912266438036783573, 233647413159698748491345358968918388113153101461⟩
  | 0, 4 => ⟨292924640112161558624977550826648256037835131043, 292924640112161558624977550826654660919756505813⟩
  | 1, 3 => ⟨437286415312171183295913444483010794486411637776, 437286415312171183295913444483022430502856828049⟩
  | 2, 2 => ⟨582747733646145850183552012871269509314316963144, 582747733646145850183552012871290943885643846070⟩
  | 3, 1 => ⟨587641815526338911818781963310156263053646869195, 587641815526338911818781963310196066825426772181⟩
  | 0, 5 => ⟨-1294667350247138049609180958765803522193743453917501, 1302003785945500703091517199298225912880176404002870⟩
  | 1, 4 => ⟨-2533552459858566778075123150658549111508335204592629, 2544616260887169441031138388963092927037203221853780⟩
  | 2, 3 => ⟨-4963000530048618974172667743181463245741974576963580, 4978961459349518335259397094247968798825717464577134⟩
  | 3, 2 => ⟨-9728614627504209368169875263986920578134364741619832, 9749595580633509479418509555651538599254939069193258⟩
  | 4, 1 => ⟨-19080154056755632244141136192097525044018999144171441, 19101667296720600798363758970739307960740758111473393⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0298Geometry.ds, E8TAxisProd0298Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26110951972519922664106962141287678719248028904 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0298CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0299GraphCenterA.qJetBox,
   E8TAxisProd0299GraphCenterB.qJetBox,
   E8TAxisProd0299GraphCenterC.qJetBox,
   E8TAxisProd0299GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0299GraphWholeA.qJetBox,
   E8TAxisProd0299GraphWholeB.qJetBox,
   E8TAxisProd0299GraphWholeC.qJetBox,
   E8TAxisProd0299GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24927088549128254872946085460387352137382298764, 24927088549128254872946085460387487290049750289⟩
  | 0, 2 => ⟨75296376832111294215365902824925274364249658733, 75296376832111294215365902824925791614733732912⟩
  | 1, 1 => ⟨76136543969887995738349663195341491303946286225, 76136543969887995738349663195342423262023170523⟩
  | 0, 3 => ⟨156497149414863735347970234378386810034654136269, 156497149414863735347970234378388493061761696851⟩
  | 1, 2 => ⟨211300866222633543043512247259363781636056225441, 211300866222633543043512247259366790635828773338⟩
  | 2, 1 => ⟨213365734039005848301058720133163087969537992857, 213365734039005848301058720133168552199540098461⟩
  | 0, 4 => ⟨269257300116308213194471101971078213709369025601, 269257300116308213194471101971083934419801476651⟩
  | 1, 3 => ⟨402661533003039326594058605296465378213337419196, 402661533003039326594058605296475751073971737055⟩
  | 2, 2 => ⟨537091807284919360288178897293563129435842761173, 537091807284919360288178897293582209487642156165⟩
  | 3, 1 => ⟨541646082204976342050372251977039488280797689693, 541646082204976342050372251977074873216567235985⟩
  | 0, 5 => ⟨-1142681886301060898201279337986580237490364516642030, 1149227920853104903424203938834847146298310117670847⟩
  | 1, 4 => ⟨-2234729496783132010325662802792849683536646840344988, 2244588993027357008094538356206423266403072647399044⟩
  | 2, 3 => ⟨-4375002817068012125593966674003625676152839202535264, 4389213820181083203219275370709420344173104474323647⟩
  | 3, 2 => ⟨-8570932609306826361156553176589487539712397099052134, 8589602339703748228891873591780993731070167500559178⟩
  | 4, 1 => ⟨-16799748055977878307725442021786268748508013388667369, 16818881930885434607597998563042029473284475678037953⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0299Geometry.ds, E8TAxisProd0299Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23396134180454053203989943670641041633226841661 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0299CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0300GraphCenterA.qJetBox,
   E8TAxisProd0300GraphCenterB.qJetBox,
   E8TAxisProd0300GraphCenterC.qJetBox,
   E8TAxisProd0300GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0300GraphWholeA.qJetBox,
   E8TAxisProd0300GraphWholeB.qJetBox,
   E8TAxisProd0300GraphWholeC.qJetBox,
   E8TAxisProd0300GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22409769186401891662722221644033179884888463135, 22409769186401891662722221644033302882719417935⟩
  | 0, 2 => ⟨68218742990017091348209910116687864480597195745, 68218742990017091348209910116688330840532312150⟩
  | 1, 1 => ⟨69050370940550298195048074454920522938257166856, 69050370940550298195048074454921360689748723796⟩
  | 0, 3 => ⟨142920395655250497103054083971342825974463188978, 142920395655250497103054083971344338180612485127⟩
  | 1, 2 => ⟨193233860515799184506178637129602097208011255280, 193233860515799184506178637129604793880947453246⟩
  | 2, 1 => ⟨195296237010582051669929050239150259519884576193, 195296237010582051669929050239155147404378351989⟩
  | 0, 4 => ⟨247800337207266857461411819830113103307626840665, 247800337207266857461411819830118224283239087368⟩
  | 1, 3 => ⟨371272823328561317852911391594216601284663866406, 371272823328561317852911391594225867942649910951⟩
  | 2, 2 => ⟨495780621878016481801165268032102779873027910961, 495780621878016481801165268032119799863966272958⟩
  | 3, 1 => ⟨500362961327359002565377960090689311071476451211, 500362961327359002565377960090720833460967277317⟩
  | 0, 5 => ⟨-1013395975495307128430627513321482977953496531591633, 1019232460619870585323112019594913594058069742926339⟩
  | 1, 4 => ⟨-1980678932178453223377573751584110436511916943490445, 1989456814037026655197045670935767666244773813477171⟩
  | 2, 3 => ⟨-3875369615447353892159733992674138442756283713974217, 3888008317759727249322266392965353748052957701255813⟩
  | 3, 2 => ⟨-7587732189230535909468055879348729558563377836912873, 7604325260715233280440991522137135592581967246821324⟩
  | 4, 1 => ⟨-14864004907910093945358059740173035902810371061077218, 14881004597799033763892361940170075858391412271594015⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0300Geometry.ds, E8TAxisProd0300Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 21022763864346199167619842468126335283208593026 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0300CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0301GraphCenterA.qJetBox,
   E8TAxisProd0301GraphCenterB.qJetBox,
   E8TAxisProd0301GraphCenterC.qJetBox,
   E8TAxisProd0301GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0301GraphWholeA.qJetBox,
   E8TAxisProd0301GraphWholeB.qJetBox,
   E8TAxisProd0301GraphWholeC.qJetBox,
   E8TAxisProd0301GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨20050592399344024120729559764235030569639899887, 20050592399344024120729559764235142347728259960⟩
  | 0, 2 => ⟨61585907767788538517102315071156616930739737659, 61585907767788538517102315071157036573788753183⟩
  | 1, 1 => ⟨62346308194247493552524896086971585128513119178, 62346308194247493552524896086972336569388173790⟩
  | 0, 3 => ⟨130120874682998580613143491010719941231768435818, 130120874682998580613143491010721296989765574370⟩
  | 1, 2 => ⟨176133952378382706634050012978246015341723249522, 176133952378382706634050012978248426487203025408⟩
  | 2, 1 => ⟨178037454438828021481855802871171117381424948104, 178037454438828021481855802871175479187429065050⟩
  | 0, 4 => ⟨227455998241267097715167635053313523346993457555, 227455998241267097715167635053318096530349484849⟩
  | 1, 3 => ⟨341423158787986303290259547375817103419175985220, 341423158787986303290259547375825361164752734700⟩
  | 2, 2 => ⟨456356420976279188275206493685146406130756588144, 456356420976279188275206493685161549526077684035⟩
  | 3, 1 => ⟨460619511898189271459475980410394655177316324179, 460619511898189271459475980410422663101843691610⟩
  | 0, 5 => ⟨-895268503949206004472160628416033896690987491163254, 900459191365270028894750494250399273345911562683584⟩
  | 1, 4 => ⟨-1748670944424190551806484727769332123611247512375401, 1756465622597462249717751539036321474449472182526652⟩
  | 2, 3 => ⟨-3419307699060573050494576796873195430401276826418722, 3430518272490620106359936351286157203155205889922134⟩
  | 3, 2 => ⟨-6690702175802620398649375026737636228989495345074782, 6705408830618432363907195787015562863556018592181527⟩
  | 4, 1 => ⟨-13098757714815980254649331489791673711227925957034292, 13113813796786451559836637568934842198656589617254234⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0301Geometry.ds, E8TAxisProd0301Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18799453505390110685875375082408108131109616489 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0301CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0302GraphCenterA.qJetBox,
   E8TAxisProd0302GraphCenterB.qJetBox,
   E8TAxisProd0302GraphCenterC.qJetBox,
   E8TAxisProd0302GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0302GraphWholeA.qJetBox,
   E8TAxisProd0302GraphWholeB.qJetBox,
   E8TAxisProd0302GraphWholeC.qJetBox,
   E8TAxisProd0302GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨22324607333597570166650288461110446191311763401, 22324607333597570166650288461110568936818822373⟩
  | 0, 2 => ⟨68040285967019200584707603601134126547082034584, 68040285967019200584707603601134591880677307854⟩
  | 1, 1 => ⟨68809118480440621123943216203099672509236842048, 68809118480440621123943216203100508390466662264⟩
  | 0, 3 => ⟨142610939053441886508645612872028336223754839266, 142610939053441886508645612872029845055550030813⟩
  | 1, 2 => ⟨192770228679166404557622427277236719116050528537, 192770228679166404557622427277239409702274470775⟩
  | 2, 1 => ⟨194677184470206211421715105216604816468452951204, 194677184470206211421715105216609693210436951834⟩
  | 0, 4 => ⟨247330359263832538215766624125608081125593605274, 247330359263832538215766624125613190286807719689⟩
  | 1, 3 => ⟨370538329778515523352652590307115560493419484400, 370538329778515523352652590307124805659923645434⟩
  | 2, 2 => ⟨494703769157931241511346219538828968213206736457, 494703769157931241511346219538845948509044690428⟩
  | 3, 1 => ⟨498941352130881641446308830740505659864819454533, 498941352130881641446308830740537108279161184651⟩
  | 0, 5 => ⟨-1010895790800476343973373802252938386077611676511933, 1016718710940059260273691110612555753278812898903298⟩
  | 1, 4 => ⟨-1975771848345953108415260787207197411816340508133436, 1984529020053728293903688003375075600528850571144782⟩
  | 2, 3 => ⟨-3865727457222373546968829525532314428891488771560258, 3878335858573498753873051193407609279345687084591271⟩
  | 3, 2 => ⟨-7568770966113168475978048802829304780512166045273354, 7585322977937902008664185830883192920372852369472207⟩
  | 4, 1 => ⟨-14826695436581503457818937037217884310408215533590744, 14843648396421018408853190966540093037988002721402925⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0302Geometry.ds, E8TAxisProd0302Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20942329300782154174277535161765490461447263800 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0302CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0303GraphCenterA.qJetBox,
   E8TAxisProd0303GraphCenterB.qJetBox,
   E8TAxisProd0303GraphCenterC.qJetBox,
   E8TAxisProd0303GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0303GraphWholeA.qJetBox,
   E8TAxisProd0303GraphWholeB.qJetBox,
   E8TAxisProd0303GraphWholeC.qJetBox,
   E8TAxisProd0303GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19973711597561330976675828232953653954722762357, 19973711597561330976675828232953765504122450547⟩
  | 0, 2 => ⟨61423434261282996029497987517365247496962309215, 61423434261282996029497987517365666215706986578⟩
  | 1, 1 => ⟨62126407313408811073277183619575225622578453367, 62126407313408811073277183619575975383022347061⟩
  | 0, 3 => ⟨129836826207498821164211171550653682187862091608, 129836826207498821164211171550655034915509584020⟩
  | 1, 2 => ⟨175707598668050748288241044199375995908339268571, 175707598668050748288241044199378401598540027981⟩
  | 2, 1 => ⟨177467633284939205083404358680130600763766501953, 177467633284939205083404358680134952597535727319⟩
  | 0, 4 => ⟨227021686400497432271948861149739982155478422415, 227021686400497432271948861149744544760651988218⟩
  | 1, 3 => ⟨340742976956216961049556829761818330608917716875, 340742976956216961049556829761826569142965865346⟩
  | 2, 2 => ⟨455357728794428114945784017012635175930401662762, 455357728794428114945784017012650283881146514655⟩
  | 3, 1 => ⟨459300071015077280514771000530942798849220643835, 459300071015077280514771000530970740783529578998⟩
  | 0, 5 => ⟨-892993780964813893833577512696686472367713438400015, 898172423150538449111416886727411168965419305767629⟩
  | 1, 4 => ⟨-1744208166268324039504813888520309529708341214256979, 1751984527402198409707014810048011276754405422013445⟩
  | 2, 3 => ⟨-3410542086017556265922112350037111440817986097729140, 3421726005545509986128845002147618784397195265756390⟩
  | 3, 2 => ⟨-6673471607749692479419342986308011125885513170323125, 6688142467167283443743041924477810500028837486265628⟩
  | 4, 1 => ⟨-13064867401522073444905416161502907291552921999037512, 13079883578388895201192459017410683016922403596945637⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0303Geometry.ds, E8TAxisProd0303Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18726881905035641353744847876759203451569293935 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0303CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0304GraphCenterA.qJetBox,
   E8TAxisProd0304GraphCenterB.qJetBox,
   E8TAxisProd0304GraphCenterC.qJetBox,
   E8TAxisProd0304GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0304GraphWholeA.qJetBox,
   E8TAxisProd0304GraphWholeB.qJetBox,
   E8TAxisProd0304GraphWholeC.qJetBox,
   E8TAxisProd0304GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42480080389281227881508204183200091946164308008, 42480080389281227881508204183200312088442451210⟩
  | 0, 2 => ⟨122929833601288794926431583795061405790719690567, 122929833601288794926431583795062285193853598592⟩
  | 1, 1 => ⟨124118913492353231797030458976111907618264718098, 124118913492353231797030458976113513519855629901⟩
  | 0, 3 => ⟨245373866284105904210788290286117890774763400294, 245373866284105904210788290286120804537506893353⟩
  | 1, 2 => ⟨329494180893805442435616716149261529190968350809, 329494180893805442435616716149266800615598659601⟩
  | 2, 1 => ⟨332296028497562527445449204718639928411884391463, 332296028497562527445449204718649587901643072832⟩
  | 0, 4 => ⟨407030812901376975232610474687853530493340573459, 407030812901376975232610474687863650197021190603⟩
  | 1, 3 => ⟨603606885028633499341736649480111848857546503544, 603606885028633499341736649480130372017324571878⟩
  | 2, 2 => ⟨801516322884169575553259047123155888374099306063, 801516322884169575553259047123190206081181659778⟩
  | 3, 1 => ⟨807509004613929317118894280965566579648530384977, 807509004613929317118894280965630641425640344742⟩
  | 0, 5 => ⟨-2077209368003382334816724982360306065561493272989397, 2088142318447422300997656663518483585185941259198656⟩
  | 1, 4 => ⟨-4074011618727050707290108466497333233880604410165049, 4090512408661347049654154428876721062101528153032220⟩
  | 2, 3 => ⟨-7997876317258775375455371050493068131252370525110305, 8021688306261510776360979213647716668663355279455697⟩
  | 3, 2 => ⟨-15711158377127595871334718274229751055569257083665514, 15742462478004420717661117588997685606652549217253469⟩
  | 4, 1 => ⟨-30879127984182537224972649350204313542170164733745821, 30911239271002898263215931549341599466052628004298852⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0304Geometry.ds, E8TAxisProd0304Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39970691159684970255409288367235358351250135061 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0304CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0305GraphCenterA.qJetBox,
   E8TAxisProd0305GraphCenterB.qJetBox,
   E8TAxisProd0305GraphCenterC.qJetBox,
   E8TAxisProd0305GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0305GraphWholeA.qJetBox,
   E8TAxisProd0305GraphWholeB.qJetBox,
   E8TAxisProd0305GraphWholeC.qJetBox,
   E8TAxisProd0305GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38228013058205178258492136523485862916988672632, 38228013058205178258492136523486062302433093225⟩
  | 0, 2 => ⟨111592794381014288920379749167502253673603359422, 111592794381014288920379749167503043605418110915⟩
  | 1, 1 => ⟨112684961804659772366704865106638072183485784648, 112684961804659772366704865106639511082553897512⟩
  | 0, 3 => ⟨224528807765133358430842670237183469118191541833, 224528807765133358430842670237186075499519687646⟩
  | 1, 2 => ⟨301803406549482376337935671293207200564752544647, 301803406549482376337935671293211905096306629198⟩
  | 2, 1 => ⟨304397432070446521534567705511423029603126807982, 304397432070446521534567705511431634840094572485⟩
  | 0, 4 => ⟨375040784155518522865688400489038877798447910316, 375040784155518522865688400489047881824408799994⟩
  | 1, 3 => ⟨557041682355436724776038160108868171320152069083, 557041682355436724776038160108884621459319683714⟩
  | 2, 2 => ⟨740286447371191266717818417001018352685485672186, 740286447371191266717818417001048785234326560239⟩
  | 3, 1 => ⟨745864434923083614471971036259519888304906470657, 745864434923083614471971036259576621891276626646⟩
  | 0, 5 => ⟨-1854280740721601505153442028901958991837634526110363, 1864251446363201066638222085722093243828915833685385⟩
  | 1, 4 => ⟨-3634919290581901430839973870634525328156844285092547, 3649971844145110699016639154004221842948507176463517⟩
  | 2, 3 => ⟨-7132312617026227512974072762724259143682087750291706, 7154040821077206050970716751208242996001114537583121⟩
  | 3, 2 => ⟨-14003891455834721059971359356927767360074500542494487, 14032463022899208987902655374269102472971538182268864⟩
  | 4, 1 => ⟨-27509963656885881810307723667793728999644864305215477, 27539277349696697934338217499333868196932586995663647⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0305Geometry.ds, E8TAxisProd0305Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35951756101422322889103797173498534052296793529 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0305CertifiedArithmetic

end


