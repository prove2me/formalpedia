-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0552CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0552CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:44:18.038124+00:00
-- url     : https://prove2.me/theorems/ae089a14-81a8-4e39-a785-444e8b92e021
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0552CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0553CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0554CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0555CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0556CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0557CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0558CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0559CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0560CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0561CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0562CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0563CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0564CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0565CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0566CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0567CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0551GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0542GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0546GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0551GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0539GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0549GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0552GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0546GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0538Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0556GraphWholeA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0557Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0559GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0560GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0562GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0563GraphWholeD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0564GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0565GraphWholeA__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0565GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0567GraphCenterA__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0552GraphCenterA.qJetBox,
   E8TAxisProd0552GraphCenterB.qJetBox,
   E8TAxisProd0552GraphCenterC.qJetBox,
   E8TAxisProd0552GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0552GraphWholeA.qJetBox,
   E8TAxisProd0552GraphWholeB.qJetBox,
   E8TAxisProd0552GraphWholeC.qJetBox,
   E8TAxisProd0552GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6910717017612825559605678190160256003181373204, 6910717017612825559605678190160304447818326624⟩
  | 0, 2 => ⟨23149638075289387506041919015880450087418074887, 23149638075289387506041919015880613424324600044⟩
  | 1, 1 => ⟨23377494783446926290740260680437214240094387772, 23377494783446926290740260680437496418699412406⟩
  | 0, 3 => ⟨52889816251417083319161292710203643796938566747, 52889816251417083319161292710204152871855426758⟩
  | 1, 2 => ⟨72390253378039361843766939310686065545690980723, 72390253378039361843766939310686944424286232527⟩
  | 2, 1 => ⟨73015066724736136537284943714106318469989717561, 73015066724736136537284943714107877178721845911⟩
  | 0, 4 => ⟨100159654390070410951312526640154590609838368162, 100159654390070410951312526640156255722026159228⟩
  | 1, 3 => ⟨153184078775374681695048310536470269904653838746, 153184078775374681695048310536473207337292124012⟩
  | 2, 2 => ⟨206567627399560511497118621616926034284665838549, 206567627399560511497118621616931336804343823580⟩
  | 3, 1 => ⟨208102280777042426449951540937222832661126412945, 208102280777042426449951540937232507514960987569⟩
  | 0, 5 => ⟨-244653762993806433307221283139245741201126983370275, 246375897323991572305458059846803157689613059338259⟩
  | 1, 4 => ⟨-473946091365780233477674913774259412626212232159162, 476489479716443743089385086106897513120069133360923⟩
  | 2, 3 => ⟨-919649130573045009216660117814030128959632524084433, 923267528964517825584458954466445406733313536632022⟩
  | 3, 2 => ⟨-1786156243524308144515378488333912118014843397901870, 1790875449804538914741864555655592230643004983677579⟩
  | 4, 1 => ⟨-3471158116291726322932073445385735760492272870518165, 3475988490391458318215907671692887593247901788036704⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0552Geometry.ds, E8TAxisProd0552Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6447140387860816483246913383575044883400811045 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0552CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0553GraphCenterA.qJetBox,
   E8TAxisProd0553GraphCenterB.qJetBox,
   E8TAxisProd0553GraphCenterC.qJetBox,
   E8TAxisProd0553GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0553GraphWholeA.qJetBox,
   E8TAxisProd0553GraphWholeB.qJetBox,
   E8TAxisProd0553GraphWholeC.qJetBox,
   E8TAxisProd0553GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6116164348108760361317129252639956531340781946, 6116164348108760361317129252640000904521973035⟩
  | 0, 2 => ⟨20677514382322183956390496368079144858205669991, 20677514382322183956390496368079292406146577053⟩
  | 1, 1 => ⟨20883883015676473533645415509474751632455116661, 20883883015676473533645415509475005289473479407⟩
  | 0, 3 => ⟨47633297477246606947252726376917387341552704418, 47633297477246606947252726376917845013511422555⟩
  | 1, 2 => ⟨65297655934631628173799905680134984881613518817, 65297655934631628173799905680135771830475239668⟩
  | 2, 1 => ⟨65869380885338544581178931696243647518766198780, 65869380885338544581178931696245039695965967944⟩
  | 0, 4 => ⟨91014086832708858008821490488126142736627033806, 91014086832708858008821490488127634322603299181⟩
  | 1, 3 => ⟨139536354463200101741859698207654460059010193699, 139536354463200101741859698207657082799992276204⟩
  | 2, 2 => ⟨188392480593917142151115184693061607114607616325, 188392480593917142151115184693066331764562556625⟩
  | 3, 1 => ⟨189813558128527920012585365428709381804586082716, 189813558128527920012585365428717987563070878098⟩
  | 0, 5 => ⟨-208683374558634734949643961293512409852385386021116, 210206222766972652066599930455809310690824162331089⟩
  | 1, 4 => ⟨-403767328517876173880870098430667203122642641079688, 406011152544103536767106776595075424716384020562116⟩
  | 2, 3 => ⟨-782600919184041627590185724627026304755979495472813, 785788701286941453099368343234811606305681754534856⟩
  | 3, 2 => ⟨-1518363664278053071853004797147289009237998383094289, 1522518819274673036999383357571581216577753942552762⟩
  | 4, 1 => ⟨-2947663118419968120449415247951620088314287226774281, 2951918894661605917492171305551335243155818158385528⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0553Geometry.ds, E8TAxisProd0553Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5702636682271696433751490306101258911353721647 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0553CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0554GraphCenterA.qJetBox,
   E8TAxisProd0554GraphCenterB.qJetBox,
   E8TAxisProd0554GraphCenterC.qJetBox,
   E8TAxisProd0554GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0554GraphWholeA.qJetBox,
   E8TAxisProd0554GraphWholeB.qJetBox,
   E8TAxisProd0554GraphWholeC.qJetBox,
   E8TAxisProd0554GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6881821257600445688085605814845458756571946019, 6881821257600445688085605814845507105601184771⟩
  | 0, 2 => ⟨23083604000823213494857171172386525675541785709, 23083604000823213494857171172386688654255496639⟩
  | 1, 1 => ⟨23287126555518075880302600214183633817099865653, 23287126555518075880302600214183915361960998181⟩
  | 0, 3 => ⟨52764745980593128226504564854280781236087038816, 52764745980593128226504564854281289176302861481⟩
  | 1, 2 => ⟨72198980290522920272194370564876705336146918618, 72198980290522920272194370564877582217524831039⟩
  | 2, 1 => ⟨72757165805339888582272467017476891915788283139, 72757165805339888582272467017478447028972339716⟩
  | 0, 4 => ⟨99952840947658214424358052521936909764961282470, 99952840947658214424358052521938571060860069767⟩
  | 1, 3 => ⟨152852963231032180219602951043708682882140960658, 152852963231032180219602951043711613505107464897⟩
  | 2, 2 => ⟨206074001566817996613571406656377023578843680636, 206074001566817996613571406656382313676130852287⟩
  | 3, 1 => ⟨207445286373559407908311300584202148460291413373, 207445286373559407908311300584211800407069239543⟩
  | 0, 5 => ⟨-243883877630064355494098331448908213034803400219699, 245602000854990158563443984832903774796270326476192⟩
  | 1, 4 => ⟨-472444026516018675357105966052610877833135514746855, 474981376015070576007340630623077639363181839367452⟩
  | 2, 3 => ⟨-916714453073768616223072816558321670473174919995357, 920324200690419598370470212153190192826242633831298⟩
  | 3, 2 => ⟨-1780417451396567268403548849332792713682479857314342, 1785125357352677785575092228302854254279418323085001⟩
  | 4, 1 => ⟨-3459928735344735976371972250656138749667614276923971, 3464747391798974331566290280262889631936449672671231⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0554Geometry.ds, E8TAxisProd0554Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6420006593952740371397957906758305905980530312 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0554CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0555GraphCenterA.qJetBox,
   E8TAxisProd0555GraphCenterB.qJetBox,
   E8TAxisProd0555GraphCenterC.qJetBox,
   E8TAxisProd0555GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0555GraphWholeA.qJetBox,
   E8TAxisProd0555GraphWholeB.qJetBox,
   E8TAxisProd0555GraphWholeC.qJetBox,
   E8TAxisProd0555GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6090354639032989102983699383936828495697767138, 6090354639032989102983699383936872781783271492⟩
  | 0, 2 => ⟨20618043815767408563045414540611890170286535522, 20618043815767408563045414540612037394930993247⟩
  | 1, 1 => ⟨20802369879117877305136313352645166247075779914, 20802369879117877305136313352645419334201831608⟩
  | 0, 3 => ⟨47519648563287303041235542699460959666516188943, 47519648563287303041235542699461416316274192608⟩
  | 1, 2 => ⟨65123426063296630641386954497031615307565446672, 65123426063296630641386954497032400462297851880⟩
  | 2, 1 => ⟨65634174945502758630243328550598989477243680002, 65634174945502758630243328550600378430137387557⟩
  | 0, 4 => ⟨90824232935869164474475597194046074725645578238, 90824232935869164474475597194047562874531148351⟩
  | 1, 3 => ⟨139231534411216149151089534038682221478779950290, 139231534411216149151089534038684838099800309531⟩
  | 2, 2 => ⟨187937170213431547844242822397482498477468177423, 187937170213431547844242822397487211976807657126⟩
  | 3, 1 => ⟨189206950900856233206324444508413508733656435792, 189206950900856233206324444508422093950563714428⟩
  | 0, 5 => ⟨-208018110457665265505113876540589399691275772748624, 209537393241376425187352902037795319556485254670523⟩
  | 1, 4 => ⟨-402470481062657537918433553721017797688018154462613, 404708969309335344522318874728318188268374043911655⟩
  | 2, 3 => ⟨-780069208751076530152909713868543780906756753384416, 783249362195462287607353064964374109318711957394252⟩
  | 3, 2 => ⟨-1513416708051669152888787389510807407331729941426262, 1517561863403062393577121409692646538532345750956702⟩
  | 4, 1 => ⟨-2937990539366063024825146227841606289136552415145944, 2942235767673446073290063167059851353110922254135290⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0555Geometry.ds, E8TAxisProd0555Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5678414552456041856266941312030266999862448972 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0555CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0556GraphCenterA.qJetBox,
   E8TAxisProd0556GraphCenterB.qJetBox,
   E8TAxisProd0556GraphCenterC.qJetBox,
   E8TAxisProd0556GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0556GraphWholeA.qJetBox,
   E8TAxisProd0556GraphWholeB.qJetBox,
   E8TAxisProd0556GraphWholeC.qJetBox,
   E8TAxisProd0556GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5406750204353213479799839204692420310005898774, 5406750204353213479799839204692460992712230171⟩
  | 0, 2 => ⟨18448851093541306316370126663311638445890193809, 18448851093541306316370126663311771796236939147⟩
  | 1, 1 => ⟨18635567757501066346731887526348706339379309818, 18635567757501066346731887526348934417492285479⟩
  | 0, 3 => ⟨42847884663307103415599572765902675511053544008, 42847884663307103415599572765903086996567831716⟩
  | 1, 2 => ⟨58832760098192501178306517110193167606793557256, 58832760098192501178306517110193872133147051583⟩
  | 2, 1 => ⟨59355346868017875755133668025566691203977385872, 59355346868017875755133668025567934322778045310⟩
  | 0, 4 => ⟨82598799619056380524948885757012319468622586205, 82598799619056380524948885757013655064325227367⟩
  | 1, 3 => ⟨126953657925295184082747457177810741044000528630, 126953657925295184082747457177813081333264254173⟩
  | 2, 2 => ⟨171618630228657603258467415389781204618972433952, 171618630228657603258467415389785411227894447096⟩
  | 3, 1 => ⟨172933365169644038595913768060216579699565078584, 172933365169644038595913768060224228142602913474⟩
  | 0, 5 => ⟨-177530827571577015601258752602861678224362595462906, 178877365317011983553027394035259544719035073158888⟩
  | 1, 4 => ⟨-343042792383398399400478296366853376822705728678686, 345022212969022164173299374319734888516515044881258⟩
  | 2, 3 => ⟨-664118036629380018548008790102572447337411621782927, 666926369505485196335102329697643047431551959590189⟩
  | 3, 2 => ⟨-1287045981048902574648397554883375333456931197905048, 1290704588540074755431239856473733338829742127750960⟩
  | 4, 1 => ⟨-2495858665206878337011142826304258941993413731444651, 2499608743075212534112786259111268839868532181487789⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0556Geometry.ds, E8TAxisProd0556Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5038266667062668316738732481661205454911302751 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0556CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0557GraphCenterA.qJetBox,
   E8TAxisProd0557GraphCenterB.qJetBox,
   E8TAxisProd0557GraphCenterC.qJetBox,
   E8TAxisProd0557GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0557GraphWholeA.qJetBox,
   E8TAxisProd0557GraphWholeB.qJetBox,
   E8TAxisProd0557GraphWholeC.qJetBox,
   E8TAxisProd0557GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4774056422176191160405625114450603679877138689, 4774056422176191160405625114450641015740572408⟩
  | 0, 2 => ⟨16441974704189575587810305331402580270949282872, 16441974704189575587810305331402700854239645416⟩
  | 1, 1 => ⟨16610738112913484587149904965166597513691951955, 16610738112913484587149904965166802653871867554⟩
  | 0, 3 => ⟨38496605183612850242206177233359583064217777921, 38496605183612850242206177233359953060226510818⟩
  | 1, 2 => ⟨52946897591190451606596820902662888321349388256, 52946897591190451606596820902663518973745589042⟩
  | 2, 1 => ⟨53424044835459776830264750720566536049417305371, 53424044835459776830264750720567645801319375667⟩
  | 0, 4 => ⟨74863474407859139617764165724834747362275731136, 74863474407859139617764165724835942821254800829⟩
  | 1, 3 => ⟨115364351209776017193653900124893628930641169526, 115364351209776017193653900124895715892351710756⟩
  | 2, 2 => ⟨156153024755731855217044663615056866605600870657, 156153024755731855217044663615060609181686580994⟩
  | 3, 1 => ⟨157368191367813732411890764375834975495811903771, 157368191367813732411890764375841767452803308341⟩
  | 0, 5 => ⟨-150660644278885855356071898468504797214632672335964, 151852849313709515229003828218581359939493837506920⟩
  | 1, 4 => ⟨-290714948935779322204563959246676994708234020511472, 292462124280445555546866700937039500080297716114849⟩
  | 2, 3 => ⟨-562110263584376919356327498044616845524936121632774, 564584400518912986105421385675167400378902459304425⟩
  | 3, 2 => ⟨-1088069518928730901722023484370123208722524557833529, 1091290113233802868060382296768077271800987890486765⟩
  | 4, 1 => ⟨-2107566095064011561558316148067039705948038669788671, 2110869862237899082261182282544192572173364017715353⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0557Geometry.ds, E8TAxisProd0557Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4446064327357573192418991998267708673695803004 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0557CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0558GraphCenterA.qJetBox,
   E8TAxisProd0558GraphCenterB.qJetBox,
   E8TAxisProd0558GraphCenterC.qJetBox,
   E8TAxisProd0558GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0558GraphWholeA.qJetBox,
   E8TAxisProd0558GraphWholeB.qJetBox,
   E8TAxisProd0558GraphWholeC.qJetBox,
   E8TAxisProd0558GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5383722588522726074783903694195822281966381852, 5383722588522726074783903694195862885279756232⟩
  | 0, 2 => ⟨18395355722664998423582332687207887807206392915, 18395355722664998423582332687208020865701319374⟩
  | 1, 1 => ⟨18562125916885453251980965755565724544940718716, 18562125916885453251980965755565952110590077731⟩
  | 0, 3 => ⟨42744745009668784463636603303292269462762125031, 42744745009668784463636603303292680027529200606⟩
  | 1, 2 => ⟨58674243289787941492459714743014270705271753016, 58674243289787941492459714743014973620378256814⟩
  | 2, 1 => ⟨59141085897324170741095978430683283097592338774, 59141085897324170741095978430684523326029087119⟩
  | 0, 4 => ⟨82424699370971318461978464319551063250055071503, 82424699370971318461978464319552395751845772202⟩
  | 1, 3 => ⟨126673323513429971650159109849343925285735082686, 126673323513429971650159109849346260078720389285⟩
  | 2, 2 => ⟨171199059818796481858724685383320107519841996797, 171199059818796481858724685383324304127550720678⟩
  | 3, 1 => ⟨172373800738807413708902759042413950056974799169, 172373800738807413708902759042421580095234637707⟩
  | 0, 5 => ⟨-176955959407328063687720063812898103909937640126025, 178299323238577809916297336514213324247828047294350⟩
  | 1, 4 => ⟨-341923183671084078615887209305387885206379492121275, 343897846472270457344129108588714316465407402851156⟩
  | 2, 3 => ⟨-661934168683482824236866400166568590132349679272747, 664735672621535876966820562597143495405971640285213⟩
  | 3, 2 => ⟨-1282782136355194584113251856136837216155515915223560, 1286431718846628770011638058584306355206013707703458⟩
  | 4, 1 => ⟨-2487528295183280052910772859822877391258892155619156, 2491268646071618990639903043476192423634880583396979⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0558Geometry.ds, E8TAxisProd0558Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5016667997614215857712529079455830599610556051 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0558CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0559GraphCenterA.qJetBox,
   E8TAxisProd0559GraphCenterB.qJetBox,
   E8TAxisProd0559GraphCenterC.qJetBox,
   E8TAxisProd0559GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0559GraphWholeA.qJetBox,
   E8TAxisProd0559GraphWholeB.qJetBox,
   E8TAxisProd0559GraphWholeC.qJetBox,
   E8TAxisProd0559GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4753534004912118288755128504315895183002290840, 4753534004912118288755128504315932446444962522⟩
  | 0, 2 => ⟨16393912393251362824978957895763225080433462828, 16393912393251362824978957895763345400205007170⟩
  | 1, 1 => ⟨16544644552224695377333778239898135243515809270, 16544644552224695377333778239898339922877128723⟩
  | 0, 3 => ⟨38403125540612979748780687573867558584899704774, 38403125540612979748780687573867927751638547340⟩
  | 1, 2 => ⟨52802853164684728841550359611193022451860130044, 52802853164684728841550359611193651657660986273⟩
  | 2, 1 => ⟨53229095032261174358341669738220484621906933338, 53229095032261174358341669738221591783759842198⟩
  | 0, 4 => ⟨74704003590053788357776526348199896642180862104, 74704003590053788357776526348201089317718024589⟩
  | 1, 3 => ⟨115106812896713769717158683977531272747170693108, 115106812896713769717158683977533354776343628855⟩
  | 2, 2 => ⟨155766787833100642037964884894247349506646356708, 155766787833100642037964884894251083119842502329⟩
  | 3, 1 => ⟨156852543382385621184888201935115524803352152198, 156852543382385621184888201935122300284830271298⟩
  | 0, 5 => ⟨-150165998430252566714567326744488257252952873603280, 151355409618236986234336970714398987176599152803506⟩
  | 1, 4 => ⟨-289752499371306979236322407467192052165091329506257, 291495457937678795748070638088186929500685671410919⟩
  | 2, 3 => ⟨-560234584335422299260501346342563969324702849455270, 562702620828349623109178511930180040878155804792225⟩
  | 3, 2 => ⟨-1084410440489860269538888290162188321380186660091140, 1087622887027500362038936037748496203320033130014885⟩
  | 4, 1 => ⟨-2100423082708169902590374436314928970746865370689454, 2103717875588288559047614697726636456624928081382539⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0559Geometry.ds, E8TAxisProd0559Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4426826556853606879595831001580037680197203411 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0559CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0560GraphCenterA.qJetBox,
   E8TAxisProd0560GraphCenterB.qJetBox,
   E8TAxisProd0560GraphCenterC.qJetBox,
   E8TAxisProd0560GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0560GraphWholeA.qJetBox,
   E8TAxisProd0560GraphWholeB.qJetBox,
   E8TAxisProd0560GraphWholeC.qJetBox,
   E8TAxisProd0560GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4247118172356867811218649297974144590237878678, 4247118172356867811218649297974179021867459955⟩
  | 0, 2 => ⟨14723476455278529571013872312218756567135700272, 14723476455278529571013872312218866146717260431⟩
  | 1, 1 => ⟨14908596459533012003040605405351940424233929882, 14908596459533012003040605405352125827793987796⟩
  | 0, 3 => ⟨34714744447808140244727337048305168354800956306, 34714744447808140244727337048305502596217917144⟩
  | 1, 2 => ⟨47856980629259493402096601304496744137223964562, 47856980629259493402096601304497311222046595610⟩
  | 2, 1 => ⟨48385466872786443179969756861353213391521991460, 48385466872786443179969756861354208552451669641⟩
  | 0, 4 => ⟨68053703828041464875613792120507553595739314325, 68053703828041464875613792120508628398156845363⟩
  | 1, 3 => ⟨105175449779635707736038895042565025055757081529, 105175449779635707736038895042566894119586900081⟩
  | 2, 2 => ⟨142621049245173922713373612405590148443588301125, 142621049245173922713373612405593492320082181273⟩
  | 3, 1 => ⟨143983010998255944839067798888085223643811259896, 143983010998255944839067798888091280557245360349⟩
  | 0, 5 => ⟨-128404144650053207810195852362125209346400828383820, 129464751246721190043362468876762529356738066543976⟩
  | 1, 4 => ⟨-247413271450832653814408590625974302039327531724050, 248962557111216976180349440411321802091632708053296⟩
  | 2, 3 => ⟨-477776964293645604782914910375220158090263345330518, 479966506590512053116221199746269658417059338272087⟩
  | 3, 2 => ⟨-923722658191042051464509817343659731497131088169172, 926570609216127202318883896101475507509836070567810⟩
  | 4, 1 => ⟨-1787154107924176913517111938149848221568814675659202, 1790079449670394662423433636978407583490990255860579⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0560Geometry.ds, E8TAxisProd0560Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3953166825054569896979536800771377158016748169 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0560CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0561GraphCenterA.qJetBox,
   E8TAxisProd0561GraphCenterB.qJetBox,
   E8TAxisProd0561GraphCenterC.qJetBox,
   E8TAxisProd0561GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0561GraphWholeA.qJetBox,
   E8TAxisProd0561GraphWholeB.qJetBox,
   E8TAxisProd0561GraphWholeC.qJetBox,
   E8TAxisProd0561GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3741498013891970165694888933614386220929510953, 3741498013891970165694888933614417883957377617⟩
  | 0, 2 => ⟨13092821128792539608647295269036689116528236696, 13092821128792539608647295269036788324326382209⟩
  | 1, 1 => ⟨13259804987433628225482476913634476601950621147, 13259804987433628225482476913634643479696973818⟩
  | 0, 3 => ⟨31114298429814027777310814917737150876821396542, 31114298429814027777310814917737451520336366295⟩
  | 1, 2 => ⟨42971366125681948511277233269294877424589927654, 42971366125681948511277233269295384972818107820⟩
  | 2, 1 => ⟨43452829674746146721536628483758008736345136267, 43452829674746146721536628483758896803248279852⟩
  | 0, 4 => ⟨61515036456829419027161702681024130466127664716, 61515036456829419027161702681025092009147564136⟩
  | 1, 3 => ⟨95336592850655621721273872121583630335519600612, 95336592850655621721273872121585295411240900107⟩
  | 2, 2 => ⟨129458095686096693881851259929969736007188351199, 129458095686096693881851259929972707277564451268⟩
  | 3, 1 => ⟨130714223014486879564386984705180306368276840461, 130714223014486879564386984705185677333923665807⟩
  | 0, 5 => ⟨-108492528227922833929916892895920397321372128345066, 109431559206551740813681916881616759265044156970201⟩
  | 1, 4 => ⟨-208714797602492114898117060002774266995507416003921, 210081463268733790716098875283907700044316374720943⟩
  | 2, 3 => ⟨-402482701710789044907711373079597754044086130582738, 404409766640303404087815131212849404601665000475165⟩
  | 3, 2 => ⟨-777129452509487483878675127871520201697919424546669, 779633588650552784528247834211183013967614564161438⟩
  | 4, 1 => ⟨-1501620572371349682326051149260318960022081599107088, 1504195492972527804493287811776470473552660293166969⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0561Geometry.ds, E8TAxisProd0561Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3480391633380678179173106668260572105531269020 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0561CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0562GraphCenterA.qJetBox,
   E8TAxisProd0562GraphCenterB.qJetBox,
   E8TAxisProd0562GraphCenterC.qJetBox,
   E8TAxisProd0562GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0562GraphWholeA.qJetBox,
   E8TAxisProd0562GraphWholeB.qJetBox,
   E8TAxisProd0562GraphWholeC.qJetBox,
   E8TAxisProd0562GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4228740925540894933275010275020707719046286114, 4228740925540894933275010275020742084305850021⟩
  | 0, 2 => ⟨14680136153522242527951580616250517300018290368, 14680136153522242527951580616250626640578632070⟩
  | 1, 1 => ⟨14848857340257372280531818932851035015667471201, 14848857340257372280531818932851220003015012277⟩
  | 0, 3 => ⟨34629768870099210884895998102853029060258686333, 34629768870099210884895998102853362551719040767⟩
  | 1, 2 => ⟨47725659635353841750039215818046939244380007274, 47725659635353841750039215818047505025291855088⟩
  | 2, 1 => ⟨48207413499224271421551053743904927577655875515, 48207413499224271421551053743905920408640118911⟩
  | 0, 4 => ⟨67907266149938023026124117319027178641512694495, 67907266149938023026124117319028250932336100425⟩
  | 1, 3 => ⟨104938216536231838729593602172132806642923467697, 104938216536231838729593602172134671268056829605⟩
  | 2, 2 => ⟨142264467463031487799277524800217995432644887297, 142264467463031487799277524800221331256105760835⟩
  | 3, 1 => ⟨143506260620430747332580365853521788393177368551, 143506260620430747332580365853527830521928318726⟩
  | 0, 5 => ⟨-127977060482338147045600290297676795605778099651411, 129035173070583725907187503722627582465000844345632⟩
  | 1, 4 => ⟨-246583117998669484281364132104015481366823048272993, 248128623224708512004942695361901870080534614314431⟩
  | 2, 3 => ⟨-476160573327285772129227997233157549698942634432153, 478344619287391753690454195536240548988447798804580⟩
  | 3, 2 => ⟨-920572082037087938837537246887156535760633284600971, 923412633668397546040216954735099893941668423225816⟩
  | 4, 1 => ⟨-1781008843380155262400952055827866749764471214970837, 1783925876007167269093334624339920214252248126746242⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0562Geometry.ds, E8TAxisProd0562Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3935949526557424186808020728202552344418319141 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0562CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0563GraphCenterA.qJetBox,
   E8TAxisProd0563GraphCenterB.qJetBox,
   E8TAxisProd0563GraphCenterC.qJetBox,
   E8TAxisProd0563GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0563GraphWholeA.qJetBox,
   E8TAxisProd0563GraphWholeB.qJetBox,
   E8TAxisProd0563GraphWholeC.qJetBox,
   E8TAxisProd0563GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3725156275513096472791776299760355376216544198, 3725156275513096472791776299760386978615153699⟩
  | 0, 2 => ⟨13053976279518018335945661057223807586245791734, 13053976279518018335945661057223906578120863690⟩
  | 1, 1 => ⟨13206165204839685563628468500623268675711816229, 13206165204839685563628468500623435179174257291⟩
  | 0, 3 => ⟨31037488283824721242455641462058339720747958114, 31037488283824721242455641462058639688917307925⟩
  | 1, 2 => ⟨42852331322579356032972459362051907871269614284, 42852331322579356032972459362052414249445246096⟩
  | 2, 1 => ⟨43291211820294140099205632408485622071746446775, 43291211820294140099205632408486508052265402415⟩
  | 0, 4 => ⟨61381239307408853721447484478411697940269634881, 61381239307408853721447484478412657225873610699⟩
  | 1, 3 => ⟨95119162664403459881735559088448229778303498550, 95119162664403459881735559088449890875833875105⟩
  | 2, 2 => ⟨129130582117986283084402759885534635800650460258, 129130582117986283084402759885537599864883762060⟩
  | 3, 1 => ⟨130275855727214804316573901665919978143706419546, 130275855727214804316573901665925335896075123068⟩
  | 0, 5 => ⟨-108127603739213115402883768587809820330537354278962, 109064409196133535159654771188115484865939661660466⟩
  | 1, 4 => ⟨-208006261611231620566118896701600985399964030938381, 209369546256952207223769691699062251585140888329260⟩
  | 2, 3 => ⟨-401104501868188943691984696212606976574164951957344, 403026629416624061634082455183760672430012549001725⟩
  | 3, 2 => ⟨-774445699557305812520913746243977756416697992558824, 776943132142198752922932720811827047030872355204742⟩
  | 4, 1 => ⟨-1496390689884942199485638705047014504347754796170378, 1498957929012023711019233377143670919982038673403625⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0563Geometry.ds, E8TAxisProd0563Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3465090334164103612113819450732741735099760674 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0563CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0564GraphCenterA.qJetBox,
   E8TAxisProd0564GraphCenterB.qJetBox,
   E8TAxisProd0564GraphCenterC.qJetBox,
   E8TAxisProd0564GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0564GraphWholeA.qJetBox,
   E8TAxisProd0564GraphWholeB.qJetBox,
   E8TAxisProd0564GraphWholeC.qJetBox,
   E8TAxisProd0564GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3292046560400264146887270747394722053858272586, 3292046560400264146887270747394751201791653812⟩
  | 0, 2 => ⟨11629476236601621394194179093002992598312269519, 11629476236601621394194179093003082477320427987⟩
  | 1, 1 => ⟨11779946979320725025328210720999717587001246785, 11779946979320725025328210720999867854436908374⟩
  | 0, 3 => ⟨27852755092995127426990449976651256787061643482, 27852755092995127426990449976651527269760983998⟩
  | 1, 2 => ⟨38539401576580858703395987690833338182891007585, 38539401576580858703395987690833792422697224032⟩
  | 2, 1 => ⟨38977521703190546934107237197616049896592340962, 38977521703190546934107237197616842256474200451⟩
  | 0, 4 => ⟨55525948813248293665849587385623578321230427953, 55525948813248293665849587385624438306096849976⟩
  | 1, 3 => ⟨86305234097301001977349914598465604154724027091, 86305234097301001977349914598467086677787256312⟩
  | 2, 2 => ⟨117362014194737011426178871627209124801192849256, 117362014194737011426178871627211763114783868197⟩
  | 3, 1 => ⟨118519150635525654015531579659527088560959371939, 118519150635525654015531579659531847408010382071⟩
  | 0, 5 => ⟨-91499449342745876037065139590172835127039622478065, 92330794096004229275180696722032672954845318764785⟩
  | 1, 4 => ⟨-175725532534509814050950092576099377986735271761194, 176930661592921507431184380937687913870724651244433⟩
  | 2, 3 => ⟨-338364572274671464396008831833835331234421615700979, 340059661404755040384438855060398964556903079490323⟩
  | 3, 2 => ⟨-652424565859340296857046844363689119042548177756839, 654624941788964922800569171745940109546839077460486⟩
  | 4, 1 => ⟨-1258970944568570046632415879124125314459734384299099, 1261236122828797390703355182745265479575187745194264⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0564Geometry.ds, E8TAxisProd0564Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3060364853059446607359241539317879905146728549 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0564CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0565GraphCenterA.qJetBox,
   E8TAxisProd0565GraphCenterB.qJetBox,
   E8TAxisProd0565GraphCenterC.qJetBox,
   E8TAxisProd0565GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0565GraphWholeA.qJetBox,
   E8TAxisProd0565GraphWholeB.qJetBox,
   E8TAxisProd0565GraphWholeC.qJetBox,
   E8TAxisProd0565GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2892979924207190874657729769047195764801864153, 2892979924207190874657729769047222626466297047⟩
  | 0, 2 => ⟨10317811854943840175451987199230299344494994418, 10317811854943840175451987199230380831816156842⟩
  | 1, 1 => ⟨10453264623708399272191000440949595046394081767, 10453264623708399272191000440949730421316188363⟩
  | 0, 3 => ⟨24902103378323309663734147334368133483202109429, 24902103378323309663734147334368376896663192264⟩
  | 1, 2 => ⟨34524059762378034143353096224547206391320712523, 34524059762378034143353096224547612916124207045⟩
  | 2, 1 => ⟨34922276685249070721679012648365375282590072416, 34922276685249070721679012648366082147805873728⟩
  | 0, 4 => ⟨50047629844852896559003332384660928825967458857, 50047629844852896559003332384661697811181082979⟩
  | 1, 3 => ⟨78025817970310137364368373422021349455806293782, 78025817970310137364368373422022668749317816286⟩
  | 2, 2 => ⟨106260430493016780785796008185466852558893971973, 106260430493016780785796008185469193626717878885⟩
  | 3, 1 => ⟨107325042028188511840889673316228257522586287139, 107325042028188511840889673316232470687757563548⟩
  | 0, 5 => ⟨-77324434639482466591759017153068177384372438966923, 78051899498607346753275318063360990044517294964824⟩
  | 1, 4 => ⟨-148237195345268189777665052854973056520156316159128, 149285841195016307348473618079345643097615733396731⟩
  | 2, 3 => ⟨-284990918224987350208766193222898860846654007793130, 286460507128230054142006301171094211521342467814381⟩
  | 3, 2 => ⟨-548714015432379762864932251219003408659676330865732, 550618368443015643430953558738465877383984756051596⟩
  | 4, 1 => ⟨-1057355209926190890685682245935860483108833178756557, 1059317799729458472473413455167932961844147481699086⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0565Geometry.ds, E8TAxisProd0565Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2687610784508518087452322931776854980897237743 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0565CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0566GraphCenterA.qJetBox,
   E8TAxisProd0566GraphCenterB.qJetBox,
   E8TAxisProd0566GraphCenterC.qJetBox,
   E8TAxisProd0566GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0566GraphWholeA.qJetBox,
   E8TAxisProd0566GraphWholeB.qJetBox,
   E8TAxisProd0566GraphWholeC.qJetBox,
   E8TAxisProd0566GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3277531457004515789054503913462849865055265013, 3277531457004515789054503913462878957560017239⟩
  | 0, 2 => ⟨11594703640576664996252117962594018782777532916, 11594703640576664996252117962594108466671044441⟩
  | 1, 1 => ⟨11731840101460743525655401839010467134668325822, 11731840101460743525655401839010617065507667779⟩
  | 0, 3 => ⟨27783423979740080231979497643948927584901235756, 27783423979740080231979497643949197459484883931⟩
  | 1, 2 => ⟨38431644461668354406571309732604976213850574874, 38431644461668354406571309732605429404013730482⟩
  | 2, 1 => ⟨38831007022202242564351222350206435350712606769, 38831007022202242564351222350207225843026970685⟩
  | 0, 4 => ⟨55403871343057450280851082825090029710711585644, 55403871343057450280851082825090887667795552316⟩
  | 1, 3 => ⟨86106215148127419474523004263422138705216086949, 86106215148127419474523004263423617665664808877⟩
  | 2, 2 => ⟨117061578250910610423264110881014938167673610278, 117061578250910610423264110881017570038825106907⟩
  | 3, 1 => ⟨118116574486108983892332287192440984505353726679, 118116574486108983892332287192445731555246970591⟩
  | 0, 5 => ⟨-91188438480087799698065635551678496327020532299277, 92017794016099342149525153072011857634377996159242⟩
  | 1, 4 => ⟨-175122378141062396944405835215640971516476683596037, 176324477552663893463379184455265605206725798195298⟩
  | 2, 3 => ⟨-337192572823845530887628187342405436805609218568949, 338883216232024393353099294266715566492801122336011⟩
  | 3, 2 => ⟨-650144568438026986864363277437300700607434778744854, 652338853258895702006557089717198978553655699128574⟩
  | 4, 1 => ⟨-1254532055550099035771686226807190520435915407424808, 1256790106477607356047796431913880315454408863792594⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0566Geometry.ds, E8TAxisProd0566Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3046781931320392078755686635081755951221491089 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0566CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0567GraphCenterA.qJetBox,
   E8TAxisProd0567GraphCenterB.qJetBox,
   E8TAxisProd0567GraphCenterC.qJetBox,
   E8TAxisProd0567GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0567GraphWholeA.qJetBox,
   E8TAxisProd0567GraphWholeB.qJetBox,
   E8TAxisProd0567GraphWholeC.qJetBox,
   E8TAxisProd0567GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2880102097874285636568777285225694569875418436, 2880102097874285636568777285225721380823969183⟩
  | 0, 2 => ⟨10286723296454014265111591847829036447308940723, 10286723296454014265111591847829117758259702972⟩
  | 1, 1 => ⟨10410170459278378514759037864711652229909088533, 10410170459278378514759037864711787302104013082⟩
  | 0, 3 => ⟨24839613376359693042859866678131932139950878569, 24839613376359693042859866678132175005857318938⟩
  | 1, 2 => ⟨34426641224602402076226969292242629432578568866, 34426641224602402076226969292243035016009579663⟩
  | 2, 1 => ⟨34789623226335449039665859084472354800447718147, 34789623226335449039665859084473059994597138064⟩
  | 0, 4 => ⟨49936409223534831883104575479563964438669606840, 49936409223534831883104575479564731603417054574⟩
  | 1, 3 => ⟨77843903013472381955269559292766323667161724112, 77843903013472381955269559292767639772795037837⟩
  | 2, 2 => ⟨105985199286779990509800689887070880000682467235, 105985199286779990509800689887073215314168007048⟩
  | 3, 1 => ⟨106955816138839823255228021871144875369973125048, 106955816138839823255228021871149078013010504435⟩
  | 0, 5 => ⟨-77064324883977312660194419868575972522398852726862, 77789891397063515275198668938318713393887021346517⟩
  | 1, 4 => ⟨-147733339624551986423470736196471221256425722688986, 148779085651092554928906917974966280327325924384155⟩
  | 2, 3 => ⟨-284012820357529571880707327729920859055420568324424, 285478146465848210900814824971187432579391015040415⟩
  | 3, 2 => ⟨-546812887530600381028827561075335017149154863996293, 548711406612407414153844339527670245342144311045213⟩
  | 4, 1 => ⟨-1053656931483571280963822585764163638926874953094761, 1055612753660554613961242775630900133489098954550067⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0567Geometry.ds, E8TAxisProd0567Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2675566921221639208261798654397839500058721941 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0567CertifiedArithmetic

end


