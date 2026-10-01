-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0163CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0163CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:17:37.595557+00:00
-- url     : https://prove2.me/theorems/a3a91834-ec40-47ae-a36f-50a4729bb77a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0163CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0164CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0165CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0166CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0167CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0168CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0169CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0170CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0171CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0172CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0173CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0174CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0175CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0176CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0177CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0178CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0152GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0150GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0154GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0151GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0160GraphWholeA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0154GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0153GraphWholeC__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0155GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0162Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0164GraphCenterB__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0165GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0166GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0167GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0168GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0168GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0169GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171GraphWholeC__14

-- ===== source module GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0163GraphCenterA.qJetBox,
   E8TAxisProd0163GraphCenterB.qJetBox,
   E8TAxisProd0163GraphCenterC.qJetBox,
   E8TAxisProd0163GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0163GraphWholeA.qJetBox,
   E8TAxisProd0163GraphWholeB.qJetBox,
   E8TAxisProd0163GraphWholeC.qJetBox,
   E8TAxisProd0163GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨250661063771053371999598014536381450410209042, 250661063771053371999598014536389581466289108⟩
  | 0, 2 => ⟨1097762305367026289547913760513307713385609641, 1097762305367026289547913760513327161093900128⟩
  | 1, 1 => ⟨1112884206607796060210376209555778656520255613, 1112884206607796060210376209555807080202691162⟩
  | 0, 3 => ⟨3027861845486508014329833723249779369429075996, 3027861845486508014329833723249829990212264001⟩
  | 1, 2 => ⟨4397880890672381182274552097823434791164941880, 4397880890672381182274552097823509756116580081⟩
  | 2, 1 => ⟨4449602934182493650815084740214614842770635321, 4449602934182493650815084740214736912972792308⟩
  | 0, 4 => ⟨6710921877286065714612197236023791804092588973, 6710921877286065714612197236023935689047816346⟩
  | 1, 3 => ⟨11346283520521236744402211590250933869933837766, 11346283520521236744402211590251154881680603904⟩
  | 2, 2 => ⟨16025335220237559418515443625331274772345422982, 16025335220237559418515443625331643153839066036⟩
  | 3, 1 => ⟨16188387552559417517090539030126380476197028547, 16188387552559417517090539030127013070590354494⟩
  | 0, 5 => ⟨-47919713988833181415772073497051123198379063740670, 48295320021976788719148868417616376590105686585981⟩
  | 1, 4 => ⟨-90821211055089146130772887250384715033428053009064, 91302616367738489259921189748228079629536139993498⟩
  | 2, 3 => ⟨-172754609414216035463971289064471417946398666083935, 173376301744815744247169639177595385597480881692419⟩
  | 3, 2 => ⟨-329098269859342013135196733473342258886378219330593, 329873125035177844574880020277704593988746820734837⟩
  | 4, 1 => ⟨-627243527541717162094584506516176053591123098052351, 628071355935363641769256329925368152419718356549515⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0163Geometry.ds, E8TAxisProd0163Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 184950353607608681001741351612329013717243419 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0163CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0164GraphCenterA.qJetBox,
   E8TAxisProd0164GraphCenterB.qJetBox,
   E8TAxisProd0164GraphCenterC.qJetBox,
   E8TAxisProd0164GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0164GraphWholeA.qJetBox,
   E8TAxisProd0164GraphWholeB.qJetBox,
   E8TAxisProd0164GraphWholeC.qJetBox,
   E8TAxisProd0164GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨191308701947033779659707339893414549340603031, 191308701947033779659707339893421890465700739⟩
  | 0, 2 => ⟨858098991786684566162198881877261489704626716, 858098991786684566162198881877278727471179291⟩
  | 1, 1 => ⟨873061512722820911994124088539308485765692461, 873061512722820911994124088539333309148228609⟩
  | 0, 3 => ⟨2403609646333033929475342755069046443102224358, 2403609646333033929475342755069090531808055923⟩
  | 1, 2 => ⟨3517802702779183611183750554605809198283431747, 3517802702779183611183750554605873478297276226⟩
  | 2, 1 => ⟨3569856418171473071933718416047012532427515037, 3569856418171473071933718416047116323044156024⟩
  | 0, 4 => ⟨5357351928211298156690203180846207690636794244, 5357351928211298156690203180846331519637507287⟩
  | 1, 3 => ⟨9180874711898294388514907373413070382519768541, 9180874711898294388514907373413257615344597174⟩
  | 2, 2 => ⟨13049667239042083518476990153647823656783267573, 13049667239042083518476990153648133029712815670⟩
  | 3, 1 => ⟨13215785128684675612598294807082722062190778677, 13215785128684675612598294807083250109854508373⟩
  | 0, 5 => ⟨-37658825805643031210352615532968526231964628455212, 37954071426554080989116241046755343986674482264620⟩
  | 1, 4 => ⟨-71094289326634457597389815297615725669063388544394, 71459667710565937781798611052965749850101616061254⟩
  | 2, 3 => ⟨-134759635646670335960772307827493002935408280348994, 135218142004450641714077569548139023590391644722178⟩
  | 3, 2 => ⟨-255856852234708421867517795711457618402193177940761, 256419006872207812301391211134195675767969252581381⟩
  | 4, 1 => ⟨-486008547270220082772225549111496822676924619476923, 486613474121661063280318863786220700431564123558295⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0164Geometry.ds, E8TAxisProd0164Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 139976247528935736306263188333419804197048902 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0164CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0165GraphCenterA.qJetBox,
   E8TAxisProd0165GraphCenterB.qJetBox,
   E8TAxisProd0165GraphCenterC.qJetBox,
   E8TAxisProd0165GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0165GraphWholeA.qJetBox,
   E8TAxisProd0165GraphWholeB.qJetBox,
   E8TAxisProd0165GraphWholeC.qJetBox,
   E8TAxisProd0165GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨143204494897613118099852473763345340560230949, 143204494897613118099852473763351962306230346⟩
  | 0, 2 => ⟨661999513811449870030557308555417952875756191, 661999513811449870030557308555433242449898232⟩
  | 1, 1 => ⟨674013744909871110192643157367714260874390717, 674013744909871110192643157367735952139943565⟩
  | 0, 3 => ⟨1888599514540233107867622487769217104573316190, 1888599514540233107867622487769255500280450883⟩
  | 1, 2 => ⟨2783638494320729279014305591809152797741739620, 2783638494320729279014305591809207876160226740⟩
  | 2, 1 => ⟨2826226947759163726483326264534127479100050208, 2826226947759163726483326264534215620335824060⟩
  | 0, 4 => ⟨4233305939741872034864186357004210075753918053, 4233305939741872034864186357004316635469397562⟩
  | 1, 3 => ⟨7361231742072400330893597459189629150279617660, 7361231742072400330893597459189787603899131220⟩
  | 2, 2 => ⟨10527378649481673355820543878371559926366519041, 10527378649481673355820543878371819305191949354⟩
  | 3, 1 => ⟨10664982100632778701441940854302503554051103941, 10664982100632778701441940854302943411465886148⟩
  | 0, 5 => ⟨-29569621696248817494383608222228616234661923908758, 29801942597756491837404946061269498478749646478214⟩
  | 1, 4 => ⟨-55579750192424238187332790616518722654777877514240, 55855009099214883057734843261738138579864328501021⟩
  | 2, 3 => ⟨-104944503780640530323105417974177392876579071100157, 105276743985504080275434388720279386759649528080391⟩
  | 3, 2 => ⟨-198508777310554353927490622056169801106412248330858, 198906104309147808193304199584206094017585936426055⟩
  | 4, 1 => ⟨-375664326033777424398912278805055600467715442579273, 376094383684869072113145014726022185532847300854709⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0165Geometry.ds, E8TAxisProd0165Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 103513019444375220521724262404526452946529564 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0165CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0166GraphCenterA.qJetBox,
   E8TAxisProd0166GraphCenterB.qJetBox,
   E8TAxisProd0166GraphCenterC.qJetBox,
   E8TAxisProd0166GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0166GraphWholeA.qJetBox,
   E8TAxisProd0166GraphWholeB.qJetBox,
   E8TAxisProd0166GraphWholeC.qJetBox,
   E8TAxisProd0166GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨189170951814341795659117685567590047325192441, 189170951814341795659117685567597364626903297⟩
  | 0, 2 => ⟨852106680495020372681017392449232555290677085, 852106680495020372681017392449249730367814470⟩
  | 1, 1 => ⟨864295644271456501140975300757272002547091853, 864295644271456501140975300757296732196604836⟩
  | 0, 3 => ⟨2390250933260704851480894116139930446269724456, 2390250933260704851480894116139974361475752230⟩
  | 1, 2 => ⟨3494912803488498169084728336851363725757290357, 3494912803488498169084728336851427740578234727⟩
  | 2, 1 => ⟨3537332614984234157661700058616789179108569073, 3537332614984234157661700058616892526309349184⟩
  | 0, 4 => ⟨5329640888682611394720521861800710240625419592, 5329640888682611394720521861800833553738002533⟩
  | 1, 3 => ⟨9131086270368241625472165441765913540154308231, 9131086270368241625472165441766099961916085823⟩
  | 2, 2 => ⟨12969445402786637972786461422831372943299206635, 12969445402786637972786461422831680925916551470⟩
  | 3, 1 => ⟨13104852198308248244783540330231083334750131972, 13104852198308248244783540330231608930073726003⟩
  | 0, 5 => ⟨-37431918488574801404560417728274144883717365703745, 37725253495418902852566473831852999438943874345941⟩
  | 1, 4 => ⟨-70657762723349277029578203262625594894652358354947, 71020342263343004860391909347495386891580380356083⟩
  | 2, 3 => ⟨-133917121226058685545090570119863400062267544003799, 134371468703513820914572160972601370530846868992965⟩
  | 3, 2 => ⟨-254227860031735527536066044447405361673564017922774, 254783915243407224668918181968213577048168070531281⟩
  | 4, 1 => ⟨-482855627345515803377029668834074521677486818008949, 483452136604639584736161505890813658406933782838319⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0166Geometry.ds, E8TAxisProd0166Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 138273664304713321005330707670080816086388777 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0166CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0167GraphCenterA.qJetBox,
   E8TAxisProd0167GraphCenterB.qJetBox,
   E8TAxisProd0167GraphCenterC.qJetBox,
   E8TAxisProd0167GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0167GraphWholeA.qJetBox,
   E8TAxisProd0167GraphWholeB.qJetBox,
   E8TAxisProd0167GraphWholeC.qJetBox,
   E8TAxisProd0167GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨141555386976715781472729105972242413558049890, 141555386976715781472729105972249013992512870⟩
  | 0, 2 => ⟨657291221099700573894890869032537175215899047, 657291221099700573894890869032552410347248474⟩
  | 1, 1 => ⟨667077610580892691937530842822813264759590076, 667077610580892691937530842822834875998014849⟩
  | 0, 3 => ⟨1878043846150275386994358571620681257076368312, 1878043846150275386994358571620719503947281036⟩
  | 1, 2 => ⟨2765285724537275714446329280173030649952076005, 2765285724537275714446329280173085504530750257⟩
  | 2, 1 => ⟨2799990352793388980344106434664387190598009507, 2799990352793388980344106434664474960468533815⟩
  | 0, 4 => ⟨4211246833092129092352093506749879708936968690, 4211246833092129092352093506749985832305139963⟩
  | 1, 3 => ⟨7321018105733505181255399038752127759515138456, 7321018105733505181255399038752285537928186695⟩
  | 2, 2 => ⟨10461955225394734559936736008427363427921479806, 10461955225394734559936736008427621657456557767⟩
  | 3, 1 => ⟨10574113742015180114163612958844147988359395453, 10574113742015180114163612958844585827621365134⟩
  | 0, 5 => ⟨-29393313894821769633659801504121353874593931000540, 29624143141955550610921708230001874692246232024489⟩
  | 1, 4 => ⟨-55241403638232951381070233857461613347680405945182, 55514579515485595047625884449964956126124130743615⟩
  | 2, 3 => ⟨-104292854476251391117340019408990529496468816139240, 104622132718408410409549848239289491412159346209999⟩
  | 3, 2 => ⟨-197251243529666176401558831424459290934418472681454, 197644418432777746257798616938204286351086502721136⟩
  | 4, 1 => ⟨-373234829674960980956541939301960774110566086223215, 373659502279249237225441636918767048647116718016295⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0167Geometry.ds, E8TAxisProd0167Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 102205618449275412357971085116000969137728066 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0167CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0168GraphCenterA.qJetBox,
   E8TAxisProd0168GraphCenterB.qJetBox,
   E8TAxisProd0168GraphCenterC.qJetBox,
   E8TAxisProd0168GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0168GraphWholeA.qJetBox,
   E8TAxisProd0168GraphWholeB.qJetBox,
   E8TAxisProd0168GraphWholeC.qJetBox,
   E8TAxisProd0168GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨108741564879694082117826592689324281035550598, 108741564879694082117826592689330303781572379⟩
  | 0, 2 => ⟨514595748655343094974567397746304475093025486, 514595748655343094974567397746318187155993481⟩
  | 1, 1 => ⟨527812257375998319125482251530912833887056434, 527812257375998319125482251530932004233144629⟩
  | 0, 3 => ⟨1493140676378833673910889366564513711352486578, 1493140676378833673910889366564547527887208768⟩
  | 1, 2 => ⟨2221880894034312813307827362871062044474030690, 2221880894034312813307827362871109772860105217⟩
  | 2, 1 => ⟨2269665702917891561755024993777552692461093769, 2269665702917891561755024993777628388894314705⟩
  | 0, 4 => ⟨3362647875103342684378108403194086480631741919, 3362647875103342684378108403194179332750784265⟩
  | 1, 3 => ⟨5945011460960578225705975039436876002057186013, 5945011460960578225705975039437011744475670233⟩
  | 2, 2 => ⟨8571667339677411015701440977994266463564076190, 8571667339677411015701440977994486575401804404⟩
  | 3, 1 => ⟨8727937627408725169187892230370728814677996595, 8727937627408725169187892230371099726167391988⟩
  | 0, 5 => ⟨-23617084118516395192967335168805599627016744358327, 23801837333188998050368974305890509525612150761526⟩
  | 1, 4 => ⟨-44195332661562270744237206806902960969115965309986, 44403887982492552365393166225114631282795269632209⟩
  | 2, 3 => ⟨-83125353250965994894869386252615731989056271350789, 83365553024028066893601774911449937455619427365302⟩
  | 3, 2 => ⟨-156653618258715302006689963159336646250309702372720, 156931911644415312243096518304474681439953998741472⟩
  | 4, 1 => ⟨-295352161885904374541650525007350256555206975637065, 295656332521805305738216916389536084702919238699856⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0168Geometry.ds, E8TAxisProd0168Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 77579893755903864171045173056026628851020492 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0168CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0169GraphCenterA.qJetBox,
   E8TAxisProd0169GraphCenterB.qJetBox,
   E8TAxisProd0169GraphCenterC.qJetBox,
   E8TAxisProd0169GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0169GraphWholeA.qJetBox,
   E8TAxisProd0169GraphWholeB.qJetBox,
   E8TAxisProd0169GraphWholeC.qJetBox,
   E8TAxisProd0169GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨79849787708511773677630538737185120919546843, 79849787708511773677630538737190571401135241⟩
  | 0, 2 => ⟨391304202600525580278976596644441636169830419, 391304202600525580278976596644453889094864841⟩
  | 1, 1 => ⟨401820739230502320937915440759006730680040261, 401820739230502320937915440759023608606126072⟩
  | 0, 3 => ⟨1160869484099284588214467058892861394024824993, 1160869484099284588214467058892891044655726959⟩
  | 1, 2 => ⟨1741168786608729196431102593016193878005613758, 1741168786608729196431102593016235026349878277⟩
  | 2, 1 => ⟨1780068044929509794276135776944363324712045211, 1780068044929509794276135776944427966804288523⟩
  | 0, 4 => ⟨2628667443255584540155197011793358221794220802, 2628667443255584540155197011793438957765065500⟩
  | 1, 3 => ⟨4730345194697518534599799631893222679952986659, 4730345194697518534599799631893338681756180677⟩
  | 2, 2 => ⟨6869413276768994403366625271496303389549704501, 6869413276768994403366625271496489662278480728⟩
  | 3, 1 => ⟨6998313665133660303588041419607798778336037510, 6998313665133660303588041419608110664715227483⟩
  | 0, 5 => ⟨-18814329585961592528206270638693206686555060186618, 18959631248919059728074679246166610288531875518230⟩
  | 1, 4 => ⟨-35035754850340865047341561268795942205890259239192, 35190051571762177371850150588490158553937961223229⟩
  | 2, 3 => ⟨-65612265116343702106703458713755078913505796049269, 65778524838423753608260005689481577792520335735841⟩
  | 3, 2 => ⟨-123132582862865327310246240870768333715867123530609, 123315595610392768332666712113546229940370127443293⟩
  | 4, 1 => ⟨-231168256970156178517456131549412636695648130065888, 231370339062820127320640166937996355454103843628176⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0169Geometry.ds, E8TAxisProd0169Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55822456699293545515566815271987419780405058 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0169CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0170GraphCenterA.qJetBox,
   E8TAxisProd0170GraphCenterB.qJetBox,
   E8TAxisProd0170GraphCenterC.qJetBox,
   E8TAxisProd0170GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0170GraphWholeA.qJetBox,
   E8TAxisProd0170GraphWholeB.qJetBox,
   E8TAxisProd0170GraphWholeC.qJetBox,
   E8TAxisProd0170GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨107459732827262161744926312425335122627903662, 107459732827262161744926312425341126052784655⟩
  | 0, 2 => ⟨510873386862357342315734888522928257097928579, 510873386862357342315734888522941921028473136⟩
  | 1, 1 => ⟨522276099239071271532867402277096302206699439, 522276099239071271532867402277115402926082929⟩
  | 0, 3 => ⟨1484756099531524915659426358031605895202077004, 1484756099531524915659426358031639581658741361⟩
  | 1, 2 => ⟨2207059223095246400782770440877931549868686796, 2207059223095246400782770440877979085708777629⟩
  | 2, 1 => ⟨2248303760430462993433434063415695419671602634, 2248303760430462993433434063415770799240793578⟩
  | 0, 4 => ⟨3345028216246559075198963396479513955762760284, 3345028216246559075198963396479606433377509083⟩
  | 1, 3 => ⟨5912353236828256769892929496524839235996990187, 5912353236828256769892929496524974408503613351⟩
  | 2, 2 => ⟨8517934694615778357784972443853431195552946252, 8517934694615778357784972443853650344780783043⟩
  | 3, 1 => ⟨8652850702493533870559026965275201361572093708, 8652850702493533870559026965275570591306404978⟩
  | 0, 5 => ⟨-23480216245301475272607783924369415651149008953622, 23663851627360325032425926136456727195450007104028⟩
  | 1, 4 => ⟨-43933404364604095898698766135397446946484504008318, 44140437325396208721742217592104712896530745482160⟩
  | 2, 3 => ⟨-82621948814840635186898644082207042306292360110493, 82860059245976510140434139586901957479583931429629⟩
  | 3, 2 => ⟨-155683885545562028944864728608648741523630482514497, 155959392212475025440544251368009822091327882591819⟩
  | 4, 1 => ⟨-293481687454610540260516327533700313302860155605197, 293782538399941785410231132203887044743457954358067⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0170Geometry.ds, E8TAxisProd0170Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 76567987791428465173126201487907200664996260 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0170CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0171GraphCenterA.qJetBox,
   E8TAxisProd0171GraphCenterB.qJetBox,
   E8TAxisProd0171GraphCenterC.qJetBox,
   E8TAxisProd0171GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0171GraphWholeA.qJetBox,
   E8TAxisProd0171GraphWholeB.qJetBox,
   E8TAxisProd0171GraphWholeC.qJetBox,
   E8TAxisProd0171GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨78875148082684413395693910466461779476441468, 78875148082684413395693910466467212487076918⟩
  | 0, 2 => ⟨388410229040832123754094946627242191693784717, 388410229040832123754094946627254402247692899⟩
  | 1, 1 => ⟨397482572340915877290354383308706242687235740, 397482572340915877290354383308723060345549898⟩
  | 0, 3 => ⟨1154315130464695862432052910957740509502882614, 1154315130464695862432052910957770047179053776⟩
  | 1, 2 => ⟨1729375611643397479107851931500486724074923434, 1729375611643397479107851931500527708174810215⟩
  | 2, 1 => ⟨1762948948828232717985924553207220791704559778, 1762948948828232717985924553207285166063834609⟩
  | 0, 4 => ⟨2614827095778506045277974835687163878697914649, 2614827095778506045277974835687244299799460773⟩
  | 1, 3 => ⟨4704217384770270297055086785245430280544941736, 4704217384770270297055086785245545813823613517⟩
  | 2, 2 => ⟨6825902889375732002986640683259086565810640448, 6825902889375732002986640683259272055888689443⟩
  | 3, 1 => ⟨6937184894732189425936386269769029160366199139, 6937184894732189425936386269769339689655434610⟩
  | 0, 5 => ⟨-18706643383197128357824664442858371527075717521953, 18851115391778554067842959710434626585721880990207⟩
  | 1, 4 => ⟨-34830273931920118639149388558248110331073619320348, 34983503798159559307551584225597728271693746761384⟩
  | 2, 3 => ⟨-65218287077189807302836964271370915923748623330555, 65383173194362549365465144833793580712529169215098⟩
  | 3, 2 => ⟨-122375241887682238771998835133153060797969934255289, 122556567444261439081678512418166224217113979501969⟩
  | 4, 1 => ⟨-229710334659756170265194873647164972958173698737058, 229910699132502270521374918106064427567168968421745⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0171Geometry.ds, E8TAxisProd0171Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55059144674522215004799522100392798432120132 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0171CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0172GraphCenterA.qJetBox,
   E8TAxisProd0172GraphCenterB.qJetBox,
   E8TAxisProd0172GraphCenterC.qJetBox,
   E8TAxisProd0172GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0172GraphWholeA.qJetBox,
   E8TAxisProd0172GraphWholeB.qJetBox,
   E8TAxisProd0172GraphWholeC.qJetBox,
   E8TAxisProd0172GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨57943136791466658856749921176220673370259988, 57943136791466658856749921176225611480283709⟩
  | 0, 2 => ⟨294949754558873710411138548210652019221457051, 294949754558873710411138548210663006378718088⟩
  | 1, 1 => ⟨303271333919044768954033323517512398035554985, 303271333919044768954033323517527312030887475⟩
  | 0, 3 => ⟨897005368339884480812658405702308661740549939, 897005368339884480812658405702334741799913417⟩
  | 1, 2 => ⟨1356579591999839538814761323360152610816516756, 1356579591999839538814761323360188191669832272⟩
  | 2, 1 => ⟨1388155965381513747000539903176579571419416113, 1388155965381513747000539903176634923131008531⟩
  | 0, 4 => ⟨2042821568312067203410781796894250921662346445, 2042821568312067203410781796894321547845999241⟩
  | 1, 3 => ⟨3748369333697171775606750626138431582866737405, 3748369333697171775606750626138531335179374542⟩
  | 2, 2 => ⟨5485496210745578075189578726976396993551349076, 5485496210745578075189578726976555632358326968⟩
  | 3, 1 => ⟨5591632681838004297563738660614313712852583268, 5591632681838004297563738660614577724293296458⟩
  | 0, 5 => ⟨-15064392052650282741223441185190750684927739244162, 15179545187897727929117120409758893080847959034050⟩
  | 1, 4 => ⟨-27906954777302144122429453559800476822137051897381, 28020875731932495644158081427834621094342485604224⟩
  | 2, 3 => ⟨-52021544556270836042473085987355482721927850255410, 52133873166185952593321236490699991053526501216572⟩
  | 3, 2 => ⟨-97192164232159496139407553740718101217466193086535, 97306471064360720794104001292291249145221788701534⟩
  | 4, 1 => ⟨-181639126763245093898382093404944544840659818164803, 181767498809613105909502072033627432984589252319683⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0172Geometry.ds, E8TAxisProd0172Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 39472213505040595779382797149118742634612358 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0172CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0173GraphCenterA.qJetBox,
   E8TAxisProd0173GraphCenterB.qJetBox,
   E8TAxisProd0173GraphCenterC.qJetBox,
   E8TAxisProd0173GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0173GraphWholeA.qJetBox,
   E8TAxisProd0173GraphWholeB.qJetBox,
   E8TAxisProd0173GraphWholeC.qJetBox,
   E8TAxisProd0173GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41484743267777641593668040641186448162138259, 41484743267777641593668040641190925594056779⟩
  | 0, 2 => ⟨220108149341021760474949390858416927995240772, 220108149341021760474949390858426813805709591⟩
  | 1, 1 => ⟨226650630075100569952821845359694478983994938, 226650630075100569952821845359707706571247129⟩
  | 0, 3 => ⟨688353182527258943674997052884184635197669952, 688353182527258943674997052884207633325923430⟩
  | 1, 2 => ⟨1050030674951559575661920217431187957737874966, 1050030674951559575661920217431218793403836929⟩
  | 2, 1 => ⟨1075582005677065279285984852796725032665642358, 1075582005677065279285984852796772513279259737⟩
  | 0, 4 => ⟨1577534458190578323036758517992389644307284921, 1577534458190578323036758517992451617042321832⟩
  | 1, 3 => ⟨2957190687429062186316480995684843527190413201, 2957190687429062186316480995684929513191452512⟩
  | 2, 2 => ⟨4363538223837753441557284708400014958374855143, 4363538223837753441557284708400150306277615742⟩
  | 3, 1 => ⟨4450795670343853062394078094120348198564018528, 4450795670343853062394078094120572031575741218⟩
  | 0, 5 => ⟨-12399743289464070159076408697873977062057261643013, 12487257056763622804891404085638869645944589820103⟩
  | 1, 4 => ⟨-22858809873026693755336874698572976519379013835783, 22935617312621663676486134754613107543151815340103⟩
  | 2, 3 => ⟨-42422803537495459239672104865792241082935866063734, 42485475020959275643151950878361437525075555379595⟩
  | 3, 2 => ⟨-78911653259448648916323272361353067936198489817197, 78962802173308655306973126469796946659724531966525⟩
  | 4, 1 => ⟨-146804256668948880769529400369545413693910125911672, 146865529228228625236678966415519077633269793057915⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0173Geometry.ds, E8TAxisProd0173Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 27180275564051702231027904948765457601105158 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0173CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0174GraphCenterA.qJetBox,
   E8TAxisProd0174GraphCenterB.qJetBox,
   E8TAxisProd0174GraphCenterC.qJetBox,
   E8TAxisProd0174GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0174GraphWholeA.qJetBox,
   E8TAxisProd0174GraphWholeB.qJetBox,
   E8TAxisProd0174GraphWholeC.qJetBox,
   E8TAxisProd0174GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨57208560234034565066140778169611462922093240, 57208560234034565066140778169616385178987028⟩
  | 0, 2 => ⟨292713613699318315857439390385449662397851246, 292713613699318315857439390385460612141242554⟩
  | 1, 1 => ⟨299891576897359514347342969197605152965778466, 299891576897359514347342969197620014656768863⟩
  | 0, 3 => ⟨891911816002220276237276266948213904098842848, 891911816002220276237276266948239885237108497⟩
  | 1, 2 => ⟨1347234692323880293115319790276444352749039023, 1347234692323880293115319790276479792160833753⟩
  | 2, 1 => ⟨1374486155210913971900818740416660148687963302, 1374486155210913971900818740416715271788342235⟩
  | 0, 4 => ⟨2032029489337177000634547847365821015011657073, 2032029489337177000634547847365891367876497707⟩
  | 1, 3 => ⟨3727568583648427768224655751023963042524821583, 3727568583648427768224655751024062394479413547⟩
  | 2, 2 => ⟨5450383890794274037757494502960730692201458101, 5450383890794274037757494502960888666623391534⟩
  | 3, 1 => ⟨5542010385643696305575392648927190998695796547, 5542010385643696305575392648927453862589692925⟩
  | 0, 5 => ⟨-14979313521496493911464331818929894590355399852620, 15093848723764380507396895176397859937077473232577⟩
  | 1, 4 => ⟨-27745116587138808873267479330764167789098191398521, 27858298590519697845370464058523401894418004687997⟩
  | 2, 3 => ⟨-51712021498800776291837868575901154170548457496421, 51823481577680860283810981341783700711881990347850⟩
  | 3, 2 => ⟨-96598479355174974712295322475481466213719141132159, 96711857747643062429310583181217310494397502343927⟩
  | 4, 1 => ⟨-180498593294138515670858762865486287306326194161511, 180626318766917113811449204820322561677226269203694⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0174Geometry.ds, E8TAxisProd0174Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38902614529243520924706413987659887393184442 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0174CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0175GraphCenterA.qJetBox,
   E8TAxisProd0175GraphCenterB.qJetBox,
   E8TAxisProd0175GraphCenterC.qJetBox,
   E8TAxisProd0175GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0175GraphWholeA.qJetBox,
   E8TAxisProd0175GraphWholeB.qJetBox,
   E8TAxisProd0175GraphWholeC.qJetBox,
   E8TAxisProd0175GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨40936619895401482418172847190965459549106834, 40936619895401482418172847190969922546882246⟩
  | 0, 2 => ⟨218392187472298891034974884376222323778034813, 218392187472298891034974884376232176452462731⟩
  | 1, 1 => ⟨224034777423084067063564410608621904330293303, 224034777423084067063564410608635086403518405⟩
  | 0, 3 => ⟨684419790983154096958521086629101738649355366, 684419790983154096958521086629124649849020640⟩
  | 1, 2 => ⟨1042658311793884783980109812535873742766686346, 1042658311793884783980109812535904456301584271⟩
  | 2, 1 => ⟨1064708493326487458106983489475139901051116928, 1064708493326487458106983489475187186039593929⟩
  | 0, 4 => ⟨1569185977727103550667503215059010834705037514, 1569185977727103550667503215059072569575227700⟩
  | 1, 3 => ⟨2940714362914450349893888686680061560654508180, 2940714362914450349893888686680147203982318542⟩
  | 2, 2 => ⟨4335297541490100751933762571652518070107647813, 4335297541490100751933762571652652853339251855⟩
  | 3, 1 => ⟨4410623792516107611820300920541739593819440153, 4410623792516107611820300920541962455478504742⟩
  | 0, 5 => ⟨-12337222944221190232627976295495246539503926157221, 12424180946316498044927595598499078995237293278507⟩
  | 1, 4 => ⟨-22740204487244727842535157886664060665715044093985, 22816364570787688662883502281587730560584061676506⟩
  | 2, 3 => ⟨-42196280922696553886565450322035527140529508266757, 42258233152867742330501333807394715745766779210447⟩
  | 3, 2 => ⟨-78477436382855603233302004058695000998097211581147, 78527925903815603279188187774154073640677661842880⟩
  | 4, 1 => ⟨-145970169456449421160382373879747525289050521294137, 146031318385226626767041534815111898409638215366616⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0175Geometry.ds, E8TAxisProd0175Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26757866228855090008989313304143036774024071 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0175CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0176GraphCenterA.qJetBox,
   E8TAxisProd0176GraphCenterB.qJetBox,
   E8TAxisProd0176GraphCenterC.qJetBox,
   E8TAxisProd0176GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0176GraphWholeA.qJetBox,
   E8TAxisProd0176GraphWholeB.qJetBox,
   E8TAxisProd0176GraphWholeC.qJetBox,
   E8TAxisProd0176GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨106187180523337554021974463149879093528435492, 106187180523337554021974463149885077690483157⟩
  | 0, 2 => ⟨507171931541286672423485186780059862210777069, 507171931541286672423485186780073478184376494⟩
  | 1, 1 => ⟨516776893397002531036069613190276980119856345, 516776893397002531036069613190296011478070029⟩
  | 0, 3 => ⟨1476415462395911038459602825908566681443731014, 1476415462395911038459602825908600238316802903⟩
  | 1, 2 => ⟨2192318988445116552105718056696283317903822669, 2192318988445116552105718056696330661957747873⟩
  | 2, 1 => ⟨2227075789806313670933362100995002245112359908, 2227075789806313670933362100995077309101964608⟩
  | 0, 4 => ⟨3327496039472793866802455558662058007542297736, 3327496039472793866802455558662150112186512326⟩
  | 1, 3 => ⟨5879862298872768332297257740218918668066384375, 5879862298872768332297257740219053273072048164⟩
  | 2, 2 => ⟨8464489615953189249054112835945869058819793390, 8464489615953189249054112835946087249584212248⟩
  | 3, 1 => ⟨8578212419191518700232024057475426077092155313, 8578212419191518700232024057475793632437443923⟩
  | 0, 5 => ⟨-23344175748741328717340256508012847798073470983211, 23526663203700338682366099048300200140409748908874⟩
  | 1, 4 => ⟨-43673024737731561783250228795126918575804317030639, 43878525815643151146499065564499451187910471028280⟩
  | 2, 3 => ⟨-82121515639622340603290426617621556801900018061112, 82357547613509118359480613078859730938685766701731⟩
  | 3, 2 => ⟨-154719911983157638625862268250406455866472761289266, 154992662919427964176307109103429697874313980094671⟩
  | 4, 1 => ⟨-291622408377366689616731624608627841211353119592376, 291920000925981087355187457447025959385689088635756⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0176Geometry.ds, E8TAxisProd0176Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 75563624325188106674504247781127240300793891 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0176CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0177GraphCenterA.qJetBox,
   E8TAxisProd0177GraphCenterB.qJetBox,
   E8TAxisProd0177GraphCenterC.qJetBox,
   E8TAxisProd0177GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0177GraphWholeA.qJetBox,
   E8TAxisProd0177GraphWholeB.qJetBox,
   E8TAxisProd0177GraphWholeC.qJetBox,
   E8TAxisProd0177GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨77907722944398357042028313764491053783060062, 77907722944398357042028313764496469374367343⟩
  | 0, 2 => ⟨385532598186751630651902521357721672416455985, 385532598186751630651902521357733840752148027⟩
  | 1, 1 => ⟨393173806880463278990183246255723672257360696, 393173806880463278990183246255740429875586324⟩
  | 0, 3 => ⟨1147795290597416412547054422414763385347105752, 1147795290597416412547054422414792810489711220⟩
  | 1, 2 => ⟨1717647586918388841115167746808162453473614899, 1717647586918388841115167746808203273964938783⟩
  | 2, 1 => ⟨1745938334542596379541931755579243751055113209, 1745938334542596379541931755579307858746767967⟩
  | 0, 4 => ⟨2601056375918353101654638698007505000679243631, 2601056375918353101654638698007585108149310526⟩
  | 1, 3 => ⟨4678224894723789011422550016430995427753943589, 4678224894723789011422550016431110494397714154⟩
  | 2, 2 => ⟨6782627630195897648561367001041004263584717892, 6782627630195897648561367001041188974208766263⟩
  | 3, 1 => ⟨6876425441479267091794267347332752847908396206, 6876425441479267091794267347333062025716414929⟩
  | 0, 5 => ⟨-18599608114363108923304017884558952602516544125059, 18743220094851941484211048812549206065505737625368⟩
  | 1, 4 => ⟨-34626000620726998957064888642365731848384271041285, 34778151322218672117668869148911094291241737186904⟩
  | 2, 3 => ⟨-64826616363713942157428200775634333744021642059446, 64990133380385986289651718549917652709317069243867⟩
  | 3, 2 => ⟨-121622363612464147317866679058933947900737590279864, 121802021109605329645645546520564905281133125927233⟩
  | 4, 1 => ⟨-228261073239155640638356894649303937610979130559303, 228459760284000401048251302318913461646541325096109⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0177Geometry.ds, E8TAxisProd0177Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 54301675208676813182499511823946018321747966 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0177CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0178GraphCenterA.qJetBox,
   E8TAxisProd0178GraphCenterB.qJetBox,
   E8TAxisProd0178GraphCenterC.qJetBox,
   E8TAxisProd0178GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0178GraphWholeA.qJetBox,
   E8TAxisProd0178GraphWholeB.qJetBox,
   E8TAxisProd0178GraphWholeC.qJetBox,
   E8TAxisProd0178GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨104923855838824511033863264233650885756021519, 104923855838824511033863264233656850713340823⟩
  | 0, 2 => ⟨503491273115819571971335429961106451917378378, 503491273115819571971335429961120020108842510⟩
  | 1, 1 => ⟨511314436781021558137314496826656716615483333, 511314436781021558137314496826675678877021544⟩
  | 0, 3 => ⟨1468118546763154848924805356304530770970377829, 1468118546763154848924805356304564198752331694⟩
  | 1, 2 => ⟨2177659772849136052560791197930149867419755000, 2177659772849136052560791197930197020444233846⟩
  | 2, 1 => ⟨2205981073875201765136277623836400531101079680, 2205981073875201765136277623836475280790274828⟩
  | 0, 4 => ⟨3310050947961382123033779804666405718424768712, 3310050947961382123033779804666497451625828025⟩
  | 1, 3 => ⟨5847537863123567012554638032689399726807840111, 5847537863123567012554638032689533766713310580⟩
  | 2, 2 => ⟨8411330708084476879162034389763492352282250347, 8411330708084476879162034389763709588712193112⟩
  | 3, 1 => ⟨8504020495753475471457064360694312682055728259, 8504020495753475471457064360694678570346750252⟩
  | 0, 5 => ⟨-23208919352644819242879139446382401079493361541667, 23390267283990547167732824696326381776924413810986⟩
  | 1, 4 => ⟨-43414161498542460973235830968175667087111054523641, 43618144235123067045660404159421259361442583743697⟩
  | 2, 3 => ⟨-81624024489498134975288637033434043904238737415121, 81858000310168035658505308476707384385021448669507⟩
  | 3, 2 => ⟨-153761657062463697201062758062425819039294521657409, 154031689204912087100348447616861433541334233036301⟩
  | 4, 1 => ⟨-289774258017193552497256862735271658367833638652219, 290068652788153364949345518053302805610520182402612⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0178Geometry.ds, E8TAxisProd0178Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74566760991431638400839314648758736585747783 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0178CertifiedArithmetic

end


