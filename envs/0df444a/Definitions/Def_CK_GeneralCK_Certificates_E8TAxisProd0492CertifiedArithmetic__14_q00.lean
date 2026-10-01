-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0492CertifiedArithmetic__14_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:57:12.690978+00:00
-- url     : https://prove2.me/theorems/ecbc9698-a3d2-4c69-8306-f7af9018f4c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 1 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 1 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0493CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0494CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0495CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0496CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0497CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0498CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0499CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0500CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0501CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0502CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0503CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0504CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0505CertifiedArithmetic) (piece 1 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0492CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0493CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0494CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0495CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0496CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0497CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0498CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0499CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0500CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0501CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0502CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0503CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0504CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0505CertifiedArithmetic) (piece 1 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0483GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0484GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0486GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0490GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0489GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0489GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0482GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0490GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0494GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0494Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0495GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0497GraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0500GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0500GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0502GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0502GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0504GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0504GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0505GraphWholeD__15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0492GraphCenterA.qJetBox,
   E8TAxisProd0492GraphCenterB.qJetBox,
   E8TAxisProd0492GraphCenterC.qJetBox,
   E8TAxisProd0492GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0492GraphWholeA.qJetBox,
   E8TAxisProd0492GraphWholeB.qJetBox,
   E8TAxisProd0492GraphWholeC.qJetBox,
   E8TAxisProd0492GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14049142524469387868190533484420799672721872911, 14049142524469387868190533484420883222776340005⟩
  | 0, 2 => ⟨44553927107509388861563226882139412709064058023, 44553927107509388861563226882139716160500844656⟩
  | 1, 1 => ⟨44958230520537832657191738383012223291539440119, 44958230520537832657191738383012760944656254986⟩
  | 0, 3 => ⟨96754167384255226848890320331094967399961107589, 96754167384255226848890320331095935803924446460⟩
  | 1, 2 => ⟨131322376193473775818666083900365712556018447619, 131322376193473775818666083900367419416670329995⟩
  | 2, 1 => ⟨132365186435111788550882616133785727088279781954, 132365186435111788550882616133788795335415228711⟩
  | 0, 4 => ⟨173688792910432799614452739780089049744013630874, 173688792910432799614452739780092274150846341439⟩
  | 1, 3 => ⟨262155723024817549839502547154142149300597333193, 262155723024817549839502547154147930349243777478⟩
  | 2, 2 => ⟨351172071285064268527622433246102737836171421987, 351172071285064268527622433246113285829302769604⟩
  | 3, 1 => ⟨353572339486192793634485634283877469339903467289, 353572339486192793634485634283896890962569500159⟩
  | 0, 5 => ⟨-596089713345194749770128177274358657382070485545902, 599688362353880737570264919057322780355877838674108⟩
  | 1, 4 => ⟨-1161656135890652689620096818099135187864816505005728, 1167033256689265757127304708019091477546729078897972⟩
  | 2, 3 => ⟨-2266562966707685131086769694171419715156410284623868, 2274269866337209442617093774481638455693609013624958⟩
  | 3, 2 => ⟨-4425676401190529932761404042260539387261439838886295, 4435764365982423648364531059973115752568343752374483⟩
  | 4, 1 => ⟨-8646091462013957739015256992300167976976470153420836, 8656402032678858224767577640954603263662676167745415⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0492Geometry.ds, E8TAxisProd0492Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13149858260257146997456379105191917598298130159 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0492CertifiedArithmetic

end


