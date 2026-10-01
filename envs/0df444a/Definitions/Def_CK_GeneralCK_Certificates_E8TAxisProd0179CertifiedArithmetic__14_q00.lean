-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:47:59.470488+00:00
-- url     : https://prove2.me/theorems/d2427fb0-36b6-4b3a-95cf-64dff389d669
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 1 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 1 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 1 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0180CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0181CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0182CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0183CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0184CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0185CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0186CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0187CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0188CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0189CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0190CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0191CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0192CertifiedArithmetic) (piece 1 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0168GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0165GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0167GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0169GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0166GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0168GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0162Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0180GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0180GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0182GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0183GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0185GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0188GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0192GraphCenterA__19

-- ===== source module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0179GraphCenterA.qJetBox,
   E8TAxisProd0179GraphCenterB.qJetBox,
   E8TAxisProd0179GraphCenterC.qJetBox,
   E8TAxisProd0179GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0179GraphWholeA.qJetBox,
   E8TAxisProd0179GraphWholeB.qJetBox,
   E8TAxisProd0179GraphWholeC.qJetBox,
   E8TAxisProd0179GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨76947471544563981894933803179938843484948606, 76947471544563981894933803179944241708375435⟩
  | 0, 2 => ⟨382671223971118179591043770149096109548751841, 382671223971118179591043770149108235818562022⟩
  | 1, 1 => ⟨388894280395745858689812412062327000293561992, 388894280395745858689812412062343698098498125⟩
  | 0, 3 => ⟨1141309790829001196548745222609607075161789048, 1141309790829001196548745222609636388190311811⟩
  | 1, 2 => ⟨1705984374940692616230891892308365501424167353, 1705984374940692616230891892308406158940170074⟩
  | 2, 1 => ⟨1729035615705376889317351431126617233801887434, 1729035615705376889317351431126681075886936240⟩
  | 0, 4 => ⟨2587354963427677230101086121564956698399924427, 2587354963427677230101086121565036493471334791⟩
  | 1, 3 => ⟨4652367079674028927745502485240564564272729402, 4652367079674028927745502485240679166163550926⟩
  | 2, 2 => ⟨6739586337438751410822432503254519957259820636, 6739586337438751410822432503254703891613606010⟩
  | 3, 1 => ⟨6816033392854138349940189071400435614941308306, 6816033392854138349940189071400743446854036600⟩
  | 0, 5 => ⟨-18493183560221153866067047679818883101160613215309, 18635941636357287401835844184433277672515210023666⟩
  | 1, 4 => ⟨-34422905874179725265942884057408293887209239764171, 34573986980666502632328691300946398628632398623916⟩
  | 2, 3 => ⟨-64437228299060030634278543106207938939736480720237, 64599391583287862166394908983114157611130737608240⟩
  | 3, 2 => ⟨-120873915574972534038359556731275764304396438182776, 121051929863391374081662096171625472566791298922674⟩
  | 4, 1 => ⟨-226820421180007621317700680617349836637862075480120, 227017470509297292272600641031620806098406763715179⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0179Geometry.ds, E8TAxisProd0179Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53550015288987156733281640106967814438017175 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic

end


