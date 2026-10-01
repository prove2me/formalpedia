-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0541CertifiedArithmetic__11_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0541CertifiedArithmetic__11_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T12:09:41.47671+00:00
-- url     : https://prove2.me/theorems/704f8f8d-6889-470e-9ea1-5fe69137629e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0542CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0542CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0543CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0544CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0545CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0546CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0547CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0548CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0549CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0550CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0551CertifiedArithmetic) (piece 1 of 11)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0542CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0543CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0544CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0545CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0546CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0547CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0548CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0549CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0550CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0551CertifiedArithmetic) (piece 1 of 11)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0542CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0543CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0544CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0545CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0546CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0547CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0548CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0549CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0550CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0551CertifiedArithmetic) (piece 1 of 11) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0541CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0542CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0543CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0544CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0545CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0546CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0547CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0548CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0549CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0550CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0551CertifiedArithmetic) (piece 1 of 11).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0536GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0527GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0531GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0535GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0539GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0537GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0537GraphWholeC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0532GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0538Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0542GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0546GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0546GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0549GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0551GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0551GraphCenterD__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0541GraphCenterA.qJetBox,
   E8TAxisProd0541GraphCenterB.qJetBox,
   E8TAxisProd0541GraphCenterC.qJetBox,
   E8TAxisProd0541GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0541GraphWholeA.qJetBox,
   E8TAxisProd0541GraphWholeB.qJetBox,
   E8TAxisProd0541GraphWholeC.qJetBox,
   E8TAxisProd0541GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2918852403395048441370510195072577450522853262, 2918852403395048441370510195072604413916083425⟩
  | 0, 2 => ⟨10380223744392017198313970729923905707905560701, 10380223744392017198313970729923987549111743783⟩
  | 1, 1 => ⟨10539818983542457435964679850638123690675222978, 10539818983542457435964679850638259673065158952⟩
  | 0, 3 => ⟨25027501133868059966479131748505453425554443380, 25027501133868059966479131748505697937763160918⟩
  | 1, 2 => ⟨34719580155338327285412236171578259344915801192, 34719580155338327285412236171578667758816590669⟩
  | 2, 1 => ⟨35188617512898622750991937763329311459790787332, 35188617512898622750991937763330021678541478275⟩
  | 0, 4 => ⟨50270718651523675915236946859177038664355878032, 50270718651523675915236946859177811302930532331⟩
  | 1, 3 => ⟨78390739179365356837660298330322705091536384889, 78390739179365356837660298330324030782791994511⟩
  | 2, 2 => ⟨106812614678463334230867402514939301285798481605, 106812614678463334230867402514941653902245018682⟩
  | 3, 1 => ⟨108066033711771656199740866208303109333989869311, 108066033711771656199740866208307343616954018687⟩
  | 0, 5 => ⟨-77847127594993485649827971722677131653431396372656, 78578407446038369679134575519860662498808057736290⟩
  | 1, 4 => ⟨-149249727811612379526506794427982639487974251181772, 150304197001030737839899492879619142416387726547292⟩
  | 2, 3 => ⟨-286956529597584111218371921027906933187068320919303, 288434677447124067885744133820552282010680673717180⟩
  | 3, 2 => ⟨-552534681790236810424074637358214858399137345302754, 554450749785636614224883757862743542785754276715210⟩
  | 4, 1 => ⟨-1064787792985996879441834829320548557703520534445573, 1066763977492357216048605170562955174566892081546036⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0541Geometry.ds, E8TAxisProd0541Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2711808268249535570467665171820343160262937304 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0541CertifiedArithmetic

end


