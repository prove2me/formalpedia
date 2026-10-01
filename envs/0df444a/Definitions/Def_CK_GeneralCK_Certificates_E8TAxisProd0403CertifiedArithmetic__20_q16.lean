-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:35:41.209284+00:00
-- url     : https://prove2.me/theorems/4a4c4703-ba9c-494d-ac4b-ab4226677810
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 17 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 17 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 17 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK/Certificates/E8TAxisProd0404CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0405CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0406CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0407CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0408CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0409CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0410CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0411CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0412CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0413CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0414CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0415CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0416CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0417CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0418CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0419CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0420CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0421CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0422CertifiedArithmetic) (piece 17 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0419GraphCenterA.qJetBox,
   E8TAxisProd0419GraphCenterB.qJetBox,
   E8TAxisProd0419GraphCenterC.qJetBox,
   E8TAxisProd0419GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0419GraphWholeA.qJetBox,
   E8TAxisProd0419GraphWholeB.qJetBox,
   E8TAxisProd0419GraphWholeC.qJetBox,
   E8TAxisProd0419GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨24181904930917349099300490513327628711523929052, 24181904930917349099300490513327761655099169628⟩
  | 0, 2 => ⟨73744800706376956577361663811237888397993443672, 73744800706376956577361663811238396611816780445⟩
  | 1, 1 => ⟨74043563124573140051311773573340983412595442014, 74043563124573140051311773573341898872633559362⟩
  | 0, 3 => ⟨153824802476145037875407593095222717463125329992, 153824802476145037875407593095224370703054155858⟩
  | 1, 2 => ⟨207305792086667211686327755397627079064100797464, 207305792086667211686327755397630034246317113089⟩
  | 2, 1 => ⟨208040983871837222046585335773682068549067571874, 208040983871837222046585335773687434141204256783⟩
  | 0, 4 => ⟨265221242097847501392930035267661809708020604717, 265221242097847501392930035267667425847620973938⟩
  | 1, 3 => ⟨396367965988319324377446387670413997538878228783, 396367965988319324377446387670424179928525723118⟩
  | 2, 2 => ⟨527880524619983686713896005849623392279313596164, 527880524619983686713896005849642120205791118983⟩
  | 3, 1 => ⟨529503708855571975719636331242630779019931532168, 529503708855571975719636331242665507192378253694⟩
  | 0, 5 => ⟨-1120270358374000790957875918206597209798677152262049, 1126694374276304210865443639465371990742523168551494⟩
  | 1, 4 => ⟨-2190723690863775809179795603050501718927569770386989, 2200396173797655367337262801285399923083480254820426⟩
  | 2, 3 => ⟨-4288499950786495121867387084032187418439560270374489, 4302435744536851742879547279323172095928106088886417⟩
  | 3, 2 => ⟨-8400762918627960114203692788178226912575741148064001, 8419056079726987726647570140231176139178271720150394⟩
  | 4, 1 => ⟨-16464791683353345705181586234661707910950293084363363, 16483487607977216030378493238518743348816654107211916⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0419Geometry.ds, E8TAxisProd0419Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 22692008935497864587770654790529985300401197396 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic

end


