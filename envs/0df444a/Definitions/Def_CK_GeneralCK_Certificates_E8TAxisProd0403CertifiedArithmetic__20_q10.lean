-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q10
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:29:36.568099+00:00
-- url     : https://prove2.me/theorems/1d9ddb12-791b-4072-8d95-a112074ca541
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 11 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 11 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 11 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK/Certificates/E8TAxisProd0404CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0405CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0406CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0407CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0408CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0409CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0410CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0411CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0412CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0413CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0414CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0415CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0416CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0417CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0418CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0419CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0420CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0421CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0422CertifiedArithmetic) (piece 11 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q09

-- ===== source module GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0413GraphCenterA.qJetBox,
   E8TAxisProd0413GraphCenterB.qJetBox,
   E8TAxisProd0413GraphCenterC.qJetBox,
   E8TAxisProd0413GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0413GraphWholeA.qJetBox,
   E8TAxisProd0413GraphWholeB.qJetBox,
   E8TAxisProd0413GraphWholeC.qJetBox,
   E8TAxisProd0413GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19592341793437746256828922922362091242766132895, 19592341793437746256828922922362201655718434629⟩
  | 0, 2 => ⟨60616374019297602402536768890569477804606000846, 60616374019297602402536768890569891931581488081⟩
  | 1, 1 => ⟨61034867884632292137236747866026823731155764255, 61034867884632292137236747866027565143954501399⟩
  | 0, 3 => ⟨128424701689457262836779914705957919783840257643, 128424701689457262836779914705959257459225927843⟩
  | 1, 2 => ⟨173588542529645535186788433734730880492451134143, 173588542529645535186788433734733259086134408630⟩
  | 2, 1 => ⟨174637190530792946346481028294450636359874518396, 174637190530792946346481028294454938662460723957⟩
  | 0, 4 => ⟨224861240802851941845696387848231694237295888694, 224861240802851941845696387848236204308544408278⟩
  | 1, 3 => ⟨337359943255122204915244054662661362387555735157, 337359943255122204915244054662669505512842204063⟩
  | 2, 2 => ⟨450391502941887066951927252771328089094718830966, 450391502941887066951927252771343021020292855053⟩
  | 3, 1 => ⟨452742072535184859825887656745115788362862265790, 452742072535184859825887656745143402578117716151⟩
  | 0, 5 => ⟨-881688129493105681986714358675658036196421039258083, 886806980751924279645066682638766710978736863260533⟩
  | 1, 4 => ⟨-1722027850634684376309173444928820541713309558906214, 1729713322315322255665056670029264787866591024823459⟩
  | 2, 3 => ⟨-3366976973927728226134811413485759966782954943018920, 3378028709412668357381457969312126680622742127596139⟩
  | 3, 2 => ⟨-6587836940853726234388743280095169944782236078044679, 6602330452649902709104406646270937673534133926564763⟩
  | 4, 1 => ⟨-12896437663882997892945596624554731555169868224091487, 12911256614255080232713460171932086238952824875344266⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0413Geometry.ds, E8TAxisProd0413Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18366903701281271785769776269830077323300966136 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic

end


