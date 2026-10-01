-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q06
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:19:38.501874+00:00
-- url     : https://prove2.me/theorems/c8bac931-9cb4-490f-8b26-563798920185
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 7 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 7 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 7 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0180CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0181CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0182CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0183CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0184CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0185CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0186CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0187CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0188CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0189CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0190CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0191CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0192CertifiedArithmetic) (piece 7 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q05

-- ===== source module GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0185GraphCenterA.qJetBox,
   E8TAxisProd0185GraphCenterB.qJetBox,
   E8TAxisProd0185GraphCenterC.qJetBox,
   E8TAxisProd0185GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0185GraphWholeA.qJetBox,
   E8TAxisProd0185GraphWholeB.qJetBox,
   E8TAxisProd0185GraphWholeC.qJetBox,
   E8TAxisProd0185GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨247926102621989352667944024428859953747134406, 247926102621989352667944024428868058234833154⟩
  | 0, 2 => ⟨1090213586480001899154287267662295951992677640, 1090213586480001899154287267662315328015828714⟩
  | 1, 1 => ⟨1101924897850904486710712577179087844732159297, 1101924897850904486710712577179116159589139047⟩
  | 0, 3 => ⟨3011127608696274437536788635796719352194539619, 3011127608696274437536788635796769772605082934⟩
  | 1, 2 => ⟨4369591549933606836055039808086016531563985514, 4369591549933606836055039808086091185983954727⟩
  | 2, 1 => ⟨4409661556812890040307037344528224634756881551, 4409661556812890040307037344528346182136686336⟩
  | 0, 4 => ⟨6676494913693764763768877478227000289161166813, 6676494913693764763768877478227143571190923924⟩
  | 1, 3 => ⟨11285239275809092647830316625513318433286910718, 11285239275809092647830316625513538484481778580⟩
  | 2, 2 => ⟨15927850671579938931048972478552816345895522715, 15927850671579938931048972478553183070732806052⟩
  | 3, 1 => ⟨16054202104348867194570681877832669272267182838, 16054202104348867194570681877833298932193870602⟩
  | 0, 5 => ⟨-47626910067679524369024349181974463670293977597299, 47999914820709891454699674070502818724894864566503⟩
  | 1, 4 => ⟨-90256782385319565934744661287878368147798806205159, 90734292863248849552690480534121976400998852541977⟩
  | 2, 3 => ⟨-171663310751670664132429752379524278899194477000611, 172279092671123278697384435477584297052599633345274⟩
  | 3, 2 => ⟨-326984763064205322946469391237568925404499101510662, 327750733143788589393795318580251178015099295242133⟩
  | 4, 1 => ⟨-623146279901123818627119795281618987466935542113311, 623961356433455503687882248595070604138868699599129⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0185Geometry.ds, E8TAxisProd0185Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 182765905885859049922248156494099652064477058 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic

end


