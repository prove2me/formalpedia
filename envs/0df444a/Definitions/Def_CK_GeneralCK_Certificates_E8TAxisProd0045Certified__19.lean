-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0045Certified__19
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0045Certified__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:39:58.647499+00:00
-- url     : https://prove2.me/theorems/eee76b92-8529-46cc-a177-f5b8a59ce828
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0045Certified (+18 modules: GeneralCK.Certificates.E8TAxisProd0046Certified, GeneralCK.Certificates.E8TAxisProd0047Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0045Certified (+18 modules: GeneralCK.Certificates.E8TAxisProd0046Certified, GeneralCK.Certificates.E8TAxisProd0047Certified, GeneralCK.Certificates.E8TAxisProd0048Certified, GeneralCK.Certificates.E8TAxisProd0049Certified, GeneralCK.Certificates.E8TAxisProd0050Certified, GeneralCK.Certificates.E8TAxisProd0051Certified, GeneralCK.Certificates.E8TAxisProd0052Certified, GeneralCK.Certificates.E8TAxisProd0053Certified, GeneralCK.Certificates.E8TAxisProd0054Certified, GeneralCK.Certificates.E8TAxisProd0055Certified, GeneralCK.Certificates.E8TAxisProd0056Certified, GeneralCK.Certificates.E8TAxisProd0057Certified, GeneralCK.Certificates.E8TAxisProd0058Certified, GeneralCK.Certificates.E8TAxisProd0059Certified, GeneralCK.Certificates.E8TAxisProd0060Certified, GeneralCK.Certificates.E8TAxisProd0061Certified, GeneralCK.Certificates.E8TAxisProd0062Certified, GeneralCK.Certificates.E8TAxisProd0063Certified)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0045Certified (+18 modules: GeneralCK.Certificates.E8TAxisProd0046Certified, GeneralCK.Certificates.E8TAxisProd0047Certified, GeneralCK.Certificates.E8TAxisProd0048Certified, GeneralCK.Certificates.E8TAxisProd0049Certified, GeneralCK.Certificates.E8TAxisProd0050Certified, GeneralCK.Certificates.E8TAxisProd0051Certified, GeneralCK.Certificates.E8TAxisProd0052Certified, GeneralCK.Certificates.E8TAxisProd0053Certified, GeneralCK.Certificates.E8TAxisProd0054Certified, GeneralCK.Certificates.E8TAxisProd0055Certified, GeneralCK.Certificates.E8TAxisProd0056Certified, GeneralCK.Certificates.E8TAxisProd0057Certified, GeneralCK.Certificates.E8TAxisProd0058Certified, GeneralCK.Certificates.E8TAxisProd0059Certified, GeneralCK.Certificates.E8TAxisProd0060Certified, GeneralCK.Certificates.E8TAxisProd0061Certified, GeneralCK.Certificates.E8TAxisProd0062Certified, GeneralCK.Certificates.E8TAxisProd0063Certified)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0045Certified (+18 modules: GeneralCK.Certificates.E8TAxisProd0046Certified, GeneralCK.Certificates.E8TAxisProd0047Certified, GeneralCK.Certificates.E8TAxisProd0048Certified, GeneralCK.Certificates.E8TAxisProd0049Certified, GeneralCK.Certificates.E8TAxisProd0050Certified, GeneralCK.Certificates.E8TAxisProd0051Certified, GeneralCK.Certificates.E8TAxisProd0052Certified, GeneralCK.Certificates.E8TAxisProd0053Certified, GeneralCK.Certificates.E8TAxisProd0054Certified, GeneralCK.Certificates.E8TAxisProd0055Certified, GeneralCK.Certificates.E8TAxisProd0056Certified, GeneralCK.Certificates.E8TAxisProd0057Certified, GeneralCK.Certificates.E8TAxisProd0058Certified, GeneralCK.Certificates.E8TAxisProd0059Certified, GeneralCK.Certificates.E8TAxisProd0060Certified, GeneralCK.Certificates.E8TAxisProd0061Certified, GeneralCK.Certificates.E8TAxisProd0062Certified, GeneralCK.Certificates.E8TAxisProd0063Certified) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0045Certified (+18 modules: GeneralCK/Certificates/E8TAxisProd0046Certified, GeneralCK/Certificates/E8TAxisProd0047Certified, GeneralCK/Certificates/E8TAxisProd0048Certified, GeneralCK/Certificates/E8TAxisProd0049Certified, GeneralCK/Certificates/E8TAxisProd0050Certified, GeneralCK/Certificates/E8TAxisProd0051Certified, GeneralCK/Certificates/E8TAxisProd0052Certified, GeneralCK/Certificates/E8TAxisProd0053Certified, GeneralCK/Certificates/E8TAxisProd0054Certified, GeneralCK/Certificates/E8TAxisProd0055Certified, GeneralCK/Certificates/E8TAxisProd0056Certified, GeneralCK/Certificates/E8TAxisProd0057Certified, GeneralCK/Certificates/E8TAxisProd0058Certified, GeneralCK/Certificates/E8TAxisProd0059Certified, GeneralCK/Certificates/E8TAxisProd0060Certified, GeneralCK/Certificates/E8TAxisProd0061Certified, GeneralCK/Certificates/E8TAxisProd0062Certified, GeneralCK/Certificates/E8TAxisProd0063Certified).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0045EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0046CertifiedArithmetic__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0046EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0047EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0048EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0049EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0050EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0051EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0052EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0053EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0054EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0055EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0056EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0057EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0058EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0059EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0060EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0061EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062CertifiedArithmetic__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0063EndpointWitnesses

-- ===== source module GeneralCK.Certificates.E8TAxisProd0045Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0045Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0045Geometry E8TAxisProd0045CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0045GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0045GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0045GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0045GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0045GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0045GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0045GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0045EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0045GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0045EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0045EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0045EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0045EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0045Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0046Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0046Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0046Geometry E8TAxisProd0046CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0046GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0046GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0046GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0046GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0046GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0046GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0046GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0046EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0046GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0046EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0046EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0046EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0046EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0046Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0047Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0047Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0047Geometry E8TAxisProd0047CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0047GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0047GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0047GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0047GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0047GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0047GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0047GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0047EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0047GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0047EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0047EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0047EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0047EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0047Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0048Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0048Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0048Geometry E8TAxisProd0048CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0048GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0048GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0048GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0048GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0048GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0048GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0048GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0048EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0048GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0048EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0048EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0048EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0048EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0048Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0049Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0049Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0049Geometry E8TAxisProd0049CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0049GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0049GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0049GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0049GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0049GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0049GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0049GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0049EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0049GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0049EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0049EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0049EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0049EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0049Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0050Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0050Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0050Geometry E8TAxisProd0050CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0050GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0050GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0050GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0050GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0050GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0050GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0050GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0050EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0050GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0050EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0050EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0050EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0050EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0050Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0051Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0051Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0051Geometry E8TAxisProd0051CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0051GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0051GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0051GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0051GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0051GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0051GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0051GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0051EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0051GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0051EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0051EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0051EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0051EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0051Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0052Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0052Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0052Geometry E8TAxisProd0052CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0052GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0052GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0052GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0052GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0052GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0052GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0052GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0052EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0052GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0052EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0052EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0052EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0052EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0052Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0053Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0053Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0053Geometry E8TAxisProd0053CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0053GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0053GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0053GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0053GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0053GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0053GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0053GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0053EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0053GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0053EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0053EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0053EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0053EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0053Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0054Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0054Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0054Geometry E8TAxisProd0054CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0054GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0054GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0054GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0054GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0054GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0054GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0054GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0054EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0054GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0054EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0054EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0054EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0054EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0054Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0055Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0055Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0055Geometry E8TAxisProd0055CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0055GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0055GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0055GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0055GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0055GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0055GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0055GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0055EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0055GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0055EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0055EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0055EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0055EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0055Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0056Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0056Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0056Geometry E8TAxisProd0056CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0056GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0056GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0056GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0056GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0056GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0056GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0056GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0056EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0056GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0056EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0056EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0056EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0056EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0056Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0057Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0057Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0057Geometry E8TAxisProd0057CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0057GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0057GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0057GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0057GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0057GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0057GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0057GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0057EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0057GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0057EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0057EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0057EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0057EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0057Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0058Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0058Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0058Geometry E8TAxisProd0058CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0058GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0058GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0058GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0058GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0058GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0058GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0058GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0058EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0058GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0058EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0058EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0058EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0058EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0058Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0059Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0059Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0059Geometry E8TAxisProd0059CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0059GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0059GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0059GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0059GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0059GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0059GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0059GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0059EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0059GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0059EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0059EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0059EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0059EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0059Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0060Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0060Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0060Geometry E8TAxisProd0060CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0060GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0060GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0060GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0060GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0060GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0060GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0060GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0060EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0060GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0060EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0060EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0060EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0060EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0060Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0061Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0061Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0061Geometry E8TAxisProd0061CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0061GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0061GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0061GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0061GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0061GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0061GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0061GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0061EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0061GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0061EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0061EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0061EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0061EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0061Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0062Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0062Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0062Geometry E8TAxisProd0062CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0062GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0062GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0062GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0062GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0062GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0062GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0062GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0062EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0062GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0062EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0062EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0062EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0062EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0062Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0063Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0063Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0063Geometry E8TAxisProd0063CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0063GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0063GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0063GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0063GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0063GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0063GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0063GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0063EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0063GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0063EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0063EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0063EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0063EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0063Certified

end


