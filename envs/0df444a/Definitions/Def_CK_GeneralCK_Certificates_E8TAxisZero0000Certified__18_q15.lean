-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Certified__18_q15
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000Certified__18_q15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:25:32.619716+00:00
-- url     : https://prove2.me/theorems/7b6b33ba-4c13-4314-a5f3-7ee74a717bb4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000Certified (+17 modules: GeneralCK.Certificates.E8TAxisZero0001Certified, GeneralCK.Certificates.E8TAxisZero0002Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000Certified (+17 modules: GeneralCK.Certificates.E8TAxisZero0001Certified, GeneralCK.Certificates.E8TAxisZero0002Certified, GeneralCK.Certificates.E8TAxisZero0003Certified, GeneralCK.Certificates.E8TAxisZero0004Certified, GeneralCK.Certificates.E8TAxisZero0005Certified, GeneralCK.Certificates.E8TAxisZero0006Certified, GeneralCK.Certificates.E8TAxisZero0007Certified, GeneralCK.Certificates.E8TAxisZero0008Certified, GeneralCK.Certificates.E8TAxisZero0009Certified, GeneralCK.Certificates.E8TAxisZero0010Certified, GeneralCK.Certificates.E8TAxisZero0011Certified, GeneralCK.Certificates.E8TAxisZero0012Certified, GeneralCK.Certificates.E8TAxisZero0013Certified, GeneralCK.Certificates.E8TAxisZero0015Certified, GeneralCK.Certificates.E8TAxisZero0016Certified, GeneralCK.Certificates.E8TAxisZero0017Certified, GeneralCK.Certificates.E8TAxisZero0018Certified) (piece 16 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000Certified (+17 modules: GeneralCK.Certificates.E8TAxisZero0001Certified, GeneralCK.Certificates.E8TAxisZero0002Certified, GeneralCK.Certificates.E8TAxisZero0003Certified, GeneralCK.Certificates.E8TAxisZero0004Certified, GeneralCK.Certificates.E8TAxisZero0005Certified, GeneralCK.Certificates.E8TAxisZero0006Certified, GeneralCK.Certificates.E8TAxisZero0007Certified, GeneralCK.Certificates.E8TAxisZero0008Certified, GeneralCK.Certificates.E8TAxisZero0009Certified, GeneralCK.Certificates.E8TAxisZero0010Certified, GeneralCK.Certificates.E8TAxisZero0011Certified, GeneralCK.Certificates.E8TAxisZero0012Certified, GeneralCK.Certificates.E8TAxisZero0013Certified, GeneralCK.Certificates.E8TAxisZero0015Certified, GeneralCK.Certificates.E8TAxisZero0016Certified, GeneralCK.Certificates.E8TAxisZero0017Certified, GeneralCK.Certificates.E8TAxisZero0018Certified) (piece 16 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000Certified (+17 modules: GeneralCK.Certificates.E8TAxisZero0001Certified, GeneralCK.Certificates.E8TAxisZero0002Certified, GeneralCK.Certificates.E8TAxisZero0003Certified, GeneralCK.Certificates.E8TAxisZero0004Certified, GeneralCK.Certificates.E8TAxisZero0005Certified, GeneralCK.Certificates.E8TAxisZero0006Certified, GeneralCK.Certificates.E8TAxisZero0007Certified, GeneralCK.Certificates.E8TAxisZero0008Certified, GeneralCK.Certificates.E8TAxisZero0009Certified, GeneralCK.Certificates.E8TAxisZero0010Certified, GeneralCK.Certificates.E8TAxisZero0011Certified, GeneralCK.Certificates.E8TAxisZero0012Certified, GeneralCK.Certificates.E8TAxisZero0013Certified, GeneralCK.Certificates.E8TAxisZero0015Certified, GeneralCK.Certificates.E8TAxisZero0016Certified, GeneralCK.Certificates.E8TAxisZero0017Certified, GeneralCK.Certificates.E8TAxisZero0018Certified) (piece 16 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000Certified (+17 modules: GeneralCK/Certificates/E8TAxisZero0001Certified, GeneralCK/Certificates/E8TAxisZero0002Certified, GeneralCK/Certificates/E8TAxisZero0003Certified, GeneralCK/Certificates/E8TAxisZero0004Certified, GeneralCK/Certificates/E8TAxisZero0005Certified, GeneralCK/Certificates/E8TAxisZero0006Certified, GeneralCK/Certificates/E8TAxisZero0007Certified, GeneralCK/Certificates/E8TAxisZero0008Certified, GeneralCK/Certificates/E8TAxisZero0009Certified, GeneralCK/Certificates/E8TAxisZero0010Certified, GeneralCK/Certificates/E8TAxisZero0011Certified, GeneralCK/Certificates/E8TAxisZero0012Certified, GeneralCK/Certificates/E8TAxisZero0013Certified, GeneralCK/Certificates/E8TAxisZero0015Certified, GeneralCK/Certificates/E8TAxisZero0016Certified, GeneralCK/Certificates/E8TAxisZero0017Certified, GeneralCK/Certificates/E8TAxisZero0018Certified) (piece 16 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Certified__18_q14

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0016Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0016Geometry E8TAxisZero0016CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0016GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0016GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0016GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0016GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0016GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0016GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0016GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0016EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0016GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0016EndpointWitnesses.wholeB_covers_slope
    (s := 2*sUpper+tUpper) ⟨by
      norm_num [sLower, sUpper, tLower, tUpper], le_rfl⟩
  rw [← hy]
  exact ⟨E8TAxisStableScalar.X a, E8TAxisStableScalar.X_pos ha,
    E8TAxisStableScalar.e8Theta_X ha⟩

noncomputable def certificate : E8TAxisRegularCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem inputs_range {s t : ℝ} (h : rectangle.Covers s t) : InputsInRange s t :=
  E8TAxisRegularCellCertificateSchema.inputsInRange_of_rectangle
    (by norm_num [rectangle, sLower]) (by norm_num [rectangle, tLower]) upperSlope_mem h

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  apply E8TAxisRegularCellCertificateSchema.Certificate.positiveAt certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    exact inputs_range h
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
  · exact h

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms positiveAt
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisZero0016Certified

end


