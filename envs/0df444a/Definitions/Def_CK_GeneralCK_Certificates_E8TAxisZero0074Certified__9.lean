-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074Certified__9
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074Certified__9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:08:47.531998+00:00
-- url     : https://prove2.me/theorems/0587a80a-22bc-40ec-bed7-ebe58104be3b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074Certified (+8 modules: GeneralCK.Certificates.E8TAxisZero0075Certified, GeneralCK.Certificates.E8TAxisZero0076Certified,…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074Certified (+8 modules: GeneralCK.Certificates.E8TAxisZero0075Certified, GeneralCK.Certificates.E8TAxisZero0076Certified, GeneralCK.Certificates.E8TAxisZero0077Certified, GeneralCK.Certificates.E8TAxisZero0078Certified, GeneralCK.Certificates.E8TAxisZero0079Certified, GeneralCK.Certificates.E8TAxisZero0080Certified, GeneralCK.Certificates.E8TAxisZero0081Certified, GeneralCK.Certificates.E8TAxisZero0082Certified)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074Certified (+8 modules: GeneralCK.Certificates.E8TAxisZero0075Certified, GeneralCK.Certificates.E8TAxisZero0076Certified, GeneralCK.Certificates.E8TAxisZero0077Certified, GeneralCK.Certificates.E8TAxisZero0078Certified, GeneralCK.Certificates.E8TAxisZero0079Certified, GeneralCK.Certificates.E8TAxisZero0080Certified, GeneralCK.Certificates.E8TAxisZero0081Certified, GeneralCK.Certificates.E8TAxisZero0082Certified)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074Certified (+8 modules: GeneralCK.Certificates.E8TAxisZero0075Certified, GeneralCK.Certificates.E8TAxisZero0076Certified, GeneralCK.Certificates.E8TAxisZero0077Certified, GeneralCK.Certificates.E8TAxisZero0078Certified, GeneralCK.Certificates.E8TAxisZero0079Certified, GeneralCK.Certificates.E8TAxisZero0080Certified, GeneralCK.Certificates.E8TAxisZero0081Certified, GeneralCK.Certificates.E8TAxisZero0082Certified) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074Certified (+8 modules: GeneralCK/Certificates/E8TAxisZero0075Certified, GeneralCK/Certificates/E8TAxisZero0076Certified, GeneralCK/Certificates/E8TAxisZero0077Certified, GeneralCK/Certificates/E8TAxisZero0078Certified, GeneralCK/Certificates/E8TAxisZero0079Certified, GeneralCK/Certificates/E8TAxisZero0080Certified, GeneralCK/Certificates/E8TAxisZero0081Certified, GeneralCK/Certificates/E8TAxisZero0082Certified).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062CertifiedArithmetic__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0075EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0076EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0077EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0078EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0079CertifiedArithmetic__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0079EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0080EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0081EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0082EndpointWitnesses

-- ===== source module GeneralCK.Certificates.E8TAxisZero0074Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0074Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0074Geometry E8TAxisZero0074CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0074GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0074GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0074GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0074GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0074GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0074GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0074GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0074EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0074GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0074EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0074Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0075Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0075Geometry E8TAxisZero0075CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0075GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0075GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0075GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0075GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0075GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0075GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0075GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0075EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0075GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0075EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0075Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0076Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0076Geometry E8TAxisZero0076CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0076GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0076GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0076GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0076GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0076GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0076GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0076GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0076EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0076GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0076EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0076Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0077Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0077Geometry E8TAxisZero0077CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0077GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0077GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0077GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0077GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0077GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0077GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0077GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0077EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0077GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0077EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0077Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0078Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0078Geometry E8TAxisZero0078CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0078GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0078GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0078GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0078GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0078GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0078GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0078GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0078EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0078GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0078EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0078Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0079Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0079Geometry E8TAxisZero0079CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0079GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0079GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0079GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0079GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0079GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0079GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0079GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0079EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0079GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0079EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0079Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0080Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0080Geometry E8TAxisZero0080CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0080GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0080GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0080GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0080GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0080GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0080GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0080GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0080EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0080GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0080EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0080Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0081Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0081Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0081Geometry E8TAxisZero0081CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0081GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0081GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0081GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0081GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0081GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0081GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0081GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0081EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0081GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0081EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0081Certified

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0082Certified =====
section

namespace GeneralCK.Certificates.E8TAxisZero0082Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0082Geometry E8TAxisZero0082CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0082GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0082GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0082GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0082GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0082GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0082GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0082GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0082EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0082GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0082EndpointWitnesses.wholeB_covers_slope
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
end GeneralCK.Certificates.E8TAxisZero0082Certified

end


