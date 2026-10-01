-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellCertified
-- name    : CK_GeneralCK_Certificates_E8TAxisFirstCellCertified
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:18:27.899804+00:00
-- url     : https://prove2.me/theorems/e0ad419e-7432-44f4-ba06-3105ceec7135
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisFirstCellCertified` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisFirstCellCertified` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisFirstCellCertified` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisFirstCellCertified (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellCertified.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellCertifiedArithmetic
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPartitionKernel
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.Certificates.E8TAxisFirstCellCertified =====
section

/-! Unconditional enclosure and positivity on the exact historical first cell.
The widened coefficient boxes are outputs of checked stable interval graphs. -/

namespace GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerA_covers
    have hh := E8TAxisFirstCellGraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerB_covers
    have hh := E8TAxisFirstCellGraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerC_covers
    have hh := E8TAxisFirstCellGraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerD_covers
    have hh := E8TAxisFirstCellGraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InFirstCell s t) :
    wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeA_covers_slope (s := t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeB_covers_slope (s := 2*s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeC_covers_slope (s := s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeD_covers_slope (s := s)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh






theorem mixedBounds : MixedBounds :=
  ⟨centerEnclosed_of_contains centerBoxes_contains,
    fun _ _ h => wholeEnclosed_of_contains (wholeBoxes_contains h)⟩

theorem centeredReplay_contains {s t : ℝ} (h : InFirstCell s t) :
    data.replay.Contains (e8RegularDeltaT s t) :=
  Data.firstCell_contains rfl rfl mixedBounds.1 mixedBounds.2 h

theorem positive {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t :=
  Data.firstCell_positive rfl rfl mixedBounds.1 mixedBounds.2 replay_positive h




theorem cellPositive : E8TAxisPartitionKernel.CellPositive rectangle := by
  intro s t _ h
  exact positive h

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms mixedBounds
#print axioms centeredReplay_contains
#print axioms positive
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisFirstCellCertified

end


