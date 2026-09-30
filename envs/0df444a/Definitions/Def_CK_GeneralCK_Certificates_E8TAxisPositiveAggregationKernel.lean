-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
-- name    : CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:33:56.432513+00:00
-- url     : https://prove2.me/theorems/1a405077-f011-45c9-bf0e-88f07fbd7f87
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisPositiveAggregationKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisPositiveAggregationKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisPositiveAggregationKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisPositiveAggregationKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisPositiveAggregationKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPartitionKernel
import Definitions.Def_GeneralCK_E8_reusable_cell_interface

-- ===== source module GeneralCK.Certificates.E8TAxisPositiveAggregationKernel =====
section

/-! Local aggregation only.  None of these declarations asserts that the
positive-t production cells cover the full t-axis domain. -/

namespace GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

open E8TAxisPartitionKernel

theorem cellPositive_of_allLeaves {tree : Tree} {r : Rect}
    (h : AllLeaves CellPositive tree r) : CellPositive r := by
  intro s t hadm hcover
  obtain ⟨leaf, hleaf, hpoint⟩ := locate_leaf h hcover
  exact hleaf s t hadm hpoint



theorem cellsPositive_nil : CellsPositive [] := by
  intro r hr
  simp at hr

theorem cellsPositive_cons {r : Rect} {rs : List Rect}
    (hr : CellPositive r) (hrs : CellsPositive rs) : CellsPositive (r :: rs) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · simpa only [h] using hr
  · exact hrs x h

theorem cellsPositive_append {xs ys : List Rect}
    (hx : CellsPositive xs) (hy : CellsPositive ys) : CellsPositive (xs ++ ys) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact hx r h
  · exact hy r h

#print axioms cellPositive_of_allLeaves
#print axioms cellsPositive_cons
#print axioms cellsPositive_append

end GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

end


