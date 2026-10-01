-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeAggregate
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeAggregate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:54:26.189468+00:00
-- url     : https://prove2.me/theorems/40232da6-4f60-4754-9fdc-487fb52d84a0
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeAggregate.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleImplicitDerivativeAdapters
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsActualSign

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate =====
section

/-! Sound bridge aggregation from future proof-bearing 256-cell certificates.
The external Fraction interval table is not imported or trusted. -/

namespace GeneralCK
open Certificates.Reflection

/-- Future Lean cell proofs plus the checked true derivative formula make
the exact double-cap bridge slope strictly increasing in `x`. -/
theorem doubleCapBridgeSlope_strictMonoOn_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression) :
    StrictMonoOn doubleCapBridgeSlope
      (Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) := by
  have hCont : ContinuousOn doubleCapBridgeSlope
      (Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) := by
    intro x hx
    exact (doubleCapBridgeSlope_hasDerivAt_on_high_middle hx).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hCont
  intro x hx
  exact doubleCapBridge_true_deriv_pos_of_256_cells
    (fun z hz => doubleCapBridgeSlope_hasDerivAt_on_high_middle hz)
    hCells (interior_subset hx)

/-- The checked 7/16 endpoint sign and future 256 Lean derivative cells
imply the exact high-branch slope bias is nonnegative on the bridge. -/
theorem doubleCapBridgeSlope_nonneg_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 ≤ doubleCapBridgeSlope x := by
  have hEndpoint : 0 ≤ doubleCapBridgeSlope (1 / 8 : ℝ) := by
    simpa only [doubleCapBridgeSlope] using
      (doubleCapHighTailSeven_bias_nonneg (x := (1 / 8 : ℝ))
        (by norm_num) (by norm_num))
  by_cases heq : x = (1 / 8 : ℝ)
  · simpa only [heq] using hEndpoint
  · have hlt : (1 / 8 : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm heq)
    have hMono := doubleCapBridgeSlope_strictMonoOn_of_256_cells hCells
      (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) hx hlt
    exact hEndpoint.trans hMono.le

#print axioms doubleCapBridgeSlope_strictMonoOn_of_256_cells
#print axioms doubleCapBridgeSlope_nonneg_of_256_cells

end GeneralCK

end


