-- Prove2me | Definitions.Def_CK_GeneralCK_FourMomentScalarBounds
-- name    : CK_GeneralCK_FourMomentScalarBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:59:31.501163+00:00
-- url     : https://prove2.me/theorems/a6849187-91a1-4a7e-bc3d-014a70b2da12
-- title:
--   Courtade–Kumar proof module `GeneralCK.FourMomentScalarBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FourMomentScalarBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FourMomentScalarBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FourMomentScalarBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FourMomentScalarBounds.lean)

import Definitions.Def_CK_GeneralCK_Reflection
import Definitions.Def_CK_GeneralCK_CorrectionGlobalConvexity
import Definitions.Def_CK_GeneralCK_FourMomentLowerBound

namespace GeneralCK.InteriorLaw
open Correction
variable {ι : Type*} [Fintype ι]

/-- All analytic and boundary steps in LB1 are proved. Its three remaining
scalar sign inputs are stated explicitly for certificate replacement. -/
theorem fourMomentLowerBound_le_cost_of_scalar_bounds (μ : InteriorLaw ι)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :
    fourMomentLowerBound μ.a μ.b μ.e μ.f ≤ μ.cost :=
  μ.fourMomentLowerBound_le_cost
    (fun _ _ hu hu' hv hv' => Reflection.atom_reflection_of_positive_curvature_nonneg href hu hu' hv hv')
    (convexOn_entropyCorrection_square hleft hdet)

end GeneralCK.InteriorLaw


