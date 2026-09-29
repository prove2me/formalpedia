-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneQuotientDefs
-- name    : CK_GeneralCK_PsiEndpointPlaneQuotientDefs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:19.174743+00:00
-- url     : https://prove2.me/theorems/260c0389-996e-4b87-90aa-d1c2d2166620
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneQuotientDefs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneQuotientDefs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneQuotientDefs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneQuotientDefs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneQuotientDefs.lean)

import Definitions.Def_CK_GeneralCK_LogSum
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneNoFold

-- ===== source module GeneralCK.PsiEndpointPlaneQuotientDefs =====
section

namespace GeneralCK.PsiEndpointPlane

noncomputable def naturalCost (x y : ℝ) : ℝ := Real.log 2 * interiorCost x y

noncomputable def quotient (A B x y : ℝ) : ℝ :=
  (naturalCost x y + A * Real.binEntropy x + B * Real.binEntropy y) / (y - x)

noncomputable def contactLevel1 (A B x y : ℝ) : ℝ :=
  A * Real.log x + B * Real.log y + (x - y) ^ 2 / (2 * x * y)

noncomputable def contactLevel0 (A B x y : ℝ) : ℝ :=
  A * Real.log (1 - x) + B * Real.log (1 - y) + (x - y) ^ 2 / (2 * (1 - x) * (1 - y))

def triangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}

end GeneralCK.PsiEndpointPlane

end


