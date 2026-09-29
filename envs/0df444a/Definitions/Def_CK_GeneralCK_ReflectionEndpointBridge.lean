-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionEndpointBridge
-- name    : CK_GeneralCK_ReflectionEndpointBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:14.952601+00:00
-- url     : https://prove2.me/theorems/5cfdb6a1-4791-40e1-add7-99e90c4d7575
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionEndpointBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionEndpointBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionEndpointBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionEndpointBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionEndpointBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_RegularReflectionExpressionJet
import Definitions.Def_CK_GeneralCK_ReflectionNormalized

-- ===== source module GeneralCK.ReflectionEndpointBridge =====
section

/-!
# Endpoint-safe reflection bridge

The compact reflection expression uses the ratio `e / (a * (1 - z) / 2)`
and therefore cannot be evaluated on a closed certificate box with upper
endpoint `z = 1`.  `RegularReflectionExpression.normalizedValue` uses the
analytic signed contact instead and is defined on that closed box.

The reflection reduction itself only asks for `z < 1`.  Thus a certificate
for the regular expression on a box closed at `1`, together with the strict
physical-side hypothesis, proves the required raw curvature statement.
-/

namespace GeneralCK.Reflection

theorem curvature_pos_of_regular_normalizedValue_pos {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1)
    (hpos : 0 < Certificates.RegularReflectionExpression.normalizedValue a z) :
    0 < curvature a (a * z) := by
  apply curvature_pos_of_normalizedValue_pos ha ha' hz hz'
  rw [← Certificates.RegularReflectionExpression.normalizedValue_eq ha ha' hz hz']
  exact hpos

#print axioms curvature_pos_of_regular_normalizedValue_pos

end GeneralCK.Reflection

end


