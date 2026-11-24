-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:21:42.469747+00:00
-- url     : https://prove2.me/theorems/f88ea649-174f-4d61-ac0e-7edd60a35e5c
-- title:
--   Exists Max Of Not Coprime
-- statement:
--   Definitions and structural lemmas for Exists Max Of Not Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ExistsMaxOfNotCoprime.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.SA
section
variable {K : Type*} [CommRing K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
include hσ hfix
end
end ReciprocityTheory.ChartRestriction.G.SA


