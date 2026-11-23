-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
-- name    : ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:10.44112+00:00
-- url     : https://prove2.me/theorems/083bebfd-5f91-4304-a42c-78a25fd4503e
-- title:
--   Aeval Is Weighted Homogeneous
-- statement:
--   Definitions and structural lemmas for Aeval Is Weighted Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
def blockIndexWeight {B n : ℕ} (b : Fin B) : Fin B × Fin n → ℕ := fun p => if p.1 = b then 1 else 0
end ReciprocityTheory.MultiplicativeHeights


