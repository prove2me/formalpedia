-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- name    : ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:18.715905+00:00
-- url     : https://prove2.me/theorems/e0c0a647-fe9e-4dcb-8a80-e26ac5ce1dbd
-- title:
--   Is Unit Det Of Span Eq
-- statement:
--   Definitions and structural lemmas for Is Unit Det Of Span Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
end ReciprocityTheory.PGsh.L2


