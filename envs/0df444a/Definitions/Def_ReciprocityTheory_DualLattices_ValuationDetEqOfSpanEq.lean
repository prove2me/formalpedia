-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
-- name    : ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:42.739803+00:00
-- url     : https://prove2.me/theorems/323334c0-e381-45fe-a65c-c26e9e1b0553
-- title:
--   Valuation Det Eq Of Span Eq
-- statement:
--   Definitions and structural lemmas for Valuation Det Eq Of Span Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]
end ReciprocityTheory.PGsh.L2


