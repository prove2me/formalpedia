-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SubgroupQuotientStatement
-- name    : ReciprocityTheory_DualLattices_SubgroupQuotientStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:02.807992+00:00
-- url     : https://prove2.me/theorems/dca2e2c5-3bd1-408a-af8f-f5e7bff75cf2
-- title:
--   Subgroup Quotient Statement
-- statement:
--   Definitions and structural lemmas for Subgroup Quotient Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubgroupQuotientStatement.lean

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
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
def SubgroupQuotientStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    (∃ AK : HopfOrder (C := C) R K, AK.carrier = AA.carrier.map (resK K)) ∧
    (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = AA.carrier.comap (pullQ K)) ∧
    dualLat (AA.carrier.map (resK (R := R) K)) = (dualLat AA.carrier).comap (extK K) ∧
    dualLat (AA.carrier.comap (pullQ (R := R) K)) = (dualLat AA.carrier).map (pushQ K)
end ReciprocityTheory.PGsh.L2


