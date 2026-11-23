-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ValUntiltESubOne
-- name    : ReciprocityTheory_DualLattices_ValUntiltESubOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:05.773389+00:00
-- url     : https://prove2.me/theorems/b9162d96-8be5-4367-95bf-d94685ca31c8
-- title:
--   Val Untilt ESub One
-- statement:
--   Definitions and structural lemmas for Val Untilt ESub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValUntiltESubOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Polynomial
namespace ReciprocityTheory.PGsh
section Ainf
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Ainf
end ReciprocityTheory.PGsh


