-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
-- name    : ReciprocityTheory_DualLattices_CyclicRecursion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:36.420789+00:00
-- url     : https://prove2.me/theorems/414a2b41-a8c5-4fba-a7b3-c10508b13f72
-- title:
--   Cyclic Recursion
-- statement:
--   Definitions and structural lemmas for Cyclic Recursion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/CyclicRecursion.lean

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
open WittVector MvPolynomial
namespace ReciprocityTheory.PGsh
section TeichSum
variable {p : ℕ} [hp : Fact p.Prime]
end TeichSum
section Cyclic
def cycT {V : Type} [AddCommGroup V] [Module ℚ V] (o : ℕ) (P : ℚ) (La : ZMod o → V)
    (i : ZMod o) : V :=
  ∑ n ∈ Finset.range o, P⁻¹ ^ (n + 1) • La (i + ((n + 1 : ℕ) : ZMod o))
end Cyclic
end ReciprocityTheory.PGsh


