-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:24.011794+00:00
-- url     : https://prove2.me/theorems/6e342632-7803-47db-99ef-75215c518722
-- title:
--   Eq One Of Is Of Fin Order
-- statement:
--   Definitions and structural lemmas for Eq One Of Is Of Fin Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean

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
namespace PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
def PDvd (q : R) (k : ℕ) (A : Matrix n n R) : Prop :=
  ∃ X : Matrix n n R, A = q ^ k • X
end PI.FinOrdRedOne.Core


