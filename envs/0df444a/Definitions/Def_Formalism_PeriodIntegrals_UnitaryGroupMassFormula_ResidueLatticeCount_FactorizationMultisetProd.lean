-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:50.06628+00:00
-- url     : https://prove2.me/theorems/04f39419-5128-4a33-b598-495fe4eb9fa9
-- title:
--   Factorization Multiset Prod
-- statement:
--   Definitions and structural lemmas for Factorization Multiset Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Residue
open scoped ENNReal
section Comb
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]
def intersection_update_fsHerm_neg_one (N : α → ℕ) (idx : α → ι) (s : Multiset α) (i : ι) : ℕ :=
  ((s.filter (fun a => idx a = i)).map N).prod
end Comb
section Sums
end Sums
end PI.Residue


