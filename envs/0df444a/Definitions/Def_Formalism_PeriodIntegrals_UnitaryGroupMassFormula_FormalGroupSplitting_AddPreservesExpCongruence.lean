-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:41.047704+00:00
-- url     : https://prove2.me/theorems/48aa0e97-1d06-4bfe-b3d7-d447fcd1db79
-- title:
--   Add Preserves Exp Congruence
-- statement:
--   Definitions and structural lemmas for Add Preserves Exp Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
def expT (f : MvPowerSeries σ K) (N : ℕ) : MvPowerSeries σ K :=
  ∑ n ∈ range N, ((n.factorial : K)⁻¹) • f ^ n
end PI.FglPhSplit.Wk
end


