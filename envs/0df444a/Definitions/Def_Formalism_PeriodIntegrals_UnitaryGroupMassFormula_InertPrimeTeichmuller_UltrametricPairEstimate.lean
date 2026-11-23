-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_UltrametricPairEstimate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_UltrametricPairEstimate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:53.756394+00:00
-- url     : https://prove2.me/theorems/3de1aaf7-1cec-4583-82f3-bebc1cb100c9
-- title:
--   Ultrametric Pair Estimate
-- statement:
--   Definitions and structural lemmas for Ultrametric Pair Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/UltrametricPairEstimate.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
namespace PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
def gens (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}
end PI.OkpW


