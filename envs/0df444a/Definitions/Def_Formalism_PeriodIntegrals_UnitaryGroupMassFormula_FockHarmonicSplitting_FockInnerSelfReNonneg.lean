-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:44.641339+00:00
-- url     : https://prove2.me/theorems/65662243-859b-495f-bf88-f27105bdaed2
-- title:
--   Fock Inner Self Re Nonneg
-- statement:
--   Definitions and structural lemmas for Fock Inner Self Re Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PI.FHS
variable {σ : Type*}
def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))
end PI.FHS


