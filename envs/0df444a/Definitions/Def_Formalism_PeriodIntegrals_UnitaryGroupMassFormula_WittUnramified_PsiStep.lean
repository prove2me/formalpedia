-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:12.841441+00:00
-- url     : https://prove2.me/theorems/8a39fb98-3693-4246-b9eb-63075e1be383
-- title:
--   Psi Step
-- statement:
--   Definitions and structural lemmas for Psi Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/PsiStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]
end PI.WittUnramWork


