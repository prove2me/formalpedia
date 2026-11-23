-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:59.821374+00:00
-- url     : https://prove2.me/theorems/012d7be1-d20e-4948-a7fa-afef85ad4d0b
-- title:
--   Good Height
-- statement:
--   Definitions and structural lemmas for Good Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
open DirichletCharacter
def wsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ ZerosNear χ t, (mult χ ρ : ℝ)
end PI.EF


