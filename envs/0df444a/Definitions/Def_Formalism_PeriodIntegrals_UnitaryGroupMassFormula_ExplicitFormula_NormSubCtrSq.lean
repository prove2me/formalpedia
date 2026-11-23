-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:17.728247+00:00
-- url     : https://prove2.me/theorems/f8efdc60-e651-403f-becf-b0715b0efbfa
-- title:
--   Norm Sub Ctr Sq
-- statement:
--   Definitions and structural lemmas for Norm Sub Ctr Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
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
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
def DZ (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ := {ρ | ρ ∈ closedBall (ctr t) (11 / 4) ∧ Lent χ ρ = 0}
end PI.EF


