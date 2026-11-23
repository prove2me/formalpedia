-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:59.325991+00:00
-- url     : https://prove2.me/theorems/9db329b1-0f43-4d6c-8d53-b5bd93b7364d
-- title:
--   Half Le Norm Lent Ctr
-- statement:
--   Definitions and structural lemmas for Half Le Norm Lent Ctr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
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
def LL (N : ℕ) (t : ℝ) : ℝ := Real.log (N * (|t| + 2))
def ctr (t : ℝ) : ℂ := 2 + t * I
def Mfun (A C : ℝ) (N : ℕ) (t : ℝ) : ℝ := |Real.log (2 * C)| + A * Real.log (4 * (N * (|t| + 2)))
end PI.EF


