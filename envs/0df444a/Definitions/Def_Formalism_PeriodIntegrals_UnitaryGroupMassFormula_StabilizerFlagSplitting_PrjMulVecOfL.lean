-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:49.687131+00:00
-- url     : https://prove2.me/theorems/a1cb463f-30a2-4219-a0bf-dd4cc956fda9
-- title:
--   Prj Mul Vec Of L
-- statement:
--   Definitions and structural lemmas for Prj Mul Vec Of L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.StabSplit.Proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
def prj (H : Matrix n n ℂ) (Y : Matrix n ι ℂ) : Matrix n n ℂ := Y * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H)
variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)
end PI.StabSplit.Proj


