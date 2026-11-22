-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:39.238777+00:00
-- url     : https://prove2.me/theorems/c3a158b1-0358-4de6-8649-4bd4f90b8281
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}
abbrev blR (ε : Fin N → Bool) :
    Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ ≃ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (blk ε)
section blocks
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end blocks
end PI.WeylForKWork


