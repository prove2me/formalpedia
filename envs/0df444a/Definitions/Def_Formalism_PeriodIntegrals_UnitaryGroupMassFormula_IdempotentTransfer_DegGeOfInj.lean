-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:00.795491+00:00
-- url     : https://prove2.me/theorems/b4970445-b459-4bac-a0ac-15e9a4a94a2a
-- title:
--   Deg Ge Of Inj
-- statement:
--   Definitions and structural lemmas for Deg Ge Of Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegGeOfInj.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.Tr
open Formalism.HN
section Dense
variable {ι : Type} [Fintype ι] {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
end Dense
section Inj
variable {R : Type} [Ring R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
end Inj
end PI.Dv.Tr


