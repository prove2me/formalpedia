-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:51.163814+00:00
-- url     : https://prove2.me/theorems/86138249-b06b-4642-b647-5f44be9221ea
-- title:
--   Maj At Zero Right
-- statement:
--   Definitions and structural lemmas for Maj At Zero Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
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
namespace PI.Dv.ProjBW
open NumberField Formalism.HN
section Real
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end Real
section Zl
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end Zl
section Main
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Main
end PI.Dv.ProjBW


