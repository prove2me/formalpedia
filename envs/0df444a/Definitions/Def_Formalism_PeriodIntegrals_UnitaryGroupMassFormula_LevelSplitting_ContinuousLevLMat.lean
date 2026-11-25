-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousLevLMat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousLevLMat
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:45.096576+00:00
-- url     : https://prove2.me/theorems/effbbf53-72d7-4047-be65-721c6346fe92
-- title:
--   Continuous Lev LMat
-- statement:
--   Definitions and structural lemmas for Continuous Lev LMat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousLevLMat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
section Af
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
end Af
end PI.LevelKSplit.W.NCL


