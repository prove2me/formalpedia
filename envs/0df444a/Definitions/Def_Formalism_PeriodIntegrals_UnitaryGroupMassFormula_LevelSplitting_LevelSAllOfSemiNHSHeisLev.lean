-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:10.703395+00:00
-- url     : https://prove2.me/theorems/46feed5d-792c-5086-affa-515b21ea0e18
-- title:
--   Level SAll Of Semi NHSHeis Lev
-- statement:
--   Definitions and structural lemmas for Level SAll Of Semi NHSHeis Lev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
section Ext
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]
end Ext
end PI.LevelKSplit.W.NC


