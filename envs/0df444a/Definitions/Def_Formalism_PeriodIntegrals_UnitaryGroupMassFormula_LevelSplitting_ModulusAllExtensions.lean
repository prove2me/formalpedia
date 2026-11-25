-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ModulusAllExtensions
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ModulusAllExtensions
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:46.086603+00:00
-- url     : https://prove2.me/theorems/d233f8ab-979f-41f9-b629-9bfe0240610e
-- title:
--   Modulus All Extensions
-- statement:
--   Definitions and structural lemmas for Modulus All Extensions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ModulusAllExtensions.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_OrthogonalInvarianceOfStableRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
end PI.LevelKSplit.W.MVA


