-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogStep
-- name    : Formalism_GaussJetBounds_GaussJetProofs_LogStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:58.79002+00:00
-- url     : https://prove2.me/theorems/875fd5ef-cb19-4c11-bd9a-55b6515f2ec8
-- title:
--   Log Step
-- statement:
--   Definitions and structural lemmas for Log Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogStep.lean

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
namespace Formalism.DworkPowerSeriesWeights
open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)
end Formalism.DworkPowerSeriesWeights


