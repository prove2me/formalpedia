-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:51.856117+00:00
-- url     : https://prove2.me/theorems/9add3290-fd3a-4d4c-85cd-b6eaa8bfc116
-- title:
--   Exponent Shift Eq Level Exponent
-- statement:
--   Definitions and structural lemmas for Exponent Shift Eq Level Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentShiftEqLevelExponent.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section fin
variable (k r' : ℕ)
end fin
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA


