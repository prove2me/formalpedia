-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:04.76607+00:00
-- url     : https://prove2.me/theorems/77ab711b-8eac-4c66-b078-1a906f8610d3
-- title:
--   UHMul Inv
-- statement:
--   Definitions and structural lemmas for UHMul Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/UHMulInv.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
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
section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end herm
section hpk
variable (k r : ℕ)
end hpk
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA


