-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:16:54.895813+00:00
-- url     : https://prove2.me/theorems/d2bda02e-43ff-4ee4-8067-21a929914306
-- title:
--   Norm Fixed Unitary Entry Le One
-- statement:
--   Definitions and structural lemmas for Norm Fixed Unitary Entry Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
def C0 (k : ℕ) (s : ℝ) (ν : Measure (Mt k 0)) : ℝ≥0∞ :=
  ∫⁻ x, (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) ∂ν
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0


