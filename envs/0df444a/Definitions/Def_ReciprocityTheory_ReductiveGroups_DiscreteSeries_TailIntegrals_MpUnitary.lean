-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:35:31.310805+00:00
-- url     : https://prove2.me/theorems/111f13ec-3623-45bb-92ba-2a9d4e04f767
-- title:
--   Mp Unitary
-- statement:
--   Definitions and structural lemmas for Mp Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MpUnitary.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
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
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
section cont
variable {p m : ℕ}
def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))
end cont
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi


