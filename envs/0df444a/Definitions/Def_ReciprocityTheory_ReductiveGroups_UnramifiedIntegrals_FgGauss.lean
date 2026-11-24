-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:16.797145+00:00
-- url     : https://prove2.me/theorems/0c65524d-67f3-4de8-a9e6-0477539904b0
-- title:
--   Fg Gauss
-- statement:
--   Definitions and structural lemmas for Fg Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def LeadAt (f : PowerSeries K) (r : ℝ) (i : ℕ) : Prop :=
  0 < r ∧ (∀ n, ‖coeff n f‖ ≤ r) ∧ (∀ n, n < i → ‖coeff n f‖ < r) ∧ ‖coeff i f‖ = r
end ReciprocityTheory.ChartRestriction.L1


