-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:42.215044+00:00
-- url     : https://prove2.me/theorems/7cee69ba-6f27-44b9-8a90-2646010c52f1
-- title:
--   Phi Cas B
-- statement:
--   Definitions and structural lemmas for Phi Cas B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def casCoef (μ : Fin n → ℤ) (a b : Fin n) : ℝ :=
  (if a = b then (μ a : ℝ) ^ 2 else 0) + (if b < a then (μ a : ℝ) - μ b else 0)
end ReciprocityTheory.ChartRestriction.DS.S7


