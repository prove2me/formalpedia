-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:59.125511+00:00
-- url     : https://prove2.me/theorems/8b255812-343f-4744-be5c-9b228522a2f0
-- title:
--   Std Gap
-- statement:
--   Definitions and structural lemmas for Std Gap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/ExceptionalGroupG2/StdGap.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
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
namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
def StdGap (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∃ h : ℝ, GapAtLeast ε lam h ∧ 2 * (n : ℝ) < h
end ReciprocityTheory.ChartRestriction.DS.G2


