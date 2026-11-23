-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:26.463209+00:00
-- url     : https://prove2.me/theorems/8c5ca42b-d9dc-4298-a2a1-1b2300ac30c3
-- title:
--   Weighted Lattice Sum
-- statement:
--   Definitions and structural lemmas for Weighted Lattice Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.WeightedLatticeSum
open Finset
def wt (R : ℝ) (m : ℕ) : ℝ := (max 1 (((m : ℝ) - 1) / (2 * R))) ^ (-(3 / 2 : ℝ))
end Formalism.MainNotions.WeightedLatticeSum
end


