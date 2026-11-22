-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:03.457697+00:00
-- url     : https://prove2.me/theorems/f7642215-99f4-4986-8463-0d332f40c77d
-- title:
--   Lattice Sum Bounds
-- statement:
--   Definitions and structural lemmas for Lattice Sum Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
noncomputable def s5bA (v : ℝ) (j : ℕ) : ℝ := ((j - 1).factorial : ℝ) * (v / Real.pi) ^ j
end Formalism.HermitianLatticeCounting.P


