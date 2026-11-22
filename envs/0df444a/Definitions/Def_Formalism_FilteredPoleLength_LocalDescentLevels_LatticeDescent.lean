-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
-- name    : Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:26.223479+00:00
-- url     : https://prove2.me/theorems/b7bff680-c6d5-4d72-8376-b765ffa23961
-- title:
--   Lattice Descent
-- statement:
--   Definitions and structural lemmas for Lattice Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeDescent.lean

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module
namespace LatticeDescentAlt
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
end LatticeDescentAlt
end Formalism.LatticeBaseChangeAlt


