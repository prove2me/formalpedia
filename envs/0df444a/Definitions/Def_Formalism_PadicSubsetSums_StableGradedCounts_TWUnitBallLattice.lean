-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:06.644408+00:00
-- url     : https://prove2.me/theorems/a2380216-16b7-4728-9c3b-940685671e33
-- title:
--   TWUnit Ball Lattice
-- statement:
--   Definitions and structural lemmas for TWUnit Ball Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWUnitBallLattice.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace Formalism.IrreducibleCountingLemmas.TW
namespace UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
noncomputable abbrev ballRing (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring
end UnitBall
end Formalism.IrreducibleCountingLemmas.TW


