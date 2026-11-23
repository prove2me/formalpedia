-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:28.529021+00:00
-- url     : https://prove2.me/theorems/c1e22d57-3d6a-43b4-a19b-66c75d417d2d
-- title:
--   Gamma Stable Of Gamma QUnit Holds
-- statement:
--   Definitions and structural lemmas for Gamma Stable Of Gamma QUnit Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/GammaStableOfGammaQUnitHolds.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
section SlopeTestRemainingChoices
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
end SlopeTestRemainingChoices
end Formalism.CoboundaryTransfers


