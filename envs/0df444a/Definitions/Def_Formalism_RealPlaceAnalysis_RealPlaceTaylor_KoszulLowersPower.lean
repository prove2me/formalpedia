-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:36.678541+00:00
-- url     : https://prove2.me/theorems/45c25faa-04ad-482c-a740-75a9984b37d4
-- title:
--   Koszul Lowers Power
-- statement:
--   Definitions and structural lemmas for Koszul Lowers Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/KoszulLowersPower.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
noncomputable section
namespace Formalism.REAL
def coeMatrixAlt {n : ℕ} (ε : Fin n → Bool) : UJ ε → Matrix (Fin n) (Fin n) ℂ :=
  fun g => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
end Formalism.REAL


