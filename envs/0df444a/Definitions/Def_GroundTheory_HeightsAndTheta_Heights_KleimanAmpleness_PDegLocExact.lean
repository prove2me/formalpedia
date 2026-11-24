-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:14:48.625533+00:00
-- url     : https://prove2.me/theorems/1f27fda2-756f-407c-a8f3-8146495ae602
-- title:
--   PDeg Loc Exact
-- statement:
--   Definitions and structural lemmas for PDeg Loc Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
namespace DegLocExact
variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]
end DegLocExact
end
end GroundTheory.Heights₂.Heights.Kleiman


