-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:40.384137+00:00
-- url     : https://prove2.me/theorems/96fab514-f56c-55d0-a1b7-a0cc7c77e67f
-- title:
--   PVert Point Nagata
-- statement:
--   Definitions and structural lemmas for PVert Point Nagata, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
namespace VerticalPointNagata
variable {T : Type} [Fintype T]
abbrev comp (n : ℕ) (f : MRing (fun _ : Unit => T)) : MRing (fun _ : Unit => T) :=
  weightedHomogeneousComponent (Inter.LocRingPow.multiDegWeight (fun _ : Unit => T)) (fun _ => n) f
end VerticalPointNagata
end
end GroundTheory.Heights₂.Heights


