-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:43.429388+00:00
-- url     : https://prove2.me/theorems/2ed672a9-6c91-4772-8888-0f82b89dba10
-- title:
--   St Local Mult Comap
-- statement:
--   Definitions and structural lemmas for St Local Mult Comap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StLocalMultComap.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights (localMult)
def LocalMultComap.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (I W : Ideal S),
    Function.Surjective σ → W.IsPrime → localMult (I.comap σ) (W.comap σ) = localMult I W
end GroundTheory.Heights₂.Heights.Targets


