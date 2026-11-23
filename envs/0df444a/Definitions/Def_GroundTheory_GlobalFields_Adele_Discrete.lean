-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
-- name    : GroundTheory_GlobalFields_Adele_Discrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:32.5585+00:00
-- url     : https://prove2.me/theorems/8e4d6bb9-eff2-42fc-b5f6-5517909efaee
-- title:
--   Discrete
-- statement:
--   Definitions and structural lemmas for Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
noncomputable def fundamentalSet : Set 𝔸[K] :=
  fundamentalSetInfinite K ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))
end GroundTheory.Global


