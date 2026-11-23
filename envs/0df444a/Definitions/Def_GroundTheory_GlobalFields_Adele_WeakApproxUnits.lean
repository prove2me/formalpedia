-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
-- name    : GroundTheory_GlobalFields_Adele_WeakApproxUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:24.418081+00:00
-- url     : https://prove2.me/theorems/312c8a71-28f8-4280-a8f5-2e8bcbefd055
-- title:
--   Weak Approx Units
-- statement:
--   Definitions and structural lemmas for Weak Approx Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApproxUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
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
open IsDedekindDomain NumberField Topology
variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
end GroundTheory.Global


