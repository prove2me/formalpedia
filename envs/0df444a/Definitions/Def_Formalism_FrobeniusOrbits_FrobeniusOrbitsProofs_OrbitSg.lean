-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:09:39.931133+00:00
-- url     : https://prove2.me/theorems/3a2f5072-bc58-45a9-9887-bfe00bec0ecd
-- title:
--   Orbit Sg
-- statement:
--   Definitions and structural lemmas for Orbit Sg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.FrobeniusOrbits
namespace OrbitSg
def emb {e : ℕ} (τ : GG e) (x : ℤˣ × HGrp e) : GG e :=
  ((if x.1 = 1 then 1 else (sg e).1) * τ.1, x.2 * τ.2)
end OrbitSg
open OrbitSg
end Formalism.FrobeniusOrbits


