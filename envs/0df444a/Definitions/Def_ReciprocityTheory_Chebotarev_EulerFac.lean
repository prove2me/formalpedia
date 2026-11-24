-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
-- name    : ReciprocityTheory_Chebotarev_EulerFac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:26.859945+00:00
-- url     : https://prove2.me/theorems/5a719bb0-6c39-4069-9238-2568eb9cbb0b
-- title:
--   Euler Fac
-- statement:
--   Definitions and structural lemmas for Euler Fac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
namespace ReciprocityTheory.Cheb
def Smooth {E : Type} [Field E] [NumberField E] (S : Finset (Prm E)) (a : Ideal (𝓞 E)) : Prop :=
  ∀ q : Prm E, q.asIdeal ∣ a → q ∈ S
end ReciprocityTheory.Cheb


