-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:00.706804+00:00
-- url     : https://prove2.me/theorems/cf699afb-93ed-40fd-a480-d613e29c3ef9
-- title:
--   Is Unit Mk Of Forall Prime
-- statement:
--   Definitions and structural lemmas for Is Unit Mk Of Forall Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.LocalUnitReduction
section
variable {K' Fr : Type*} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
  {ι : Type*} {R : ι → Type*} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
  (φ : ∀ c, Fr →ₐ[K'] R c)
end
end Formalism.L2.Pj.LocalUnitReduction


