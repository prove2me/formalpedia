-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
-- name    : Formalism_FrobeniusOrbits_HostOrbitCountSg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:04.418032+00:00
-- url     : https://prove2.me/theorems/ba8c39fe-426c-4540-b0ea-ac665e97b914
-- title:
--   Host Orbit Count Sg
-- statement:
--   Definitions and structural lemmas for Host Orbit Count Sg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/HostOrbitCountSg.lean

import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
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
def HostOrbitCountSg : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) → ∀ τ ∈ Psi e,
    orderOf φ = Nat.lcm 2 (orderOf φ.2) ∧
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ
end Formalism.FrobeniusOrbits


