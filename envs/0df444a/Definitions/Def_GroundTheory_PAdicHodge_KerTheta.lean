-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_KerTheta
-- name    : GroundTheory_PAdicHodge_KerTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:32.871136+00:00
-- url     : https://prove2.me/theorems/e0369ac0-9df1-46bc-b912-523bc9668d86
-- title:
--   Ker Theta
-- statement:
--   Definitions and structural lemmas for Ker Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
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
namespace GroundTheory.PAdicHodge
open WittVector
section Adic
variable {R : Type*} [CommRing R]
end Adic
section WittPerfect
variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]
end WittPerfect
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
section Integers
variable {p}
end Integers
section Tilt
def ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) : 𝒪♭ :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP 𝒪 p) p)
local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)
end Tilt
end IsPerfectoidField
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
section Kernel
end Kernel
section WittTilt
end WittTilt
end IsPerfectoidField
end GroundTheory.PAdicHodge


