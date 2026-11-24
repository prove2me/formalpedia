-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PowDefs
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PowDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:20:49.474848+00:00
-- url     : https://prove2.me/theorems/d6541992-a2e3-4e0f-8059-67a156a21c94
-- title:
--   Pow Defs
-- statement:
--   Definitions and structural lemmas for Pow Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PowDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_EulerCharDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory
universe u w
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] {R : Type w} [CommMonoid R]
structure IsMultiplicativeOn (P : ℕ → Prop) (χ : (A : Rep.{u} k G) → [IsDiscreteRep A] → R) :
    Prop where

  iso : ∀ {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [Finite A],
    P (Nat.card A) → (A ≅ B) → χ A = χ B

  shortExact : ∀ {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
    [IsDiscreteRep S.X₃] [Finite S.X₂], S.ShortExact → P (Nat.card S.X₂) →
    χ S.X₂ = χ S.X₁ * χ S.X₃
end GroundTheory.ProfCoh


