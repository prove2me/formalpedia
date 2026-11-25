-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupTate
-- name    : GroundTheory_TateCohomology_CupTate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:31:26.407202+00:00
-- url     : https://prove2.me/theorems/de8b2974-9f86-454e-bbd1-86819dff889b
-- title:
--   Cup Tate
-- statement:
--   Definitions and structural lemmas for Cup Tate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩
noncomputable def tateCupTensor (A B : Rep.{u} k G) (p q : ℤ) :
    TensorProduct k (tateCohomology A p) (tateCohomology B q) →ₗ[k] tateCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (tateCup p q A B (p + q) rfl)
end GroundTheory.GroupCoh


