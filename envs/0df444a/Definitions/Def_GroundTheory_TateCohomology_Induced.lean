-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_Induced
-- name    : GroundTheory_TateCohomology_Induced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:35.461797+00:00
-- url     : https://prove2.me/theorems/fcc0c5f6-c365-481b-8ad7-7674fc1273e5
-- title:
--   Induced
-- statement:
--   Definitions and structural lemmas for Induced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)
section Coind
variable (B : Rep.{u} k (⊥ : Subgroup G))
open scoped Classical in

noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V :=
  LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp
end Coind
end GroundTheory.GroupCoh


