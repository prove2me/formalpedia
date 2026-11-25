-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
-- name    : GroundTheory_AutomorphicForms_CuspidalAdmissible
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:30:56.298826+00:00
-- url     : https://prove2.me/theorems/7bdf6fd2-e797-52e5-ba58-f6de7610a289
-- title:
--   Cuspidal Admissible
-- statement:
--   Definitions and structural lemmas for Cuspidal Admissible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
section Normalize
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
end Normalize
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
section DiagPow
open Cartan
theorem diagPow_mem_levi (μ : Fin n → ℤ) : diagPow F n μ ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  show (diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
  rw [coe_diagPow, diagonal_apply_ne _ this]
end DiagPow
section Cuspidal
variable (F n β) in

def leviUnipotent (γ : Fin n → ℕ) : Subgroup (levi F n β) :=
  (unipotentRadical F n γ).subgroupOf (levi F n β)
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
def IsCuspidal (σ : Representation ℂ (levi F n β) W) : Prop :=
  ∀ γ : Fin n → ℕ, (∃ i j, β i = β j ∧ γ i ≠ γ j) →
    Subsingleton (Representation.Coinvariants (σ.comp (leviUnipotent F n β γ).subtype))
def splitFun (S : Finset (Fin n)) : Fin n → ℕ := fun j => if j ∈ S then 0 else 1
instance secondCountableTopology_levi : SecondCountableTopology (levi F n β) :=
  inferInstanceAs (SecondCountableTopology (levi F n β : Set (GL (Fin n) F)))
end Cuspidal
end Parabolic
end GroundTheory.Automorphic


