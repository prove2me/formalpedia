-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
-- name    : GroundTheory_AutomorphicForms_FiniteLengthLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:26.003865+00:00
-- url     : https://prove2.me/theorems/64f3537d-d33e-4b46-bd11-1501c126c4ee
-- title:
--   Finite Length Lattice
-- statement:
--   Definitions and structural lemmas for Finite Length Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean

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
noncomputable section
namespace GroundTheory.Automorphic
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
def HasFiniteLength (ρ : Representation ℂ G V) : Prop :=
  IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule
variable {ρ : Representation ℂ G V}
section MapComap
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
def subrepMap (f : Representation.IntertwiningMap ρ σ) (A : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, A.apply_mem_toSubmodule g hx, Representation.IntertwiningMap.isIntertwining _ _ f g x⟩
def subrepComap (f : Representation.IntertwiningMap ρ σ) (B : Subrepresentation σ) :
    Subrepresentation ρ where
  toSubmodule := B.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g x hx := by
    show f (ρ g x) ∈ B.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hx
end MapComap
section Filtration
end Filtration
end GroundTheory.Automorphic


