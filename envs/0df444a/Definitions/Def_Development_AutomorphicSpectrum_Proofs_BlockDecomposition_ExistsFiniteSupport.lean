-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:00.594438+00:00
-- url     : https://prove2.me/theorems/8996b360-65e9-42a8-8b97-99096367da83
-- title:
--   Exists Finite Support
-- statement:
--   Definitions and structural lemmas for Exists Finite Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
namespace GlobalTheory.CompanionTheory.PRep.JacExact
section Finite
variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def avg (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] : V →ₗ[ℂ] V :=
  ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q)
end Finite
section Top
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def stabIn (τ : Representation ℂ G V) (L : Subgroup G) (x : V) : Subgroup L where
  carrier := {l | τ (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
end Top
end GlobalTheory.CompanionTheory.PRep.JacExact


