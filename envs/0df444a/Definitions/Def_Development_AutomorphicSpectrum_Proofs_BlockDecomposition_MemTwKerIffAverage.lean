-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:35.164803+00:00
-- url     : https://prove2.me/theorems/890c0a15-bde7-458c-b316-c47209bde6ad
-- title:
--   Mem Tw Ker Iff Average
-- statement:
--   Definitions and structural lemmas for Mem Tw Ker Iff Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
section Coset
variable {H V : Type} [Group H] [AddCommGroup V]
end Coset
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
def twOrbit (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) (t : L) : V :=
  (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) x
def stabKer (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) : Subgroup L where
  carrier := {l | ρ (l : G) x = x ∧ θ l = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, by rw [map_mul, ha', hb', one_mul]⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, by rw [map_inv, ha', inv_one]⟩
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
section Top
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Top
end GlobalTheory.CompanionTheory.TwistedAverage


