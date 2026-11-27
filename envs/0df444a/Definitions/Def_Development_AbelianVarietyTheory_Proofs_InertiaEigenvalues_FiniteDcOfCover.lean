-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:39.126488+00:00
-- url     : https://prove2.me/theorems/c6d9db50-b7a7-5f51-bfca-3e79c7d8d90c
-- title:
--   Finite Dc Of Cover
-- statement:
--   Definitions and structural lemmas for Finite Dc Of Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
def dcSetoid (Γ K : Subgroup G) : Setoid G := GlobalTheory.DoubleCosetSetoid.doubleCosetSetoid Γ K
abbrev DC (Γ K : Subgroup G) : Type _ := Quotient (dcSetoid Γ K)
def stabCard (Γ K : Subgroup G) (t : G) : ℕ := Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
def mass (Γ K : Subgroup G) : ℚ := ∑ᶠ c : DC Γ K, ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹
end GlobalTheory.UnimodMass
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
def dcConj (Γ K : Subgroup G) (h : G) : DC Γ (K.map (MulAut.conj h).toMonoidHom) ≃ DC Γ K :=
  Quotient.congr (Equiv.mulRight h) (by
    intro a b
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      rw [Subgroup.mem_map_equiv] at hκ
      refine ⟨γ, hγ, _, hκ, ?_⟩
      simp [e, MulAut.conj_symm_apply, mul_assoc]
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      refine ⟨γ, hγ, h * κ * h⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_map_equiv]
        simpa [MulAut.conj_symm_apply, mul_assoc] using hκ
      · have e' : b = γ * a * h * κ * h⁻¹ := by
          have := congrArg (· * h⁻¹) e
          simpa [mul_assoc] using this
        rw [e']
        simp [mul_assoc])
end GlobalTheory.UnimodMass


