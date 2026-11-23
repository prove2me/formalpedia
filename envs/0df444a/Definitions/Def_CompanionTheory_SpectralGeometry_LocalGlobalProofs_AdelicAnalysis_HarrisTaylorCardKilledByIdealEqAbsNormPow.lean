-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:30.456702+00:00
-- url     : https://prove2.me/theorems/ea2d9d7d-99e4-4174-8b79-75ed426c6b6e
-- title:
--   Harris Taylor Card Killed By Ideal Eq Abs Norm Pow
-- statement:
--   Definitions and structural lemmas for Harris Taylor Card Killed By Ideal Eq Abs Norm Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.FourierPi
section Char
variable {R : Type} [CommRing R] {ψ : R → ℂ}
theorem psi_ne (hn : ∀ x, ‖ψ x‖ = 1) (x : R) : ψ x ≠ 0 := fun h => by
  have := hn x
  simp [h] at this
theorem psi_zero (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1) : ψ 0 = 1 := by
  have := ha 0 0
  rw [add_zero] at this
  exact (mul_eq_left₀ (psi_ne hn 0)).1 this.symm
def ann (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1) (L : AddSubgroup R) :
    AddSubgroup R where
  carrier := {t | ∀ s ∈ L, ψ (s * t) = 1}
  add_mem' := by
    intro t t' h h' s hs
    rw [mul_add, ha, h s hs, h' s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psi_zero ha hn]
  neg_mem' := by
    intro t h s hs
    have e := ha (s * t) (s * -t)
    rw [← mul_add, add_neg_cancel, mul_zero, psi_zero ha hn, h s hs, one_mul] at e
    exact e.symm
end Char
section One
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ}
end One
section Many
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ} {ι : Type} [Fintype ι]
abbrev box (ι : Type) (A : Set R) : Set (ι → R) := Set.pi Set.univ fun _ => A
end Many
section Main
end Main
end GlobalTheory.CompanionTheory.SW.FourierPi


