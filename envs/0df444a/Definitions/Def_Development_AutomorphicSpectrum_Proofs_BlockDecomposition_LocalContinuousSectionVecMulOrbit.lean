-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:11.684292+00:00
-- url     : https://prove2.me/theorems/82e8723b-d921-45d2-a9bc-71bfd1ed702b
-- title:
--   Local Continuous Section Vec Mul Orbit
-- statement:
--   Definitions and structural lemmas for Local Continuous Section Vec Mul Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
namespace GlobalTheory.CompanionTheory.OrbitSection
section Shear
variable {k : Type} [Field k] {n : ℕ}
noncomputable def shear (j : Fin n) (c : k) (ζ ξ : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + c • vecMulVec (Pi.single j 1) (ξ - ζ)
theorem shear_mul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    shear j (ζ j)⁻¹ ζ ξ * shear j (-(ξ j)⁻¹) ζ ξ = 1 := by
  have hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ)
      = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    simp
  have hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0 := by
    field_simp
    ring
  have key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E →
      (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 := by
    intro E hEE
    have : (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E)
        = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]
      module
    rw [this, hc, zero_smul, add_zero]
  exact key _ hE
open Classical in

noncomputable def orbitSection (j : Fin n) (ζ ξ : Fin n → k) : GL (Fin n) k :=
  if h : ζ j ≠ 0 ∧ ξ j ≠ 0 then
    ⟨shear j (ζ j)⁻¹ ζ ξ, shear j (-(ξ j)⁻¹) ζ ξ, shear_mul_shear j ζ ξ h.1 h.2,
      mul_eq_one_comm.mp (shear_mul_shear j ζ ξ h.1 h.2)⟩
  else 1
end Shear
section Top
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}
end Top
end GlobalTheory.CompanionTheory.OrbitSection


