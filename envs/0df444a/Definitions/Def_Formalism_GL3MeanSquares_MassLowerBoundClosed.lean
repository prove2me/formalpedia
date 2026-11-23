-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_MassLowerBoundClosed
-- name    : Formalism_GL3MeanSquares_MassLowerBoundClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:42.059718+00:00
-- url     : https://prove2.me/theorems/9d29eaad-c980-416b-9932-e2cd959c099d
-- title:
--   Mass Lower Bound Closed
-- statement:
--   Definitions and structural lemmas for Mass Lower Bound Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/MassLowerBoundClosed.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioLowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioUpperBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Finset
namespace Formalism.HermitianLattices.SiegelMassBounds
def SiegelMassRatioThm : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio
def MassLowerBoundClosed : Prop :=
  ∀ (ε C₀ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (Lk : Submodule (RingOfIntegers K) V) (Lr : Submodule (RingOfIntegers K) V')
      (m k : ℕ) (Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ) (Dstar dstar Isig Ipi : ℝ),
    h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h Lk k →
    Formalism.HermitianLatticesTheory.IsOrthoLattice h' Lr (k - 1 + m) →
    1 ≤ Formalism.HermitianLatticesTheory.fDeg K → 1 ≤ m → 2 ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K → Real.log (Formalism.HermitianLatticesTheory.vInv K) ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → Formalism.LogVandermondeBounds.StandardLattice.PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ)) →
    0 < Formalism.HermitianLatticesTheory.mass h Lk → 0 < Formalism.HermitianLatticesTheory.mass h' Lr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ Formalism.HermitianLatticesTheory.fDeg K * Real.log (Formalism.LogVandermondeBounds.StandardLattice.zetaR M)) →
    (hidx : ((2 : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K))⁻¹ *
      (g₁ * g₂) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) →
    (hD : (2 / 3 : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K * Formalism.HermitianLatticesTheory.mass h' Lr * Isig *
      ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (Formalism.LogVandermondeBounds.StandardLattice.rowPar k (v ρ) (b ρ)) (k - 1 + m)
        ≤ Dstar) →
    (hd : dstar = Formalism.HermitianLatticesTheory.mass h Lk * Ipi * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (u ρ) k) →
    (∑ j ∈ range m, (1 / (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) * ∑ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K),
        Real.log (w ρ j * Formalism.HermitianLatticesTheory.vInv K / Real.pi))
        + m * (Real.log g₁ + Real.log g₂) - C * (L + (m : ℝ) ^ 2 * L / k)
      ≤ (1 / ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * k)) * Real.log (Dstar / dstar)
def MassUpperBoundClosed : Prop :=
  ∀ (ε C₀ C₃ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → 1 ≤ C₃ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (Lk : Submodule (RingOfIntegers K) V) (Lr : Submodule (RingOfIntegers K) V')
      (m k : ℕ) (Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ) (Dstar dstar Isig Ipi : ℝ) (dsig : ℕ → ℝ),
    h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h Lk k →
    Formalism.HermitianLatticesTheory.IsOrthoLattice h' Lr (k - 1 + m) →
    1 ≤ Formalism.HermitianLatticesTheory.fDeg K → 2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ^ 2 * L ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K → Real.log (Formalism.HermitianLatticesTheory.vInv K) ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    Real.log g₁ ≤ C₀ * L → Real.log g₂ ≤ C₀ * L →
    (∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → Formalism.LogVandermondeBounds.StandardLattice.PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
      (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) →
    0 < Formalism.HermitianLatticesTheory.mass h Lk → 0 < Formalism.HermitianLatticesTheory.mass h' Lr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ Formalism.HermitianLatticesTheory.fDeg K * Real.log (Formalism.LogVandermondeBounds.StandardLattice.zetaR M)) →
    (hidx : Isig / Ipi ≤ (2 : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) *
      (g₁ * g₂) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * m * (2 * k + m - 1) / 2)) →
    (hD : Dstar = Formalism.HermitianLatticesTheory.mass h' Lr * Isig * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), dsig ρ) →
    (h3 : ∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → 0 < dsig ρ ∧
      dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau k m (Formalism.LogVandermondeBounds.StandardLattice.rowPar k (v ρ) (b ρ)) *
      (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
        (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) →
    (hd : dstar = Formalism.HermitianLatticesTheory.mass h Lk * Ipi * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (u ρ) k) →
    (1 / ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * k)) * Real.log (Dstar / dstar) ≤ C * m * L
end Formalism.HermitianLattices.SiegelMassBounds


