-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:29.969653+00:00
-- url     : https://prove2.me/theorems/bc5694c2-ef2d-4336-a2a6-467752cef884
-- title:
--   Bridge NGLQ
-- statement:
--   Definitions and structural lemmas for Bridge NGLQ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeNGLQ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeNGLQ
open MeasureTheory Matrix
open scoped ENNReal
def S1 : Prop :=
  ∀ (O : Type) [CommRing O] [IsPrincipalIdealRing O]
    (D : Type) [AddCommGroup D] [Module O D] [Finite D]
    (D' : Type) [AddCommGroup D'] [Module O D'] [Finite D']
    (g : ℕ) (s : Fin g → D), Submodule.span O (Set.range s) = ⊤ →
      Nat.card (Submodule O D) ≤ Nat.card D ^ g ∧ Nat.card (D →ₗ[O] D') ≤ Nat.card D' ^ g
def S3 : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] [LocallyCompactSpace K] [ContinuousStar K] [MeasurableSpace K] [BorelSpace K],
    (∃ x : K, star x ≠ x) →
    ∀ (n m : ℕ) (A : GL (Fin m) K) (c : ℝ≥0∞),
      (∃ μ : Measure K, μ.IsAddHaarMeasure ∧
        ∀ T : Set K, MeasurableSet T →
          μ ((fun y => (A : Matrix (Fin m) (Fin m) K).det * y) '' T) = c * μ T) →
      (∀ [MeasurableSpace (Matrix (Fin n) (Fin m) K)] [BorelSpace (Matrix (Fin n) (Fin m) K)]
          (ν : Measure (Matrix (Fin n) (Fin m) K)), ν.IsAddHaarMeasure →
          ∀ S : Set (Matrix (Fin n) (Fin m) K), MeasurableSet S →
            ν ((fun X => X * (A : Matrix (Fin m) (Fin m) K)) '' S) = c ^ n * ν S) ∧
      (∀ [MeasurableSpace (selfAdjoint (Matrix (Fin m) (Fin m) K))]
          [BorelSpace (selfAdjoint (Matrix (Fin m) (Fin m) K))]
          (ν : Measure (selfAdjoint (Matrix (Fin m) (Fin m) K))), ν.IsAddHaarMeasure →
          ∀ S : Set (selfAdjoint (Matrix (Fin m) (Fin m) K)), MeasurableSet S →
            ν {H' | ∃ H ∈ S, (H' : Matrix (Fin m) (Fin m) K) =
                (A : Matrix (Fin m) (Fin m) K)ᴴ * (H : Matrix (Fin m) (Fin m) K) *
                  (A : Matrix (Fin m) (Fin m) K)} = c ^ m * ν S)
def HaarScalingSplit : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F],
    ∀ (n m : ℕ) (A₁ A₂ : GL (Fin m) F) (c₁ c₂ : ℝ≥0∞),
      (∃ μ : Measure F, μ.IsAddHaarMeasure ∧ ∀ T : Set F, MeasurableSet T →
          μ ((fun y => (A₁ : Matrix (Fin m) (Fin m) F).det * y) '' T) = c₁ * μ T) →
      (∃ μ : Measure F, μ.IsAddHaarMeasure ∧ ∀ T : Set F, MeasurableSet T →
          μ ((fun y => (A₂ : Matrix (Fin m) (Fin m) F).det * y) '' T) = c₂ * μ T) →
      (∀ [MeasurableSpace (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)]
          [BorelSpace (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)]
          (ν : Measure (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)), ν.IsAddHaarMeasure →
          ∀ S : Set (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F), MeasurableSet S →
            ν ((fun X => (X.1 * (A₁ : Matrix (Fin m) (Fin m) F), X.2 * (A₂ : Matrix (Fin m) (Fin m) F))) '' S)
              = (c₁ * c₂) ^ n * ν S) ∧
      (∀ [MeasurableSpace (Matrix (Fin m) (Fin m) F)] [BorelSpace (Matrix (Fin m) (Fin m) F)]
          (ν : Measure (Matrix (Fin m) (Fin m) F)), ν.IsAddHaarMeasure →
          ∀ S : Set (Matrix (Fin m) (Fin m) F), MeasurableSet S →
            ν ((fun H => (A₂ : Matrix (Fin m) (Fin m) F)ᵀ * H * (A₁ : Matrix (Fin m) (Fin m) F)) '' S)
              = (c₁ * c₂) ^ m * ν S)
open Classical in

def HermitianQuadricInertCount : Prop :=
  ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (d : ℕ), 1 ≤ d → ∀ (H : Matrix (Fin d) (Fin d) K),
      (∀ i j, H j i = H i j ^ Fintype.card F) → H.det ≠ 0 →
      ∀ c : F,
        (Nat.card {y : Fin d → K //
            ∑ i, ∑ j, y i ^ Fintype.card F * H i j * y j = algebraMap F K c} : ℤ) =
          if c = 0 then
            (Fintype.card F : ℤ) ^ (2 * d - 1) +
              (-1) ^ d * ((Fintype.card F : ℤ) ^ d - (Fintype.card F : ℤ) ^ (d - 1))
          else (Fintype.card F : ℤ) ^ (2 * d - 1) - (-1) ^ d * (Fintype.card F : ℤ) ^ (d - 1)
open Classical in

def HermitianQuadricSplitCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (d : ℕ), 1 ≤ d → ∀ (M : Matrix (Fin d) (Fin d) F),
    M.det ≠ 0 → ∀ c : F,
      (Nat.card {y : (Fin d → F) × (Fin d → F) // ∑ i, ∑ j, y.2 i * M i j * y.1 j = c} : ℤ) =
        if c = 0 then
          (Fintype.card F : ℤ) ^ (2 * d - 1) + (Fintype.card F : ℤ) ^ d - (Fintype.card F : ℤ) ^ (d - 1)
        else (Fintype.card F : ℤ) ^ (2 * d - 1) - (Fintype.card F : ℤ) ^ (d - 1)
def S4 : Prop := HermitianQuadricInertCount ∧ HermitianQuadricSplitCount
def GaussSum : Prop :=
  ∀ (R : Type) [CommRing R] [Fintype R] [StarRing R] (Φ : AddChar R ℂ),
    (∀ z : R, (∀ y : R, Φ (y * z + star (y * z)) = 1) → z = 0) →
    ∀ (ρ : ℕ) (H : Matrix (Fin ρ) (Fin ρ) R), Hᴴ = H → IsUnit H.det →
    ∀ χ : AddChar (Fin ρ → R) ℂ,
      ‖∑ u : Fin ρ → R, Φ (star u ⬝ᵥ (H *ᵥ u)) * χ u‖ ^ 2 ≤ (Fintype.card R : ℝ) ^ ρ
end Formalism.MainNotions.BridgeNGLQ


