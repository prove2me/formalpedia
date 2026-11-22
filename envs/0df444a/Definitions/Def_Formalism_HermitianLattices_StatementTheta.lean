-- Prove2me | Definitions.Def_Formalism_HermitianLattices_StatementTheta
-- name    : Formalism_HermitianLattices_StatementTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:07.107803+00:00
-- url     : https://prove2.me/theorems/95420813-bcf0-4288-8b30-cf75d2e5f563
-- title:
--   Statement Theta
-- statement:
--   Definitions and structural lemmas for Statement Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/StatementTheta.lean

import Mathlib
import Definitions.Def_Formalism_AlphaUniqueness_Statement
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Defs
def weilT {D : Type*} (Q : D → ℂ) (f : D → ℂ) : D → ℂ := fun γ => Q γ * f γ
def weilS {D : Type*} [AddCommGroup D] [Fintype D] (Q : D → ℂ) (f : D → ℂ) : D → ℂ :=
  fun γ => ((Real.sqrt (Fintype.card D) : ℝ) : ℂ)⁻¹ *
    ∑ δ, starRingEnd ℂ (polar Q γ δ) * f δ
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
def thetaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V)
    (τ : ℂ) : ℂ :=
  ∑' x : L, Complex.exp (Real.pi * Complex.I * τ *
    ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))
def thetaN (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (n : ℕ)
    (γ : Fin n → V) (τ : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑' x : Fin n → L, Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j,
    ((Algebra.trace ℚ K (h (γ i + x i) (γ j + x j)) : ℚ) : ℂ) * τ j i)
end Defs
def thetaE {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (Λ : Submodule ℤ W) (γ : W)
    (τ : ℂ) : ℂ :=
  ∑' x : Λ, Complex.exp (Real.pi * Complex.I * τ * ((‖γ + (x : W)‖ ^ 2 : ℝ) : ℂ))
def WeilFinite : Prop :=
  ∀ (D : Type) [AddCommGroup D] [Fintype D] (Q : D → ℂ), IsUQuad Q → Nondeg Q →
    (∀ f : D → ℂ, weilS Q (weilS Q f) = fun γ => f (-γ)) ∧
    (∀ f : D → ℂ, ∑ γ, ‖weilS Q f γ‖ ^ 2 = ∑ γ, ‖f γ‖ ^ 2) ∧
    (∀ f : D → ℂ, weilS Q (weilT Q (weilS Q (weilT Q (weilS Q (weilT Q f))))) =
      fun γ => gsum Q / ((Real.sqrt (Fintype.card D) : ℝ) : ℂ) * f (-γ))
def ThetaBasic : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      (∀ l ∈ L, thetaL h L (γ + l) τ = thetaL h L γ τ) ∧
      thetaL h L (-γ) τ = thetaL h L γ τ ∧
      (∀ g ∈ isom h, thetaL h (gmap g L) (g γ) τ = thetaL h L γ τ) ∧
      ((∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h x x) = 2 * n) →
        (∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h γ x) = n) →
        thetaL h L γ (τ + 1) =
          Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)) *
            thetaL h L γ τ) ∧
      (∀ (n : ℕ) (γs : Fin n → V) (T : Matrix (Fin n) (Fin n) ℂ), ∀ g ∈ isom h,
        thetaN h (gmap g L) n (fun i => g (γs i)) T = thetaN h L n γs T) ∧
      (∀ T : Matrix (Fin 1) (Fin 1) ℂ, thetaN h L 1 (fun _ => γ) T = thetaL h L γ (T 0 0))
def ThetaSummable : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      Summable (fun x : L => Complex.exp (Real.pi * Complex.I * τ *
        ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ)))
def ThetaSEuclid : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ W] (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (γ : W) (τ : ℂ), 0 < τ.im →
    thetaE Λ γ (-τ⁻¹) =
      (-Complex.I * τ) ^ ((Module.finrank ℝ W : ℂ) / 2) / (ZLattice.covolume Λ : ℂ) *
        ∑' μ : Formalism.H.dual Λ, Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ γ (μ : W) : ℝ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I * τ * ((‖(μ : W)‖ ^ 2 : ℝ) : ℂ))
end Formalism.HermitianLatticesTheory


