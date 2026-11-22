-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
-- name    : Formalism_GL3MeanSquares_ModelCocycleExponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:17.493073+00:00
-- url     : https://prove2.me/theorems/f7c26a63-35f0-47bc-9ae3-365cab23bc59
-- title:
--   Model Cocycle Exponent
-- statement:
--   Definitions and structural lemmas for Model Cocycle Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/ModelCocycleExponent.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
def AdjointFromNorm : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    ∀ α : Oˣ, (∀ u, φ ((α : O) • u) = nm α • φ u) →
      ∀ a b, cob φ ((α : O) • a) b = cob φ a (star (α : O) • b)
def AdjointAdd : Prop :=
  ∀ (O M Q : Type) [CommRing O] [StarRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
    (φ : M → Q), (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    ∀ α α' : O, (∀ a b, cob φ (α • a) b = cob φ a (star α • b)) →
      (∀ a b, cob φ (α' • a) b = cob φ a (star α' • b)) →
      ∀ a b, cob φ ((α + α') • a) b = cob φ a (star (α + α') • b)
def SplitVanish : Prop :=
  ∀ (Z M Q : Type) [CommRing Z] [AddCommGroup M] [Module Z M] [AddCommGroup Q] [Module Z Q]
    (φ : M → Q) (a abar : Z),
    (∀ x x' y, cob φ (x + x') y = cob φ x y + cob φ x' y) →
    (∀ (z : Z) x y, cob φ (z • x) y = z • cob φ x y) →
    (∀ x y, cob φ (a • x) y = cob φ x (abar • y)) →
    IsUnit (a - abar) → (∀ u, φ (-u) = φ u) → φ 0 = 0 → (∀ x : Q, x + x = 0 → x = 0) →
    (∀ x y, cob φ x y = 0) ∧ ∀ u, φ u = 0
def IsotropicZero : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] (f : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) →
      ∀ t : ι → M, ∑ i, φ (∑ e, f e i • t e) = 0
def CrossTermsVanish : Prop :=
  ∀ (M N Q : Type) [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q] (Φ : M × N → Q),
    (∀ a a' b, cob Φ (a + a') b = cob Φ a b + cob Φ a' b) →
    (∀ x y, Φ (-x, y) = Φ (x, y)) →
    ∀ x y, cob Φ (x, 0) (0, y) + cob Φ (x, 0) (0, y) = 0
def EqualPowers : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (σ : Type) (N : ℕ)
    (f g : MvPowerSeries σ R), 0 < N →
    MvPowerSeries.constantCoeff f = 1 → MvPowerSeries.constantCoeff g = 1 → f ^ N = g ^ N → f = g
def JetsOfLogUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (U f : PowerSeries K),
    (∀ n, PowerSeries.coeff n U ∈ R) → PowerSeries.constantCoeff U = 1 →
    PowerSeries.derivative K f * U = PowerSeries.derivative K U →
    ∀ n : ℕ, 1 ≤ n → (n.factorial : K) * PowerSeries.coeff n f ∈ R
def GenusOneCharacter : Prop :=
  ∀ x : ZMod 2 × ZMod 2,
    (if x = 0 then (1 : ℤ) else -1) * (-1) ^ (x.1 + x.2).val = (-1) ^ (x.1 * x.2).val
def EpsTeichAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ε : WittVector p (AlgebraicClosure (ZMod p)),
      ε ^ (p ^ 2 - 1) = -1 → WittVector.frobenius (WittVector.frobenius ε) = -ε
def ChiPower : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A) (χ : A →* Circle),
    (∀ k ∈ K, χ k = 1) →
    (∀ z : unitary E, ((χ (ι z) : Circle) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    ∀ (t : A) (h : ℕ) (z : unitary E) (k : A), k ∈ K → t ^ h = ι z * k →
      ((χ t : Circle) : ℂ) ^ h = ∏ τ ∈ Ψ, (τ (z : E))⁻¹
def ChiModulusAll : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A) (χ : A →* Circle),
    (∀ (τ : E →+* ℂ) (x : E), τ (star x) = (starRingEnd ℂ) (τ x)) →
    (∀ k ∈ K, χ k = 1) →
    (∀ z : unitary E, ((χ (ι z) : Circle) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    ∀ (t : A) (h : ℕ) (z : unitary E) (k : A), 0 < h → k ∈ K → t ^ h = ι z * k →
      ∀ s : ℂ →+* ℂ, ‖s ((χ t : Circle) : ℂ)‖ = 1
def ModelCocycleExponent : Prop :=
  ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] (h : V → V → E) (s : E),
    (∀ x x' y, h (x + x') y = h x y + h x' y) → (∀ x y, h x y = star (h y x)) → star s = -s →
    ∀ (x y : V) (a b : E), star a = a → star b = b → h x y = (a + b * s) / 2 →
      b / 2 - (h (x + y) (x + y) - h x x - h y y) / 2 = (b - a) / 2
def ModelCocycleTwo : Prop :=
  ∀ d : ℕ, d % 8 = 7 →
    (∃ δ : ℚ_[2], δ ^ 2 = -(d : ℚ_[2])) ∧
    ∀ δ : ℚ_[2], δ ^ 2 = -(d : ℚ_[2]) →
      ‖(1 - δ) / (2 * δ)‖ ≤ 1 ∧ ‖(-(1 + δ)) / (2 * δ)‖ ≤ 1 ∧
      ∀ a b : ℚ_[2],
        ((1 - δ) / (2 * δ)) * ((a + b * δ) / 2) + ((-(1 + δ)) / (2 * δ)) * ((a - b * δ) / 2) =
          (b - a) / 2
end Formalism.HermitianLattices.ModelCocycles


