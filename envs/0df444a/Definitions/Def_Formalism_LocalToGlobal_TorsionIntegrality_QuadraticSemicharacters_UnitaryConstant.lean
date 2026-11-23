-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:09.283918+00:00
-- url     : https://prove2.me/theorems/d10c702d-7f99-4c98-902c-20a2e495ea60
-- title:
--   Unitary Constant
-- statement:
--   Definitions and structural lemmas for Unitary Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/UnitaryConstant.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Objects
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def cayC (Ae : V ≃ₗ[ℂ] V) (x : V) : V := Ae.symm x - (1 / 2 : ℂ) • x
def phiC (H : Sesq V) (α : V → ℂ) (Ae : V ≃ₗ[ℂ] V) (x : V) : ℂ :=
  α x * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x) x)
def bC (H : Sesq V) (Ae : V ≃ₗ[ℂ] V) (x x' : V) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (Ae.symm x) x' : ℂ))
def latA (Λ : AddSubgroup V) (δ Ae : V ≃ₗ[ℂ] V) : AddSubgroup V :=
  imgLat (Ae : V →ₗ[ℂ] V) (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ)
structure UnitaryData (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V) : Prop where
  herm : IsHerm H
  pos : IsPosDef H
  selfDual : IsSelfDual H Λ
  semi : IsSemiChar H Λ α
  isom : IsIsom H H (δ : V →ₗ[ℂ] V)
  semi' : IsSemiChar H (imgLat (δ : V →ₗ[ℂ] V) Λ) α
  inv : ∀ x ∈ Λ, α (δ x) = α x
  idx₁ : relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ ≠ 0
  idx₂ : relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) ≠ 0
  cay : ∀ x, Ae x = x - δ.symm x
def gaussC (H : Sesq V) (α : V → ℂ) (Ae : V ≃ₗ[ℂ] V) (S : Finset V) : ℂ :=
  ((Real.sqrt S.card : ℝ) : ℂ)⁻¹ * ∑ x ∈ S, phiC H α Ae x
def AtMostLine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Sesq V) (α : V → ℂ)
    (Λ : AddSubgroup V) : Prop :=
  ∀ θ ∈ Th H α Λ, θ ≠ 0 → ∀ F ∈ Th H α Λ, ∃ c : ℂ, F = c • θ
end Objects
def UnitaryIndex : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    latA Λ δ Ae ≤ Λ ∧
    (relIdx (latA Λ δ Ae) Λ : ℝ)
      = (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) * ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2
def PhiBasic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), UnitaryData H Λ α δ Ae →
    (∀ x y, H (cayC Ae x) y = -H x (cayC Ae y)) ∧ (∀ x, (H (cayC Ae x) x).re = 0) ∧
    (∀ x ∈ Λ, ‖phiC H α Ae x‖ = 1) ∧
    ∀ x ∈ Λ, ∀ y ∈ latA Λ δ Ae, phiC H α Ae (x + y) = phiC H α Ae x
def PhiQuadratic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), UnitaryData H Λ α δ Ae →
    (∀ x ∈ Λ, ∀ x' ∈ Λ, phiC H α Ae (x + x') = phiC H α Ae x * phiC H α Ae x' * bC H Ae x x') ∧
    (∀ x ∈ Λ, ∀ x' ∈ Λ, bC H Ae x x' = bC H Ae x' x) ∧
    (∀ x x' x'', bC H Ae (x + x') x'' = bC H Ae x x'' * bC H Ae x' x'') ∧
    (∀ x ∈ Λ, (∀ x' ∈ Λ, bC H Ae x x' = 1) ↔ x ∈ latA Λ δ Ae) ∧
    ∀ x ∈ Λ, ∀ k : ℕ, phiC H α Ae (k • x) = phiC H α Ae x ^ (k ^ 2)
structure IsQuadFn {M : Type*} [AddCommGroup M] (φ : M → ℂ) (b : M → M → ℂ) : Prop where
  add : ∀ x y, φ (x + y) = φ x * φ y * b x y
  left : ∀ x y z, b (x + y) z = b x z * b y z
  sq : ∀ (k : ℕ) (x : M), φ (k • x) = φ x ^ (k ^ 2)
  ne : ∀ x, φ x ≠ 0
  nondeg : ∀ x, (∀ y, b x y = 1) → x = 0
def GaussEighth : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (b : M → M → ℂ), IsQuadFn φ b →
    (∑ x, φ x) ^ 8 = (Fintype.card M : ℂ) ^ 4
def UnitaryGauss : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), UnitaryData H Λ α δ Ae → ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S →
    gaussC H α Ae S ^ 8 = 1
def DetCayley : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ δ Ae : V ≃ₗ[ℂ] V, IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    conj (LinearMap.det (Ae : V →ₗ[ℂ] V))
      = (-1) ^ Module.finrank ℂ V * LinearMap.det (δ : V →ₗ[ℂ] V) * LinearMap.det (Ae : V →ₗ[ℂ] V)
def UnitaryConstant : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    AtMostLine H α Λ → ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S → ∀ θ ∈ Th H α Λ,
      pullInv δ θ = ((‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
        * gaussC H α Ae S) • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ
def UnitaryEighth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    AtMostLine H α Λ → ∀ θ ∈ Th H α Λ, θ ≠ 0 → ∀ c : ℂ,
      pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ →
      c ^ 8 = LinearMap.det (δ : V →ₗ[ℂ] V) ^ 4
end Formalism.L2.Th1.H


