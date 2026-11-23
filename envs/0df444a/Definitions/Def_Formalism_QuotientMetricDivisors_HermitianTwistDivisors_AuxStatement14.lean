-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:51.016797+00:00
-- url     : https://prove2.me/theorems/1d0123ad-97ef-4758-bec4-f44095ff1b48
-- title:
--   Aux Statement14
-- statement:
--   Definitions and structural lemmas for Aux Statement14, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_apply
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_hform_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace exponent_index_lattice
section Abs
variable {R K V W : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
end Abs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm
theorem orth_eq {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    H * E = Prᴴ * (Eᴴ * H * E) := by
  have h2 : Eᴴ * H = Eᴴ * H * (E * Pr) := by
    have h := hO.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  have h3 := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH] at h3
  rw [h3]
  simp only [Matrix.mul_assoc]
theorem adj {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr)
    (x : Fin n → K) (z : Fin d → K) :
    hform (Eᴴ * H * E) (Matrix.mulVecLin Pr x) z = hform H x (Matrix.mulVecLin E z) := by
  have key : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (u v : Fin m → K),
      hform M u v = star u ⬝ᵥ (M *ᵥ v) := by
    intro m M u v
    simp only [hform_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [key, key, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← orth_eq hH hO]
end exponent_index_lattice
open exponent_index_lattice RationalHermitianForm
namespace exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def sm (D : ℕ) (a : K) : (Fin D → K) →ₗ[K] (Fin D → K) := a • LinearMap.id
def smLat {D : ℕ} (a : K) (A : Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  A.map ((sm D a).restrictScalars (𝓞 K))
end exponent_index_lattice
namespace exponent_index_lattice
section Abs2
variable {K V W : Type} [Field K] [StarRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
end Abs2
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end exponent_index_lattice
namespace exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
section Inv
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {Γ : Type} [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V)
def invSub : Submodule K V where
  carrier := {v | ∀ γ, ρ γ v = v}
  add_mem' := fun {a b} ha hb γ => by rw [map_add, ha γ, hb γ]
  zero_mem' := fun γ => map_zero _
  smul_mem' := fun c v hv γ => by rw [map_smul, hv γ]
theorem tr_inv (v : V) (γ : Γ) : ρ γ (∑ δ, ρ δ v) = ∑ δ, ρ δ v := by
  rw [map_sum]
  have h : ∀ δ, ρ γ (ρ δ v) = ρ (γ * δ) v := fun δ => by rw [map_mul]; rfl
  simp_rw [h]
  exact Fintype.sum_bijective (γ * ·) (Group.mulLeft_bijective γ) _ _ (fun _ => rfl)
theorem avg_mem (v : V) :
    (((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ : V →ₗ[K] V) v ∈ invSub ρ := by
  intro γ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, tr_inv]
def avg : V →ₗ[K] invSub ρ :=
  LinearMap.codRestrict (invSub ρ) (((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ) (avg_mem ρ)
end Inv
end exponent_index_lattice
namespace exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end exponent_index_lattice
end Formalism.DivisionValues


