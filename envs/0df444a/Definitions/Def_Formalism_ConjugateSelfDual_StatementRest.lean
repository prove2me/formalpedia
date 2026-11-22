-- Prove2me | Definitions.Def_Formalism_ConjugateSelfDual_StatementRest
-- name    : Formalism_ConjugateSelfDual_StatementRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:02:38.858983+00:00
-- url     : https://prove2.me/theorems/03bd1925-f26f-4c5b-b37c-9df24f191f5d
-- title:
--   Statement Rest
-- statement:
--   Definitions and structural lemmas for Statement Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ConjugateSelfDual/StatementRest.lean

import Mathlib
import Definitions.Def_Formalism_ConjugateSelfDual_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
section places
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end places
section galois
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
def UnramAt {R : Type*} [CommRing R] (ρ : G F Ω →* GL (Fin n) R) (v : HeightOneSpectrum (𝓞 F)) :
    Prop :=
  ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia A, ρ σ = 1
def AlmostUnram {R : Type*} [CommRing R] (ρ : G F Ω →* GL (Fin n) R) : Prop :=
  {v : HeightOneSpectrum (𝓞 F) | ¬ UnramAt ρ v}.Finite
def Irred (ρ : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  0 < n ∧ ∀ W : Submodule (Qbar l) (Fin n → Qbar l),
    (∀ σ, ∀ w ∈ W, Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) (Qbar l)) w ∈ W) → W = ⊥ ∨ W = ⊤
def FrobMatch (ρ : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l →+* ℂ)
    (P : HeightOneSpectrum (𝓞 F) → ℂ[X]) : Prop :=
  ∀ᶠ v in cofinite, ∀ A σ, IsPlaceOver A v → IsFrob A (normV v) σ →
    (ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι = P v
end galois
section polar
def conjGal {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (s : K ≃+* K) (τ : Ω ≃+* Ω)
    (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)) (σ : G K Ω) : G K Ω :=
  AlgEquiv.ofRingEquiv (f := (τ.symm.trans σ.toRingEquiv).trans τ) (by
    intro x
    have h1 : τ.symm (algebraMap K (Ω) x) =
        algebraMap K (Ω) (s.symm x) := by
      rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.trans_apply, h1, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
variable {n l : ℕ} [Fact l.Prime]
def IsConjSelfDualSym {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (ρ : G K Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω)
      (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)), (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) (Qbar l), J.det ≠ 0 ∧ J.transpose = J ∧
    ∃ μ : G K Ω → Qbar l, ∀ σ : G K Ω,
      (ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).transpose * J * (ρ (conjGal s τ hτ σ) : Matrix _ _ _) = μ σ • J
def IsComplexConj {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (c : G ℚ Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)
def IsOddSymplectic {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (ρ : G ℚ Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ J : Matrix (Fin n) (Fin n) (Qbar l), J.det ≠ 0 ∧ J.transpose = -J ∧
    ∃ ν : G ℚ Ω → Qbar l,
      (∀ σ, (ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).transpose * J * (ρ σ : Matrix _ _ _) = ν σ • J) ∧
      ∀ c, IsComplexConj c → ν c = -1
def IsOdd {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ c, IsComplexConj c → (ρ c : Matrix (Fin 2) (Fin 2) (Qbar l)).det = -1
end polar
structure CuspSpectrum (F : Type*) [Field F] [NumberField F] (n : ℕ) where
  Rep : Type
  wt : Rep → (F →+* ℂ) → Fin n → ℤ
  level : Rep → ℕ → Prop
  hecke : Rep → HeightOneSpectrum (𝓞 F) → ℂ[X]
  level_exists : ∀ π, ∃ M : ℕ, 0 < M ∧ level π M
  level_dvd : ∀ π (M M' : ℕ), level π M → M ∣ M' → 0 < M' → level π M'
  hecke_monic : ∀ π (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), level π M →
    ((M : ℕ) : 𝓞 F) ∉ v.asIdeal → (hecke π v).Monic ∧ (hecke π v).natDegree = n
  mult_one : ∀ π π', (∀ᶠ v in cofinite, hecke π v = hecke π' v) → π = π'
  finite : ∀ (M : ℕ) (w : (F →+* ℂ) → Fin n → ℤ), {π | level π M ∧ wt π = w}.Finite
abbrev SpectrumFamily := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), CuspSpectrum F n
def CuspSpectrum.empty (F : Type*) [Field F] [NumberField F] (n : ℕ) : CuspSpectrum F n where
  Rep := Empty
  wt π := π.elim
  level π := π.elim
  hecke π := π.elim
  level_exists π := π.elim
  level_dvd π := π.elim
  hecke_monic π := π.elim
  mult_one π := π.elim
  finite _ _ := Set.toFinite _
def IsNormEigenform {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (χ : DirichletCharacter ℂ N) : Prop :=
  (∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) =
      χ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) • ⇑f) ∧
  (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1 ∧
  (∀ a b : ℕ, Nat.Coprime a b → (UpperHalfPlane.qExpansion 1 f).coeff (a * b) =
      (UpperHalfPlane.qExpansion 1 f).coeff a * (UpperHalfPlane.qExpansion 1 f).coeff b) ∧
  (∀ p r : ℕ, p.Prime → ¬ p ∣ N → (UpperHalfPlane.qExpansion 1 f).coeff (p ^ (r + 2)) =
      (UpperHalfPlane.qExpansion 1 f).coeff p * (UpperHalfPlane.qExpansion 1 f).coeff (p ^ (r + 1)) -
        χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (UpperHalfPlane.qExpansion 1 f).coeff (p ^ r)) ∧
  (∀ p r : ℕ, p.Prime → p ∣ N → (UpperHalfPlane.qExpansion 1 f).coeff (p ^ r) =
      (UpperHalfPlane.qExpansion 1 f).coeff p ^ r)
end Formalism.ConjugateSelfDual


