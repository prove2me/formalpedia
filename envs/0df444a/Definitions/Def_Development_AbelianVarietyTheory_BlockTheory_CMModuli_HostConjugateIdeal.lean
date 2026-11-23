-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:07.920396+00:00
-- url     : https://prove2.me/theorems/d0deb892-19ac-42b8-ba33-1956851a341d
-- title:
--   Host Conjugate Ideal
-- statement:
--   Definitions and structural lemmas for Host Conjugate Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
abbrev conjO (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a
structure Host where

  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7

  s : E
  s_sq : s ^ 2 = -(d : E)
  unramified : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ →
    P.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1

  s₀ : ℂ
  s₀_sq : s₀ ^ 2 = -(d : ℂ)
variable {E}
namespace Host
variable (H : Host E)
abbrev K : IntermediateField ℚ E := IntermediateField.adjoin ℚ {H.s}
def Psi : Set (E →+* ℂ) := {τ | τ H.s = H.s₀}
def f (_H : Host E) : ℕ := Module.finrank ℚ (maximalRealSubfield E)
theorem isCMField_complexConj_s_eq_neg : IsCMField.complexConj E H.s = -H.s := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h : (φ H.s) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.s_sq, map_neg, map_natCast]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hre : (φ H.s).re = 0 := by
    by_contra hne
    have him : (φ H.s).im = 0 := by
      have : (φ H.s).re * (φ H.s).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hne
    rw [him] at h1
    nlinarith [mul_self_nonneg (φ H.s).re]
  apply Complex.ext <;> simp [hre]
theorem isIntegral_half : IsIntegral ℤ ((1 + H.s) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hk' : (H.d : E) + 1 = 4 * k := by exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), ?_, ?_⟩
  · monicity!
  · have hs := H.s_sq
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, eq_intCast, Int.cast_natCast,
      Polynomial.eval₂_natCast]
    linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * hk'
def w₀ : 𝓞 E := ⟨(1 + H.s) / 2, H.isIntegral_half⟩
theorem conj_mem_K {x : E} (hx : x ∈ H.K) : IsCMField.complexConj E x ∈ H.K := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, H.isCMField_complexConj_s_eq_neg]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ H.s)
  | algebraMap q => rw [eq_ratCast, map_ratCast]; exact SubfieldClass.ratCast_mem _ q
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
def conjK : H.K →+* H.K :=
  RingHom.codRestrict (((IsCMField.complexConj E : E →+* E)).comp (algebraMap H.K E)) H.K
    (fun x => H.conj_mem_K x.2)
def conjIdeal (I : Ideal (𝓞 H.K)) : Ideal (𝓞 H.K) :=
  I.map (RingOfIntegers.mapRingHom H.conjK)
def SplitInK (p : ℕ) : Prop :=
  ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.K)).ncard = 2
end Host
section Lattice
variable (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
def actR (a : 𝓞 E) : (ℝ ⊗[ℤ] La) →ₗ[ℝ] (ℝ ⊗[ℤ] La) :=
  (DistribSMul.toLinearMap ℤ La a).baseChange ℝ
variable {La}
def eigenPart (J : (ℝ ⊗[ℤ] La) →ₗ[ℝ] (ℝ ⊗[ℤ] La)) (τ : E →+* ℂ) : Submodule ℝ (ℝ ⊗[ℤ] La) :=
  ⨅ a : 𝓞 E, LinearMap.eqLocus (actR La a)
    ((τ (a : E)).re • LinearMap.id + (τ (a : E)).im • J)
def domain (H : Host E) (EF : LinearMap.BilinForm ℤ La) (p q : ℕ) :
    Set ((ℝ ⊗[ℤ] La) →ₗ[ℝ] (ℝ ⊗[ℤ] La)) :=
  {J | (∀ a : 𝓞 E, J ∘ₗ actR La a = actR La a ∘ₗ J) ∧
    J ∘ₗ J = -LinearMap.id ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ τ ∈ H.Psi, Module.finrank ℝ (eigenPart J τ) = 2 * p ∧
      Module.finrank ℝ (eigenPart J ((starRingEnd ℂ).comp τ)) = 2 * q}
end Lattice
structure Datum (H : Host E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
    [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] where

  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimodular : Function.Bijective (EF : La →ₗ[ℤ] Module.Dual ℤ La)
  adjoint : ∀ (a : 𝓞 E) (x y : La), EF (a • x) y = EF x (conjO E a • y)

  p : ℕ

  q : ℕ
  p_add_q : p + q = Module.finrank (𝓞 E) La
  domain_nonempty : (domain H EF p q).Nonempty
namespace Datum
variable {H : Host E} {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
  [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (X : Datum H La)
def r (_X : Datum H La) : ℕ := Module.finrank (𝓞 E) La
def DD : Set ((ℝ ⊗[ℤ] La) →ₗ[ℝ] (ℝ ⊗[ℤ] La)) := domain H X.EF X.p X.q
def g : ℕ := H.f * X.r
def D : ℕ := H.f * X.p * X.q
def RankPos : Prop := 1 ≤ X.r
end Datum
structure Level (H : Host E) where

  M : ℕ
  three_le : 3 ≤ M
  odd : Odd M
  split : ∀ p : ℕ, p.Prime → p ∣ M → H.SplitInK p

  MM : Ideal (𝓞 H.K)
  mul_conj : MM * H.conjIdeal MM = Ideal.span {(M : 𝓞 H.K)}
  coprime : MM ⊔ H.conjIdeal MM = ⊤

  A : ℕ
  one_le : 1 ≤ A
namespace Level
variable {H : Host E}
def MMbar (L : Level H) : Ideal (𝓞 H.K) := H.conjIdeal L.MM
def MMbarO (L : Level H) : Ideal (𝓞 E) := L.MMbar.map (algebraMap (𝓞 H.K) (𝓞 E))
def M' (L : Level H) : ℕ := Nat.lcm L.M L.A
def M₀ (L : Level H) (p : ℕ) : ℕ := L.M / p ^ L.M.factorization p
def GoodAt (L : Level H) (p : ℕ) : Prop := p.Prime ∧ 3 ≤ L.M₀ p
def Dvd (L L₂ : Level H) : Prop := L.M ∣ L₂.M ∧ L.A ∣ L₂.A ∧ L.MM ∣ L₂.MM
end Level
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal


