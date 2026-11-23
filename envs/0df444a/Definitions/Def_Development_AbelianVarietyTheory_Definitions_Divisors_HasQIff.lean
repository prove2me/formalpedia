-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:25.336339+00:00
-- url     : https://prove2.me/theorems/74a0c6de-656e-4a41-a4f8-a56f1559146c
-- title:
--   Has QIff
-- statement:
--   Definitions and structural lemmas for Has QIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasQIff.lean

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
open scoped UpperHalfPlane MatrixGroups ModularForm
namespace GlobalTheory.QFam
def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)
def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)
def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)
def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ
def FamQ {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (N : ℕ) (f : ι → ℍ → ℂ) (a : ι → ℕ → ℂ) : Prop :=
  IsFam act w f ∧ ∀ i, HasQ N (f i) (a i)
def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2
def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0
def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)
def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)
def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩
end GlobalTheory.QFam


