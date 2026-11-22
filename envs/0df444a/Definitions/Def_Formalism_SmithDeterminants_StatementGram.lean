-- Prove2me | Definitions.Def_Formalism_SmithDeterminants_StatementGram
-- name    : Formalism_SmithDeterminants_StatementGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:36.833095+00:00
-- url     : https://prove2.me/theorems/bfa2304c-564c-4ae2-902f-7e4375f852b4
-- title:
--   Statement Gram
-- statement:
--   Definitions and structural lemmas for Statement Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SmithDeterminants/StatementGram.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
namespace Formalism.A
def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial
def fockZ {σ : Type*} (f g : MvPolynomial σ ℤ) : ℤ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (mfact m : ℤ)
def gramZ {σ ι : Type*} (f : ι → MvPolynomial σ ℤ) : Matrix ι ι ℤ :=
  fun a b => fockZ (f a) (f b)
def l1Z {σ : Type*} (f : MvPolynomial σ ℤ) : ℤ := ∑ m ∈ f.support, |f.coeff m|
def famZ {σ ι : Type*} (E : ι → MvPolynomial σ ℤ) (α : ι → (σ →₀ ℕ)) (a : ι) :
    MvPolynomial σ ℤ :=
  E a * MvPolynomial.monomial (α a) 1
def fockG {σ : Type*} (f g : MvPolynomial σ GaussianInt) : GaussianInt :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (mfact m : GaussianInt)
def gramG {σ ι : Type*} (f : ι → MvPolynomial σ GaussianInt) : Matrix ι ι GaussianInt :=
  fun a b => fockG (f a) (f b)
def l1G {σ : Type*} (f : MvPolynomial σ GaussianInt) : ℝ :=
  ∑ m ∈ f.support, ‖GaussianInt.toComplex (f.coeff m)‖
def famG {σ ι : Type*} (E : ι → MvPolynomial σ GaussianInt) (α : ι → (σ →₀ ℕ)) (a : ι) :
    MvPolynomial σ GaussianInt :=
  E a * MvPolynomial.monomial (α a) 1
def GramZ : Prop :=
  ∀ (k s : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (E : ι → MvPolynomial (Fin k) ℤ) (e : ι → ℕ) (α : ι → (Fin k →₀ ℕ)),
    (∀ a, (E a).IsHomogeneous (e a)) →
    (∀ a, Finsupp.degree (α a) + e a = s) →
    (∀ a, l1Z (E a) ≤ (k : ℤ) ^ (e a)) →
    LinearIndependent ℤ (famZ E α) →
    (∀ a b, (mfact (α a) : ℤ) ∣ gramZ (famZ E α) a b) ∧
    ((gramZ (famZ E α)).map (Int.cast : ℤ → ℝ)).PosDef ∧
    0 < (gramZ (famZ E α)).det ∧
    (gramZ (famZ E α)).det ≤ ∏ a, gramZ (famZ E α) a a ∧
    (∀ a, gramZ (famZ E α) a a ≤ (mfact (α a) : ℤ) * ((k : ℤ) ^ 2 * s) ^ (e a)) ∧
    (∏ a, (mfact (α a) : ℤ)) ∣ (gramZ (famZ E α)).det ∧
    0 < (gramZ (famZ E α)).det / ∏ a, (mfact (α a) : ℤ) ∧
    (gramZ (famZ E α)).det / ∏ a, (mfact (α a) : ℤ) ≤ ∏ a, ((k : ℤ) ^ 2 * s) ^ (e a) ∧
    (∀ p : ℕ, p.Prime →
      (padicValInt p (gramZ (famZ E α)).det : ℝ) ≤
        ∑ a, ((padicValNat p (mfact (α a)) : ℝ) +
          (e a : ℝ) * Real.log ((k : ℝ) ^ 2 * s) / Real.log p)) ∧
    (∀ a, mfact (α a) ∣ s.factorial)
def GramGauss : Prop :=
  ∀ (k s : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (E : ι → MvPolynomial (Fin k) GaussianInt) (e : ι → ℕ) (α : ι → (Fin k →₀ ℕ)),
    (∀ a, (E a).IsHomogeneous (e a)) →
    (∀ a, Finsupp.degree (α a) + e a = s) →
    (∀ a, l1G (E a) ≤ (k : ℝ) ^ (e a)) →
    LinearIndependent GaussianInt (famG E α) →
    (∀ a b, (mfact (α a) : GaussianInt) ∣ gramG (famG E α) a b) ∧
    ((gramG (famG E α)).map GaussianInt.toComplex).PosDef ∧
    (∀ a, (gramG (famG E α) a a).im = 0 ∧
      (gramG (famG E α) a a).re ≤ (mfact (α a) : ℤ) * ((k : ℤ) ^ 2 * s) ^ (e a)) ∧
    ∃ N : ℤ, (gramG (famG E α)).det = (N : GaussianInt) ∧ 0 < N ∧
      N ≤ ∏ a, (gramG (famG E α) a a).re ∧
      (∏ a, (mfact (α a) : ℤ)) ∣ N ∧
      0 < N / ∏ a, (mfact (α a) : ℤ) ∧
      N / ∏ a, (mfact (α a) : ℤ) ≤ ∏ a, ((k : ℤ) ^ 2 * s) ^ (e a) ∧
      (∀ p : ℕ, p.Prime →
        (padicValInt p N : ℝ) ≤
          ∑ a, ((padicValNat p (mfact (α a)) : ℝ) +
            (e a : ℝ) * Real.log ((k : ℝ) ^ 2 * s) / Real.log p))
end Formalism.A


