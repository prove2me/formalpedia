-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IdeleGenerators_ConstSmall
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_IdeleGenerators_ConstSmall
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:18.501261+00:00
-- url     : https://prove2.me/theorems/8543f7dd-095f-577a-a73e-d18654146a6c
-- title:
--   Const Small
-- statement:
--   Definitions and structural lemmas for Const Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IdeleGenerators/ConstSmall.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AutomorphicForms_Newform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.ConjugateSelfDual Polynomial CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm
namespace UpperTheory.V.Sd
def numL : ℕ → ℤ[X]
  | 0 => 0
  | 1 => X
  | (k + 2) => X * (derivative (numL (k + 1)) * (1 - X) + C ((k : ℤ) + 1) * numL (k + 1))
def Lk {K : Type} [Field K] (k : ℕ) (x : K) : K := aeval x (numL k) / (1 - x) ^ k
def lipC (k : ℕ) : ℂ := (-2 * Real.pi * Complex.I) ^ k / ((k - 1).factorial : ℂ)
def eisFun (N k : ℕ) (a : ZMod N) (z : ℍ) : ℂ :=
  (N : ℂ) ^ k / lipC k * ∑' v : {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a},
    ((v.1.1 : ℂ) * (z : ℂ) + (v.1.2 : ℂ)) ^ (-(k : ℤ))
def sigChi (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  ∑ j ∈ n.divisors, χ (j : ZMod N) * (j : ℂ) ^ (k - 1)
def VanOff (N k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), ¬ (N : ℤ) ∣ γ 1 0 → IsZeroAtImInfty (f ∣[(k : ℤ)] γ)
def IntQ {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (f : ℍ → ℂ) : Prop := ∀ n, ‖ι.symm (coef f n)‖ ≤ 1
structure Eigenform (k N : ℕ) (χ : DirichletCharacter ℂ N) where

  f : CuspForm (Gamma1 N) (k : ℤ)
  char : HasChar k χ f
  one : coef f 1 = 1
  eig : ∀ p : ℕ, p.Prime → IsEigAt k χ f p (coef f p)
def Eigenform.a {k N : ℕ} {χ : DirichletCharacter ℂ N} (g : Eigenform k N χ) (n : ℕ) : ℂ := coef g.f n
def LkDist : Prop :=
  ∀ (w k : ℕ), 1 ≤ w → 1 ≤ k → ∀ ζ x : ℂ, IsPrimitiveRoot ζ w → x ^ w ≠ 1 →
    ∑ j ∈ Finset.range w, Lk k (x * ζ ^ j) = (w : ℂ) ^ k * Lk k (x ^ w)
def Lipschitz : Prop :=
  ∀ k : ℕ, 2 ≤ k → (∀ x : ℂ, ‖x‖ < 1 → HasSum (fun e : ℕ => (e : ℂ) ^ (k - 1) * x ^ e) (Lk k x)) ∧
    ∀ t : ℂ, 0 ≤ t.im → (∀ j : ℤ, t ≠ j) →
      HasSum (fun j : ℤ => (t + j) ^ (-(k : ℤ))) (lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * t)))
def EisSlash : Prop :=
  ∀ (N k : ℕ) [NeZero N], 3 ≤ k → ∀ (a : ZMod N) (γ : SL(2, ℤ)), γ ∈ Gamma0 N →
    eisFun N k a ∣[(k : ℤ)] γ = eisFun N k (a * ((γ 1 1 : ℤ) : ZMod N))
def EisMF : Prop :=
  ∀ (N k : ℕ) [NeZero N], 3 ≤ k → ∀ a : ZMod N, ∃ f : ModularForm (Gamma1 N) (k : ℤ), (f : ℍ → ℂ) = eisFun N k a
def EisVan : Prop := ∀ (N k : ℕ) [NeZero N], 3 ≤ k → ∀ a : ZMod N, IsUnit a → 1 < N → VanOff N k (eisFun N k a)
def EisCoef : Prop :=
  ∀ (N k : ℕ) [NeZero N], 3 ≤ k → ∀ a : ZMod N, a ≠ 0 →
    coef (eisFun N k a) 0 = Lk k (ZMod.stdAddChar a : ℂ) ∧
    ∀ n : ℕ, 1 ≤ n → coef (eisFun N k a) n = ∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) *
      ((ZMod.stdAddChar (a * (e : ZMod N)) : ℂ) + (-1) ^ k * (ZMod.stdAddChar (-(a * (e : ZMod N))) : ℂ))
def LkSep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ N : ℕ, 0 < N → ¬ l ∣ N →
    (∀ (k : ℕ) (x : Qbar l), x ^ N = 1 → x ≠ 1 → ‖Lk k x‖ ≤ 1) ∧
    (∀ x : Qbar l, x ^ N = 1 → x ^ 2 ≠ 1 → ‖Lk 3 x‖ = 1) ∧
    ∀ x y : Qbar l, x ^ N = 1 → y ^ N = 1 → x ^ 2 ≠ 1 → y ^ 2 ≠ 1 → y ≠ x → y ≠ x⁻¹ →
      ‖Lk 4 x - Lk 4 y‖ = 1 ∨ ‖Lk 3 x ^ 2 - Lk 3 y ^ 2‖ = 1 ∨ ‖Lk 3 x * Lk 5 x - Lk 3 y * Lk 5 y‖ = 1
def LevelOne : Prop :=
  ∀ (N k : ℕ) [NeZero N], Even k → k ≠ 2 → ∃ f : ModularForm (Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), (f : ℍ → ℂ) ∣[(k : ℤ)] γ = f) ∧ coef f 0 = 1 ∧ ∀ n, ∃ c : ℤ, coef f n = c
def IsFam {N : ℕ} (k : ℕ) (f : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ)) : Prop :=
  ∀ (a b : (ZMod N)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → (b : ZMod N) = a * ((γ 1 1 : ℤ) : ZMod N) →
    (f a : ℍ → ℂ) ∣[(k : ℤ)] γ = f b
def UnitFam : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N], 3 ≤ N → ¬ l ∣ N → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∃ f : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ), IsFam k f ∧ (∀ a, IntQ ι (f a)) ∧ (∀ a, VanOff N k (f a)) ∧
      ‖ι.symm (coef (f 1) 0)‖ = 1 ∧ ∀ a, a ≠ 1 → a ≠ -1 → coef (f a) 0 = 0
def UnitForm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N], 3 ≤ N → ¬ l ∣ N → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∀ χ : DirichletCharacter ℂ N, χ (-1) = (-1) ^ k →
      ∃ f : ModularForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ IntQ ι f ∧ VanOff N k f ∧ coef f 0 = 1
def EisChi : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 < N → 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → χ (-1) = (-1) ^ k →
    ∃ f : ModularForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ VanOff N k f ∧ (∀ n, 1 ≤ n → coef f n = sigChi k χ n) ∧
      2 * gaussSum χ⁻¹ ZMod.stdAddChar * coef f 0 = ∑ a : ZMod N, χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ)
structure EDat (l M w : ℕ) (φ : DirichletCharacter ℂ M) (θ : DirichletCharacter ℂ w) (χ : DirichletCharacter ℂ (M * w)) : Prop where
  odd : l ≠ 2
  one_lt : 1 < M
  cop : ¬ l ∣ M
  prim : φ.IsPrimitive
  prime : w.Prime
  dvd : l ∣ w - 1
  wM : ¬ w ∣ M
  φw : φ (w : ZMod M) = 1
  θne : θ ≠ 1
  θpow : θ ^ l = 1
  mul : ∀ n : ℕ, χ (n : ZMod (M * w)) = φ (n : ZMod M) * θ (n : ZMod w)
def EPrim : Prop := ∀ (l M w : ℕ) φ θ χ, EDat l M w φ θ χ → χ.IsPrimitive
def ConstSmall : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M w : ℕ) [NeZero (M * w)] φ θ χ, EDat l M w φ θ χ → ∀ k : ℕ, 1 ≤ k → ∀ c : ℂ,
    2 * gaussSum χ⁻¹ ZMod.stdAddChar * c = ∑ a : ZMod (M * w), χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ) → ‖ι.symm c‖ < 1
def CuspOf : Prop :=
  ∀ (N k : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : ModularForm (Gamma1 N) (k : ℤ)), HasChar k χ f → VanOff N k f →
    coef f 0 = 0 → ∃ g : CuspForm (Gamma1 N) (k : ℤ), (g : ℍ → ℂ) = f
def HeckeEx : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f →
    ∀ p : ℕ, p.Prime → ∃ g : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ g ∧ ∀ n : ℕ, 1 ≤ n →
      coef g n = coef f (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)
def FinDim : Prop :=
  ∀ (N k : ℕ) [NeZero N], FiniteDimensional ℂ (CuspForm (Gamma1 N) (k : ℤ)) ∧
    ∀ f : CuspForm (Gamma1 N) (k : ℤ), (∀ n, 1 ≤ n → coef f n = 0) → f = 0
def DelSerre : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (I J : Type) (V : Submodule (Qbar l) (I → Qbar l)), FiniteDimensional (Qbar l) V →
    ∀ T : J → Module.End (Qbar l) V, (∀ i j, T i * T j = T j * T i) →
    (∀ j (v : V), (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T j v).1 n‖ ≤ 1) → (∀ j (v : V), (∀ n, ‖v.1 n‖ < 1) → ∀ n, ‖(T j v).1 n‖ < 1) →
    ∀ (f : V) (a : J → Qbar l), (∀ n, ‖f.1 n‖ ≤ 1) → (∃ n, ‖f.1 n‖ = 1) → (∀ j, ‖a j‖ ≤ 1) →
    (∀ j n, ‖(T j f).1 n - a j * f.1 n‖ < 1) →
    ∃ (h : V) (b : J → Qbar l), h ≠ 0 ∧ (∀ n, ‖h.1 n‖ ≤ 1) ∧ (∀ j, T j h = b j • h) ∧ ∀ j, ‖b j - a j‖ < 1
def EigLift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f → IntQ ι f → ‖ι.symm (coef f 1)‖ = 1 → ∀ a : ℕ → ℂ,
    (∀ p : ℕ, p.Prime → ‖ι.symm (a p)‖ ≤ 1 ∧ ∀ n : ℕ, 1 ≤ n →
      ‖ι.symm (coef f (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0) - a p * coef f n)‖ < 1) →
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - a p)‖ < 1
def PropE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M w : ℕ) φ θ χ, EDat l M w φ θ χ → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ (-1) = (-1) ^ k →
    ∃ g : Eigenform k (M * w) χ, ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)))‖ < 1
end UpperTheory.V.Sd


