-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AutomorphicForms_Newform
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_AutomorphicForms_Newform
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:34:10.138953+00:00
-- url     : https://prove2.me/theorems/1ee42f9a-a44d-49f1-993d-fa8274e5e857
-- title:
--   Newform
-- statement:
--   Definitions and structural lemmas for Newform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/Newform.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
namespace UpperTheory.V.Af
def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n
def HasChar (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → f ∣[(k : ℤ)] γ = χ ((γ 1 1 : ℤ) : ZMod M) • f
def IsEigAt (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (p : ℕ) (lam : ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    coef f (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0) = lam * coef f n
structure Newform (k : ℕ) where

  M : ℕ
  pos : 0 < M

  f : CuspForm (Gamma1 M) (k : ℤ)

  χ : DirichletCharacter ℂ M
  char : HasChar k χ f
  one : coef f 1 = 1
  eig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → IsEigAt k χ f p (coef f p)
  new : ∀ M' : ℕ, M' ∣ M → M' ≠ M → ∀ (g : CuspForm (Gamma1 M') (k : ℤ)) (χ' : DirichletCharacter ℂ M'),
    HasChar k χ' g → (∀ᶠ p : ℕ in Filter.cofinite, p.Prime → IsEigAt k χ' g p (coef f p)) → g = 0
namespace Newform
variable {k : ℕ} (g : Newform k)
def a (n : ℕ) : ℂ := coef g.f n
def heckePoly (p : ℕ) : ℂ[X] := X ^ 2 - C (g.a p) * X + C (g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1))
def Att {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  IsSSRep V ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (∀ s ∈ Ine (F := ℚ) A, V s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
      (V σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom = g.heckePoly (normV w)
end Newform
end UpperTheory.V.Af


