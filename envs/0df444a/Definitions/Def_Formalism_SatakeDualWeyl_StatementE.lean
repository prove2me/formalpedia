-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementE
-- name    : Formalism_SatakeDualWeyl_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:16:47.929079+00:00
-- url     : https://prove2.me/theorems/47920630-6e27-413a-af92-3ae25a75c144
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementE.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.UG
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
abbrev Ov : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring
def qV : ℕ := Ideal.absNorm v.asIdeal
def IsUnifV (ϖ : v.adicCompletion F) : Prop :=
  Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
def ordV (x : v.adicCompletion F) : ℤ :=
  if h : Valued.v x = 0 then 0 else -Multiplicative.toAdd (WithZero.unzero h)
def diagPow {n : ℕ} (ϖ : v.adicCompletion F) (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  Matrix.diagonal (fun i => ϖ ^ (a i))
def IsUpperB {n : ℕ} (b : GL (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = 0
def chiDelta {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F)) : ℂ :=
  ∏ i : Fin n, α i ^ (ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i)) *
    ((qV F v : ℂ) ^ (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) *
      (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)))
def IsSpherical {n : ℕ} (α : Fin n → ℂ) (φ : GL (Fin n) (v.adicCompletion F) → ℂ) : Prop :=
  ∀ b g k : GL (Fin n) (v.adicCompletion F), IsUpperB F v b → k ∈ GLint (Fin n) (Ov F v) →
    φ (b * g * k) = chiDelta F v α b * φ g
def CartanDecomp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ →
    ∀ g : GL (Fin n) (v.adicCompletion F), ∃ a : Fin n → ℤ, Antitone a ∧
      ∃ k₁ ∈ GLint (Fin n) (Ov F v), ∃ k₂ ∈ GLint (Fin n) (Ov F v),
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) _) * diagPow F v ϖ a * (k₂ : Matrix (Fin n) (Fin n) _)
def CartanUnique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ a a' : Fin n → ℤ, Antitone a → Antitone a' →
    ∀ k₁ ∈ GLint (Fin n) (Ov F v), ∀ k₂ ∈ GLint (Fin n) (Ov F v),
      (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * diagPow F v ϖ a * (k₂ : Matrix (Fin n) (Fin n) _) =
        diagPow F v ϖ a' → a = a'
def HeckeCommGL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (k : Type) [CommRing k],
    ∀ f₁ ∈ Hecke k (GLint (Fin n) (Ov F v)), ∀ f₂ ∈ Hecke k (GLint (Fin n) (Ov F v)),
      conv (GLint (Fin n) (Ov F v)) f₁ f₂ = conv (GLint (Fin n) (Ov F v)) f₂ f₁
def SphericalExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂ),
    (∀ i, α i ≠ 0) → ∃ φ : GL (Fin n) (v.adicCompletion F) → ℂ, IsSpherical F v α φ ∧ φ 1 = 1 ∧
      ∀ ψ, IsSpherical F v α ψ → ψ = fun g => ψ 1 * φ g
def SatakeTj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ (α : Fin n → ℂ), (∀ i, α i ≠ 0) →
    ∀ φ : GL (Fin n) (v.adicCompletion F) → ℂ, IsSpherical F v α φ → ∀ j : ℕ, j ≤ n →
      hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ =
        ((qV F v : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * Multiset.esymm (Multiset.map α Finset.univ.val) j) • φ
def TjCosets : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ j : ℕ, j ≤ n →
      (Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
          Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} : ℤ) * ∏ i ∈ Finset.range j, ((qV F v : ℤ) ^ (i + 1) - 1) =
        ∏ i ∈ Finset.range j, ((qV F v : ℤ) ^ (n - i) - 1)
end Formalism.UG


