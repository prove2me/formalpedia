-- Prove2me | Definitions.Def_Formalism_CMTypeGalois_StatementField
-- name    : Formalism_CMTypeGalois_StatementField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:15.793798+00:00
-- url     : https://prove2.me/theorems/a07ac03a-d7fe-4d03-9948-c50a41781561
-- title:
--   Statement Field
-- statement:
--   Definitions and structural lemmas for Statement Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/StatementField.lean

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Finset
open scoped Pointwise
noncomputable section
namespace Formalism.Q3
def IsMQ {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (a : Fin k → ℤ) (α : Fin k → E) : Prop :=
  (∀ i, α i ^ 2 = (a i : E)) ∧ IntermediateField.adjoin ℚ (Set.range α) = ⊤
def IsHost (q : Fin 3 → ℕ) {E : Type*} [Field E] [Algebra ℚ E] (α : Fin 3 → E) : Prop :=
  IsMQ (fun i => -(q i : ℤ)) α
open Classical in

def galSign {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (α : Fin k → E) (σ : Gal(E/ℚ)) :
    Fin k → ℤˣ :=
  fun i => if σ (α i) = α i then 1 else -1
def IsCMTypeEmb {K : Type*} [Field K] (S : Finset (K →+* ℂ)) : Prop :=
  ∀ ψ : K →+* ℂ, ψ ∈ S ↔ ComplexEmbedding.conjugate ψ ∉ S
def MQGalois : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ i, a i ≠ 0) →
    IsGalois ℚ E ∧
    (∀ (σ : Gal(E/ℚ)) (i : Fin k), σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i) ∧
    (∀ σ τ : Gal(E/ℚ), galSign α (σ * τ) = galSign α σ * galSign α τ) ∧
    Function.Injective (galSign α)
def MQKummer : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ S : Finset (Fin k), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : ℚ))) →
    Module.finrank ℚ E = 2 ^ k ∧ Function.Bijective (galSign α) ∧
    ∀ d : ℚ, IsSquare (algebraMap ℚ E d) ↔
      ∃ S : Finset (Fin k), IsSquare (d * ∏ i ∈ S, (a i : ℚ))
def MQFrob : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ i, a i ≠ 0) →
    ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
      (σ : Gal(E/ℚ)), IsArithFrobAt ℤ σ P → ∀ i : Fin k,
      (¬ (p : ℤ) ∣ 2 * a i → ((galSign α σ i : ℤˣ) : ℤ) = jacobiSym (a i) p) ∧
      (p = 2 → a i % 4 = 1 → (galSign α σ i = 1 ↔ a i % 8 = 1))
def MQExists : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℤ),
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (α : Fin k → E), IsMQ a α
def HostGalois : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    IsGalois ℚ E ∧ Module.finrank ℚ E = 8 ∧ Function.Bijective (galSign α) ∧
    (∀ σ τ : Gal(E/ℚ), galSign α (σ * τ) = galSign α σ * galSign α τ)
def HostFrob : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    ∀ (p : ℕ) [Fact p.Prime], (∀ i, p ≠ q i) →
    ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : Gal(E/ℚ), IsArithFrobAt ℤ σ P) ∧
      ∀ σ : Gal(E/ℚ), IsArithFrobAt ℤ σ P ↔ ∀ i, ((galSign α σ i : ℤˣ) : ℤ) = chiQ (q i) p
def HostConj : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    (∀ (φ : E →+* ℂ) (σ : Gal(E/ℚ)), (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galSign α σ = cc) ∧
    IsCMField E ∧
    (∀ [IsCMField E], galSign α ((IsCMField.complexConj E).restrictScalars ℚ) = cc) ∧
    Module.finrank ℚ (maximalRealSubfield E) = 4 ∧
    (∀ x : E, x ∈ maximalRealSubfield E ↔ ∀ σ : Gal(E/ℚ), galSign α σ = cc → σ x = x) ∧
    (IntermediateField.adjoin ℚ {α 0 * α 1, α 1 * α 2}).toSubfield = maximalRealSubfield E
def HostQuad : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    (∀ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ↔
        ∃ S : Finset (Fin 3), S.Nonempty ∧ K = IntermediateField.adjoin ℚ {∏ i ∈ S, α i}) ∧
    ∀ S : Finset (Fin 3), S.Nonempty →
      (∏ i ∈ S, α i) ^ 2 = ((∏ i ∈ S, (-(q i : ℤ)) : ℤ) : E) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ {∏ i ∈ S, α i}) = 2 ∧
      (∀ σ : Gal(E/ℚ),
        (∀ x ∈ IntermediateField.adjoin ℚ {∏ i ∈ S, α i}, σ x = x) ↔ chiS S (galSign α σ) = 1) ∧
      ((∀ φ : IntermediateField.adjoin ℚ {∏ i ∈ S, α i} →+* ℂ, ComplexEmbedding.IsReal φ) ↔
        Even S.card)
def HostUnram : Prop :=
  ∀ (k : ℕ) (q : Fin k → ℕ), 2 ≤ k → (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin k → E), IsMQ (fun i => -(q i : ℤ)) α →
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
    (∀ σ : Gal(E/ℚ), galSign α σ = (fun _ => -1) → ∃ x : 𝓞 E, σ • x - x ∉ P) ∧
    ramificationIdx P (𝓞 (maximalRealSubfield E)) = 1
def HostInertia : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
  ∀ (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})] (σ : Gal(E/ℚ)),
    (∀ x : 𝓞 E, σ • x - x ∈ P) ↔ (galSign α σ = 1 ∨ galSign α σ = e3 i)
def HostDecompSub : Prop :=
  ∀ q : Fin 3 → ℕ, HostPrimes q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
  ∀ (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})],
    (∀ σ ∈ MulAction.stabilizer Gal(E/ℚ) P, galSign α σ ∈ modelDecomp q i) ∧
    (∀ σ : Gal(E/ℚ), galSign α σ = cc → σ ∉ MulAction.stabilizer Gal(E/ℚ) P)
def HostDecompEq : Prop :=
  ∀ q : Fin 3 → ℕ, HostPrimes q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
  ∀ (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})],
    ∀ g ∈ modelDecomp q i, ∃ σ ∈ MulAction.stabilizer Gal(E/ℚ) P, galSign α σ = g
def HostUnramOutside : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    ∀ (p : ℕ) [Fact p.Prime], (∀ i, p ≠ q i) →
    ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})], ramificationIdx P ℤ = 1
def HostMu : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → (∀ i, q i ≠ 3) →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    ∀ ζ : E, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ = 1 ∨ ζ = -1
open Classical in

def HostEmb : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
  ∀ φ₀ : E →+* ℂ,
    Function.Bijective (fun σ : Gal(E/ℚ) => φ₀.comp σ.toAlgHom.toRingHom) ∧
    (∀ σ τ : Gal(E/ℚ), galSign α τ = cc →
      φ₀.comp (τ * σ).toAlgHom.toRingHom =
        ComplexEmbedding.conjugate (φ₀.comp σ.toAlgHom.toRingHom)) ∧
    ∀ Φ : Finset Gal3, IsCMTypeG cc Φ ↔
      IsCMTypeEmb ((univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image
        (fun σ => φ₀.comp σ.toAlgHom.toRingHom))
end Formalism.Q3


