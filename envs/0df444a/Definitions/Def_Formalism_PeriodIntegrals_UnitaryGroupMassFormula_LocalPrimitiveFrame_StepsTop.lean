-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:53.723453+00:00
-- url     : https://prove2.me/theorems/d82d806f-7f1b-4846-b97b-7291f1152ff2
-- title:
--   Steps Top
-- statement:
--   Definitions and structural lemmas for Steps Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/StepsTop.lean

import Definitions.Def_Formalism_PeriodIntegrals_LocFramePrim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
def DiffLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (y : Fv F v ⊗[F] E),
    y ∈ Submodule.span (v.adicCompletionIntegers F)
        (inclR (F := F) (Fv F v) '' ((ddE F ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) ↔
      ∃ p ∈ OEv (E := E) v, y = sc (E := E) v ((dV v)⁻¹ ^ k) * p
def Dual : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E)) (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    ∃ (φ : Fin r → (Fin n → E) →ₗ[E] E) (φz : (Fin n → E) →ₗ[E] E),
      (∀ a b, φ a (e b) = if a = b then 1 else 0) ∧ (∀ a b, φ a (f b) = 0) ∧
      (∀ a, ∀ l ∈ Lb, φ a l = 0) ∧ (∀ a, φz (e a) = 0) ∧ (∀ a, φz (f a) = 0) ∧
      φz z = 1 ∧ ∀ l ∈ Lb, ∃ o : 𝓞 E, φz l = o
def Assemble : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    (∀ (k : ℕ) (y : Fv F v ⊗[F] E),
      y ∈ Submodule.span (v.adicCompletionIntegers F)
        (inclR (F := F) (Fv F v) '' ((ddE F ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) ↔
      ∃ p ∈ OEv (E := E) v, y = sc (E := E) v ((dV v)⁻¹ ^ k) * p) →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    z ∈ Lb →
    ∀ (φ : Fin r → (Fin n → E) →ₗ[E] E) (φz : (Fin n → E) →ₗ[E] E),
      (∀ a b, φ a (e b) = if a = b then 1 else 0) → (∀ a b, φ a (f b) = 0) →
      (∀ a, ∀ l ∈ Lb, φ a l = 0) → (∀ a, φz (e a) = 0) → (∀ a, φz (f a) = 0) →
      φz z = 1 → (∀ l ∈ Lb, ∃ o : 𝓞 E, φz l = o) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))
end PI.LocFramePrimWork


