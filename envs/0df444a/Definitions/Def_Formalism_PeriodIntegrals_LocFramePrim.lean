-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocFramePrim
-- name    : Formalism_PeriodIntegrals_LocFramePrim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:59.496249+00:00
-- url     : https://prove2.me/theorems/ca5fbec1-570b-4ea3-b7c4-f2a4000b8561
-- title:
--   Loc Frame Prim
-- statement:
--   Definitions and structural lemmas for Loc Frame Prim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocFramePrim.lean

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
namespace PI.LocFramePrim
open NumberField IsDedekindDomain
open scoped TensorProduct Classical
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
def ratTup {M n : ℕ} (X : Fin n → Fin M → E) : Fin n → Fin M → R ⊗[F] E :=
  fun a i => inclR R (X a i)
def ratV {n : ℕ} (x : Fin n → E) : Fin n → R ⊗[F] E := fun i => inclR R (x i)
end Alg
abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
section Level
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
def latLoc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' Λ)
end Level
section Frames
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E
def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))
def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)
variable {n : ℕ} (Λ : Set (Fin n → E))
def IsPrim {a : ℕ} (X : TupV (E := E) v n a) : Prop :=
  (∀ i, X i ∈ latLoc (E := E) v Λ) ∧
  ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ → ∀ i, c i ∈ OEv (E := E) v
def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d
def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1
def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1
def locF {r : ℕ} (X : TupV (E := E) v n (r + 1)) : TupV (E := E) v n (r + 1) :=
  fun a => sc (E := E) v (alp v r a) • X a
end Frames
section Split
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def ddE : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
variable {F}
def latSpan {n r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (w : Fin r → Fin n → E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • w a}
end Split
def Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))
end PI.LocFramePrim


