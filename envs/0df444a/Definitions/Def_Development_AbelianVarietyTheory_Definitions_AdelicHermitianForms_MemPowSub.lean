-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
-- name    : Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:17.799492+00:00
-- url     : https://prove2.me/theorems/efb9b3c2-de3d-43a8-99ac-59bb64de4dab
-- title:
--   Mem Pow Sub
-- statement:
--   Definitions and structural lemmas for Mem Pow Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CNorm
def pows (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : Subgroup G := U.map (powMonoidHom p)
def pIdx (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ := (pows p U).relIndex U
def pTor (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ :=
  Nat.card {x : G // x ∈ U ∧ x ^ p = 1}
def nrm {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) : A →* A where
  toFun a := ∏ i ∈ Finset.range n, σ^[i] a
  map_one' := by simp [iterate_map_one]
  map_mul' a b := by simp [iterate_map_mul, Finset.prod_mul_distrib]
def dif {A : Type} [CommGroup A] (σ : A →* A) : A →* A where
  toFun a := σ a / a
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_div_mul_comm]
def fix {A : Type} [CommGroup A] (σ : A →* A) : Subgroup A := σ.eqLocus (MonoidHom.id A)
def oneUnits {O : Type} [CommRing O] (t : O) : Subgroup Oˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t})).ker
def powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) : Subgroup Fˣ where
  carrier := {x | ∃ r : L, r ^ p = φ (x : F)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [mul_pow, hr, hs, Units.val_mul, map_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [inv_pow, hr, Units.val_inv_eq_inv_val, map_inv₀]⟩
def kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) : Subgroup Fˣ :=
  (Units.map (Algebra.norm L : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →* L)).range.comap
    (Units.map (φ : F →* L))
structure IsKum (p : ℕ) {F E : Type} [Field F] [Field E] [Algebra F E] (ζ δ : F) (θ : E)
    (σ : E ≃ₐ[F] E) : Prop where
  prime : p.Prime
  root : IsPrimitiveRoot ζ p
  nonpow : ∀ r : F, r ^ p ≠ δ
  pow : θ ^ p = algebraMap F E δ
  conj : σ θ = algebraMap F E ζ * θ
  gen : Algebra.adjoin F {θ} = ⊤
def TNorm (F E L : Type) [Field F] [Field E] [Algebra F E] [Field L] [Algebra F L] (x : F) : Prop :=
  ∃ y : L ⊗[F] E, Algebra.norm L y = algebraMap F L x
section
variable (p : ℕ) (F : Type) [Field F] [NumberField F]
def finPow (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, powSub p (algebraMap F (v.adicCompletion F))
def finNorm (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, kNorm p (algebraMap F (v.adicCompletion F)) δ
def tNon (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  Set.ncard {v : HeightOneSpectrum (𝓞 F) |
    v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ}
def AdmP (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  GlobalTheory.QNorm.admitted F S ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (p : F) = 1
end
def LocNorm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (x : F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), TNorm F E (v.adicCompletion F) x) ∧
    ∀ a : Algebra F ℝ, @TNorm F E ℝ _ _ _ _ a x
def NP (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Prop :=
  ∀ x : F, x ≠ 0 → LocNorm F E x → ∃ y : E, Algebra.norm F y = x
end GlobalTheory.CNorm
end


