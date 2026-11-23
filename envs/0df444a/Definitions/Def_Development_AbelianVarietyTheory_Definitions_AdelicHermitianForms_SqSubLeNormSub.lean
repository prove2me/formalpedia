-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- name    : Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:52.974951+00:00
-- url     : https://prove2.me/theorems/e14c01cd-2bbb-4103-900d-1cf0fc04e94d
-- title:
--   Sq Sub Le Norm Sub
-- statement:
--   Definitions and structural lemmas for Sq Sub Le Norm Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
namespace GlobalTheory.QNorm
def sqSub {F L : Type} [Field F] [Field L] (φ : F →+* L) : Subgroup Fˣ where
  carrier := {x | IsSquare (φ (x : F))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simpa using IsSquare.mul ha hb
  inv_mem' := by
    intro a ha
    simpa using IsSquare.inv ha
def normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) : Subgroup Fˣ where
  carrier := {x | ∃ a b : L, φ (x : F) = a ^ 2 - φ δ * b ^ 2}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, b, h⟩ ⟨c, d, h'⟩
    refine ⟨a * c + φ δ * b * d, a * d + b * c, ?_⟩
    rw [Units.val_mul, map_mul, h, h']; ring
  inv_mem' := by
    rintro x ⟨a, b, h⟩
    have hx : φ (x : F) ≠ 0 := by simp
    refine ⟨a / φ (x : F), b / φ (x : F), ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
    rw [← h]
def sqs {G : Type} [CommGroup G] (U : Subgroup G) : Subgroup G := U.map (powMonoidHom 2)
def hiUnits {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (n : ℕ) : Subgroup Kˣ where
  carrier := {x | w (x : K) = 1 ∧ w ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have : ((x * y : Kˣ) : K) - 1 = (x : K) * ((y : K) - 1) + ((x : K) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    refine le_trans (w.map_add _ _) (max_le ?_ hx')
    rw [map_mul, hx, one_mul]; exact hy'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have : ((x⁻¹ : Kˣ) : K) - 1 = -((x : K)⁻¹ * ((x : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hx'
def EvenNorms {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (Δ : K) : Prop :=
  ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → ∃ n : ℤ, w (a ^ 2 - Δ * b ^ 2) = WithZero.exp (2 * n)
variable (F : Type) [Field F] [NumberField F]
def sUnits (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (S : Set (HeightOneSpectrum (𝓞 F))).unit F
def finSq (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))
def locSq (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  finSq F S ⊓ ⨅ σ : F →+* ℝ, sqSub σ
def locNorm (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (⨅ v ∈ S, normSub (algebraMap F (v.adicCompletion F)) δ) ⊓ ⨅ σ : F →+* ℝ, normSub σ δ
def tFin (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  Set.ncard {v : HeightOneSpectrum (𝓞 F) |
    v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)}
def tReal (δ : F) : ℕ := Set.ncard {σ : F →+* ℝ | σ δ < 0}
def admitted (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F 2 = 1 ∧
    ∃ π : F, v.valuation F π = WithZero.exp (-1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F π = 1
structure IsQuad {F E : Type} [Field F] [Field E] [Algebra F E] (δ : F) (θ : E)
    (σ : E ≃ₐ[F] E) : Prop where
  nonsq : ¬ IsSquare δ
  sq : θ ^ 2 = algebraMap F E δ
  conj : σ θ = -θ
  span : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ
end GlobalTheory.QNorm
end


