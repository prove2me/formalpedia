-- Prove2me | solution 1 for AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3cca108f-eca7-5893-95d5-10ce4b868e66

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Ws31
namespace TwRes

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ringAut_mul_apply (f g : RingAut (AdeleRing (𝓞 L) L)) (x : AdeleRing (𝓞 L) L) : (f * g) x = f (g x) := rfl

theorem iterate_act_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (i : ℕ) (x : AdeleRing (𝓞 L) L) :
    (⇑(D.act σ))^[i] x = D.act (σ ^ i) x := by
  induction i generalizing x with
  | zero => rw [pow_zero, map_one]; rfl
  | succ i ih => rw [Function.iterate_succ_apply, ih, pow_succ, map_mul, ringAut_mul_apply]

theorem act_pow_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (i : ℕ) (x : AdeleRing (𝓞 L) L) :
    D.act (σ ^ i) (D.act σ x) = D.act (σ ^ (i + 1)) x := by
  rw [pow_succ, map_mul, ringAut_mul_apply]

theorem act_pow_zero (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    D.act (σ ^ 0) x = x := by
  rw [pow_zero, map_one]; rfl

theorem orderOf_eq_finrank [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank K L :=
  (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)

theorem pow_finrank_eq_one [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank K L σ hgen]; exact pow_orderOf_eq_one σ

theorem prod_range_pow_eq_prod_univ [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {M : Type*} [CommMonoid M] (f : (L ≃ₐ[K] L) → M) :
    ∏ i ∈ Finset.range (Module.finrank K L), f (σ ^ i) = ∏ τ : L ≃ₐ[K] L, f τ := by
  classical
  have hord := orderOf_eq_finrank K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) ↑(Finset.range (Module.finrank K L)) := by
    rw [Finset.coe_range, ← hord]; exact pow_injOn_Iio_orderOf
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hord, orderOf_eq_card_of_forall_mem_zpowers hgen,
      Nat.card_eq_fintype_card]
  rw [← himg, Finset.prod_image hinj]

theorem algebraMap_norm_eq_prod_range [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L) : algebraMap K L (Algebra.norm K x) = ∏ i ∈ Finset.range (Module.finrank K L), (σ ^ i) x := by
  rw [Algebra.norm_eq_prod_automorphisms, ← prod_range_pow_eq_prod_univ K L σ hgen (fun τ => τ x)]

theorem prod_range_telescope (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (u u' : AdeleRing (𝓞 L) L) (h : u' * u = 1) (m : ℕ) :
    ∏ i ∈ Finset.range m, (D.act (σ ^ i) u' * D.act (σ ^ (i + 1)) u) = u' * D.act (σ ^ m) u := by
  induction m with
  | zero => rw [Finset.prod_range_zero, act_pow_zero, h]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have : D.act (σ ^ m) u * D.act (σ ^ m) u' = 1 := by rw [← map_mul, mul_comm, h, map_one]
    calc u' * D.act (σ ^ m) u * (D.act (σ ^ m) u' * D.act (σ ^ (m + 1)) u)
        = u' * (D.act (σ ^ m) u * D.act (σ ^ m) u') * D.act (σ ^ (m + 1)) u := by ring
      _ = u' * D.act (σ ^ (m + 1)) u := by rw [this, mul_one]

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (b : AdelicGL2 (𝓞 L) L) (hb : b ∈ AutomorphicForm.adelicBorel (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (A B E : AdeleRing (𝓞 L) L)
    (hA : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A)
    (hB : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B)
    (hE : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E) :
    (IsUnit A ∧ IsUnit B) ∧
    A * (D.act σ) ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) =
      B * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) + E ∧
    (∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] A) ∧
    (∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[Module.finrank K L] r = r) := by
  classical

  have hb10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := hb
  set P : (AdeleRing (𝓞 L) L)ˣ := borelDiagFst ⟨b, hb⟩ with hP
  set R : (AdeleRing (𝓞 L) L)ˣ := borelDiagSnd ⟨b, hb⟩ with hR
  have hPval : (P : AdeleRing (𝓞 L) L) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 := rfl
  have hRval : (R : AdeleRing (𝓞 L) L) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 := rfl
  have hPinv : ((P⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 := rfl
  have hRinv : ((R⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 := rfl
  have hbinv10 : ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 :=
    (adelicBorel (𝓞 L) L).inv_mem hb
  set p := (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hp
  set q := (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 with hq
  set r := (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 with hr
  set p' := ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hp'
  set q' := ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 with hq'
  set r' := ((b⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 with hr'
  have hp'p : p' * p = 1 := by rw [← hPval, ← hPinv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hr'r : r' * r = 1 := by rw [← hRval, ← hRinv, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  have hrel : p' * q + q' * r = 0 := by
    have h := congrArg (fun u : AdelicGL2 (𝓞 L) L => (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1) (inv_mul_cancel b)
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Units.val_one,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h
    exact h

  set t0 := (t : Matrix (Fin 2) (Fin 2) L) 0 0 with ht0
  set t1 := (t : Matrix (Fin 2) (Fin 2) L) 1 1 with ht1'
  have hdet : t0 * t1 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det t).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ht₁, mul_zero, sub_zero] at this
    exact this
  have ht0ne : t0 ≠ 0 := left_ne_zero_of_mul hdet
  have ht1ne : t1 ≠ 0 := right_ne_zero_of_mul hdet

  have hT : ∀ i j, ((globalPoints (𝓞 L) L t : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      algebraMap L (AdeleRing (𝓞 L) L) ((t : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
  have hZ : ∀ i j, ((centralScalar (𝓞 L) L z * b : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (z : AdeleRing (𝓞 L) L) * (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j := by
    intro i j
    have hval : ((centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
        Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
    rw [Units.val_mul, hval, Matrix.scalar_apply, Matrix.diagonal_mul]
  have hS : ∀ (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2),
      ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
        D.act σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := fun g i j => rfl

  have hA' : A = p' * algebraMap L (AdeleRing (𝓞 L) L) t0 * D.act σ ((z : AdeleRing (𝓞 L) L) * p) := by
    rw [← hA]
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hT, hS, hZ, hb10, ht₁, ht₂, hbinv10,
      map_zero, mul_zero, zero_mul, add_zero, zero_add]
    ring
  have hB' : B = r' * algebraMap L (AdeleRing (𝓞 L) L) t1 * D.act σ ((z : AdeleRing (𝓞 L) L) * r) := by
    rw [← hB]
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hT, hS, hZ, hb10, ht₁, ht₂, hbinv10,
      map_zero, mul_zero, zero_mul, add_zero, zero_add]
    ring
  have hE' : E = p' * algebraMap L (AdeleRing (𝓞 L) L) t0 * D.act σ ((z : AdeleRing (𝓞 L) L) * q) + q' * algebraMap L (AdeleRing (𝓞 L) L) t1 * D.act σ ((z : AdeleRing (𝓞 L) L) * r) := by
    rw [← hE]
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hT, hS, hZ, hb10, ht₁, ht₂, hbinv10,
      map_zero, mul_zero, zero_mul, add_zero, zero_add]
    ring

  have hιt0 : IsUnit (algebraMap L (AdeleRing (𝓞 L) L) t0) := (isUnit_iff_ne_zero.mpr ht0ne).map (algebraMap L (AdeleRing (𝓞 L) L))
  have hιt1 : IsUnit (algebraMap L (AdeleRing (𝓞 L) L) t1) := (isUnit_iff_ne_zero.mpr ht1ne).map (algebraMap L (AdeleRing (𝓞 L) L))
  have hp'u : IsUnit p' := ⟨P⁻¹, hPinv⟩
  have hr'u : IsUnit r' := ⟨R⁻¹, hRinv⟩
  have hzu : IsUnit (z : AdeleRing (𝓞 L) L) := Units.isUnit z
  have hpu : IsUnit p := ⟨P, hPval⟩
  have hru : IsUnit r := ⟨R, hRval⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hA']; exact (hp'u.mul hιt0).mul ((hzu.mul hpu).map (D.act σ))
  · rw [hB']; exact (hr'u.mul hιt1).mul ((hzu.mul hru).map (D.act σ))
  ·
    have hx : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 * ((borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) = q * p' := by
      rw [← hP, hPinv]
    rw [hx, hA', hB', hE', map_mul, map_mul, map_mul, map_mul]
    have hsp : D.act σ p * D.act σ p' = 1 := by rw [← map_mul, mul_comm, hp'p, map_one]
    linear_combination (p' * algebraMap L (AdeleRing (𝓞 L) L) t0 * D.act σ (z : AdeleRing (𝓞 L) L) * D.act σ q) * hsp + (-(algebraMap L (AdeleRing (𝓞 L) L) t1 * D.act σ (z : AdeleRing (𝓞 L) L) * D.act σ r * r')) * hrel +
      (algebraMap L (AdeleRing (𝓞 L) L) t1 * D.act σ (z : AdeleRing (𝓞 L) L) * D.act σ r * q') * hr'r
  ·
    simp only [iterate_act_eq]
    have hBi : ∀ i : ℕ, D.act (σ ^ i) B =
        (D.act (σ ^ i) r' * D.act (σ ^ (i + 1)) r) * (D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) t1) * D.act (σ ^ (i + 1)) (z : AdeleRing (𝓞 L) L)) := by
      intro i; rw [hB']; simp only [map_mul, act_pow_act]; ring
    have hAi : ∀ i : ℕ, D.act (σ ^ i) A =
        (D.act (σ ^ i) p' * D.act (σ ^ (i + 1)) p) * (D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) t0) * D.act (σ ^ (i + 1)) (z : AdeleRing (𝓞 L) L)) := by
      intro i; rw [hA']; simp only [map_mul, act_pow_act]; ring
    rw [Finset.prod_congr rfl (fun i _ => hBi i), Finset.prod_congr rfl (fun i _ => hAi i),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib (f := fun i => D.act (σ ^ i) p' * D.act (σ ^ (i + 1)) p),
      prod_range_telescope K L D σ r r' hr'r, prod_range_telescope K L D σ p p' hp'p,
      pow_finrank_eq_one K L σ hgen, map_one]
    have h1r : (1 : RingAut (AdeleRing (𝓞 L) L)) r = r := rfl
    have h1p : (1 : RingAut (AdeleRing (𝓞 L) L)) p = p := rfl
    rw [h1r, h1p, hr'r, hp'p, one_mul, one_mul, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib (f := fun i => D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) t0))]
    have hcomp : ∀ (i : ℕ) (x : L), D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) x) = algebraMap L (AdeleRing (𝓞 L) L) ((σ ^ i) x) :=
      fun i x => D.compat (σ ^ i) x
    have h1 : ∏ i ∈ Finset.range (Module.finrank K L), D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) t1) =
        algebraMap L (AdeleRing (𝓞 L) L) (∏ i ∈ Finset.range (Module.finrank K L), (σ ^ i) t1) := by
      rw [map_prod]; exact Finset.prod_congr rfl fun i _ => hcomp i t1
    have h0 : ∏ i ∈ Finset.range (Module.finrank K L), D.act (σ ^ i) (algebraMap L (AdeleRing (𝓞 L) L) t0) =
        algebraMap L (AdeleRing (𝓞 L) L) (∏ i ∈ Finset.range (Module.finrank K L), (σ ^ i) t0) := by
      rw [map_prod]; exact Finset.prod_congr rfl fun i _ => hcomp i t0
    rw [h1, h0, algebraMap_norm_eq_prod_range K L σ hgen, ← mul_assoc, ← map_mul, ← Finset.prod_mul_distrib]
    congr 2
    exact Finset.prod_congr rfl fun i _ => by rw [← map_mul, div_mul_cancel₀ _ ht0ne]
  ·
    intro x
    rw [iterate_act_eq, pow_finrank_eq_one K L σ hgen, map_one]
    rfl

end Ws31.TwRes

end

open scoped TensorProduct.RightActions in
open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (b : AdelicGL2 (𝓞 L) L) (hb : b ∈ AutomorphicForm.adelicBorel (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (A B E : AdeleRing (𝓞 L) L)
    (hA : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A)
    (hB : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B)
    (hE : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E) :
    (IsUnit A ∧ IsUnit B) ∧
    A * (D.act σ) ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) =
      B * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) + E ∧
    (∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] A) ∧
    (∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[Module.finrank K L] r = r) :=
  Ws31.TwRes.main K L D σ hgen t ht₁ ht₂ b hb z A B E hA hB hE

end S_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal (solution)
