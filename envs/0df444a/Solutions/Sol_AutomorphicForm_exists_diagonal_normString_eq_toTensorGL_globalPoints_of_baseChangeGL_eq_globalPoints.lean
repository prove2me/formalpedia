-- Prove2me | solution 1 for AutomorphicForm.exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dc267333-e786-59c5-b2f7-4e6bc54b554a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

namespace NSD9

open AutomorphicForm

section general

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem val_mul_apply (x y : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((x * y : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i 0 * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i 1 * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_apply (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := rfl

theorem sigmaGL_iterate_apply (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL_apply, ih]

theorem toTensorGL_apply (g : GL (Fin 2) A) (i j : Fin 2) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((g : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem prod_iterate_diag (x : GL (Fin 2) (L ⊗[K] A))
    (h01 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (h10 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0)
    (n : ℕ) :
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
        ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)).prod ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
        ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)).prod ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h00, h11, h01', h10'⟩ := ih
    have e01 : (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sigmaGL_iterate_apply, h01]; exact Function.iterate_fixed (map_zero _) n
    have e10 : (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sigmaGL_iterate_apply, h10]; exact Function.iterate_fixed (map_zero _) n
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [val_mul_apply, h00, h01', zero_mul, add_zero, sigmaGL_iterate_apply]
    · rw [val_mul_apply, h11, h10', zero_mul, zero_add, sigmaGL_iterate_apply]
    · rw [val_mul_apply, h01', e01, mul_zero, zero_mul, add_zero]
    · rw [val_mul_apply, h10', e10, mul_zero, zero_mul, add_zero]

theorem sigmaTensor_iterate_tmul_one (n : ℕ) (l : L) :
    (⇑(sigmaTensor K L A σ))^[n] (l ⊗ₜ[K] (1 : A)) = ((⇑σ)^[n] l) ⊗ₜ[K] (1 : A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (((⇑σ)^[n] l) ⊗ₜ[K] (1 : A)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

theorem list_prod_tmul_one (f : ℕ → L) (n : ℕ) :
    ((List.range n).map fun i => (f i) ⊗ₜ[K] (1 : A)).prod = ((List.range n).map f).prod ⊗ₜ[K] (1 : A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton, ih,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem list_prod_range_eq_finset_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton, ih,
      Finset.prod_range_succ]

end general

theorem prod_range_pow_apply_eq_norm (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L) :
    ∏ i ∈ Finset.range (Module.finrank K L), (σ ^ i) x = algebraMap K L (Algebra.norm K x) := by
  classical
  have hord : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact IsGalois.card_aut_eq_finrank K L
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Module.finrank K L) : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < orderOf σ := by rw [hord]; exact Finset.mem_range.mp hi
    have hj' : j < orderOf σ := by rw [hord]; exact Finset.mem_range.mp hj
    have := (pow_inj_mod (x := σ)).mp hij
    rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank K L).symm
  rw [Algebra.norm_eq_prod_automorphisms, ← himg, Finset.prod_image hinj]

end NSD9

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) :
    ∃ γ : GL (Fin 2) K,
      (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)  := by
  classical
  set A := AdeleRing (𝓞 K) K with hA

  have hdet : (t : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [Matrix.det_fin_two, ht₁, mul_zero, sub_zero] at hdet
  obtain ⟨ht00, ht11⟩ := mul_ne_zero_iff.mp hdet
  set n0 : K := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) with hn0
  set n1 : K := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) with hn1
  have hn0' : n0 ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht00
  have hn1' : n1 ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht11
  have hγdet : (!![n0, 0; 0, n1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two]; simp [hn0', hn1']
  set γ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hγdet with hγ
  have hγv : ∀ i j : Fin 2, ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = (!![n0, 0; 0, n1] : Matrix (Fin 2) (Fin 2) K) i j :=
    fun _ _ => rfl
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hγv]; simp
  · rw [hγv]; simp
  · rw [hγv]; simp [hn0]
  · rw [hγv]; simp [hn1]

  have hδv : ∀ i j : Fin 2, ((δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      ((t : Matrix (Fin 2) (Fin 2) L) i j) ⊗ₜ[K] (1 : A) := by
    intro i j
    have h := congrArg (fun M : GL (Fin 2) (AdeleRing (𝓞 L) L) => (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) hδ
    change (baseChangeEquiv K L) (((δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) =
      algebraMap L (AdeleRing (𝓞 L) L) ((t : Matrix (Fin 2) (Fin 2) L) i j) at h
    rw [← baseChangeEquiv_tmul_one K L] at h
    exact (baseChangeEquiv K L).injective h
  have hδ01 : ((δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
    rw [hδv, ht₂, TensorProduct.zero_tmul]
  have hδ10 : ((δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
    rw [hδv, ht₁, TensorProduct.zero_tmul]
  obtain ⟨h00, h11, h01, h10⟩ := NSD9.prod_iterate_diag K L A σ δ hδ01 hδ10 (Module.finrank K L)

  have key : ∀ l : L,
      ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaTensor K L A σ))^[i] (l ⊗ₜ[K] (1 : A))).prod =
        (1 : L) ⊗ₜ[K] algebraMap K A (Algebra.norm K l) := by
    intro l
    have e1 : ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaTensor K L A σ))^[i] (l ⊗ₜ[K] (1 : A))) =
        (List.range (Module.finrank K L)).map fun i => ((σ ^ i) l) ⊗ₜ[K] (1 : A) := by
      refine List.map_congr_left fun i _ => ?_
      rw [NSD9.sigmaTensor_iterate_tmul_one, AlgEquiv.coe_pow]
    rw [e1, NSD9.list_prod_tmul_one K L A (fun i => (σ ^ i) l), NSD9.list_prod_range_eq_finset_prod,
      NSD9.prod_range_pow_apply_eq_norm K L σ hgen l, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have E : ∀ i j : Fin 2,
      ((((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] algebraMap K A ((!![n0, 0; 0, n1] : Matrix (Fin 2) (Fin 2) K) i j) := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [h00, hδv, key]; simp [hn0]
    · rw [h01]; simp
    · rw [h10]; simp
    · rw [h11, hδv, key]; simp [hn1]
  apply Units.ext
  ext i j
  change ((((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = _
  rw [NSD9.toTensorGL_apply, Algebra.TensorProduct.includeRight_apply, E i j]
  rfl

end S_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
end P2MW
export P2MW.S_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints (solution)
