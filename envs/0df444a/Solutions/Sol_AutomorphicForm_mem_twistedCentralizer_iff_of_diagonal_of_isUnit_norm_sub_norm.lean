-- Prove2me | solution 1 for AutomorphicForm.mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/69d2ca99-4969-5715-8054-378c4e9caa14

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Theorems.Thm_AutomorphicForm_sigmaTensor_apply_eq_self_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace R4S30TwistedTorus

section Norm

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "E" => L ⊗[K] A

theorem sigmaTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (x : A) :
    AutomorphicForm.sigmaTensor K L A τ (l ⊗ₜ x) = τ l ⊗ₜ x := rfl

theorem sigmaTensor_one_tmul (τ : L ≃ₐ[K] L) (x : A) :
    AutomorphicForm.sigmaTensor K L A τ ((1 : L) ⊗ₜ x) = (1 : L) ⊗ₜ x := by
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_alg_one (x : E) : AutomorphicForm.sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (k : ℕ) (x : E) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] x = AutomorphicForm.sigmaTensor K L A (σ ^ k) x := by
  induction k generalizing x with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, sigmaTensor_alg_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, pow_succ', AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem comm_map_id (τ : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L
        (Algebra.TensorProduct.map (AlgHom.id K A) (τ : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A τ (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul,
        TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul, sigmaTensor_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable [FiniteDimensional K L] [IsGalois K L]

theorem one_tmul_norm_eq_prod_univ (x : E) :
    (1 : L) ⊗ₜ[K] Algebra.norm A x = ∏ τ : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A τ x := by
  set e := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with he
  set z : A ⊗[K] L := e.symm x with hz
  have hx : x = e z := by rw [hz, AlgEquiv.apply_symm_apply]
  have hnorm : Algebra.norm A x = Algebra.norm A z := by rw [hx]; exact Algebra.norm_eq_of_algEquiv e z
  have h := Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z
  have h' := congrArg e h
  rw [AlgEquiv.commutes, map_prod] at h'
  have halg : algebraMap A E (Algebra.norm A z) = (1 : L) ⊗ₜ Algebra.norm A z := rfl
  rw [hnorm, ← halg, h']
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [comm_map_id, ← hx]

variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
include hgen

theorem orderOf_eq_finrank : orderOf σ = Module.finrank K L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

theorem pow_finrank_eq_one : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank K L σ hgen]; exact pow_orderOf_eq_one σ

theorem prod_range_iterate_eq_prod_univ (x : E) :
    ∏ i ∈ Finset.range (Module.finrank K L), (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] x =
      ∏ τ : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A τ x := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) ↑(Finset.range (Module.finrank K L)) := by
    rw [Finset.coe_range, ← orderOf_eq_finrank K L σ hgen]
    exact pow_injOn_Iio_orderOf
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  rw [← himg, Finset.prod_image hinj]
  exact Finset.prod_congr rfl fun i _ => sigmaTensor_iterate K L A σ i x

theorem prod_range_iterate_eq_one_tmul_norm (x : E) :
    ∏ i ∈ Finset.range (Module.finrank K L), (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] x =
      (1 : L) ⊗ₜ[K] Algebra.norm A x := by
  rw [prod_range_iterate_eq_prod_univ K L A σ hgen, one_tmul_norm_eq_prod_univ]

theorem sigmaTensor_iterate_finrank (x : E) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  rw [sigmaTensor_iterate, pow_finrank_eq_one K L σ hgen, sigmaTensor_alg_one]

theorem mem_range_of_fixed (l : L) (hl : σ l = l) : l ∈ (algebraMap K L).range := by
  rw [RingHom.mem_range, ← Set.mem_range, IsGalois.mem_range_algebraMap_iff_fixed]
  intro f
  have hf : f ∈ Subgroup.zpowers σ := hgen f
  have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) l :=
    Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hl)
  exact hstab hf

end Norm

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "E" => L ⊗[K] A

theorem sigmaGL_apply (t : GL (Fin 2) E) (i j : Fin 2) :
    (AutomorphicForm.sigmaGL K L A σ t : Matrix (Fin 2) (Fin 2) E) i j =
      AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) i j) := rfl

theorem sigmaGL_iterate_apply (k : ℕ) (t : GL (Fin 2) E) (i j : Fin 2) :
    (((⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) i j =
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] ((t : Matrix (Fin 2) (Fin 2) E) i j) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL_apply, ih]

def P (δ : GL (Fin 2) E) (k : ℕ) : GL (Fin 2) E :=
  ((List.range k).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod

theorem P_zero (δ : GL (Fin 2) E) : P K L A σ δ 0 = 1 := by simp [P]

theorem P_succ (δ : GL (Fin 2) E) (k : ℕ) :
    P K L A σ δ (k + 1) = P K L A σ δ k * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ := by
  unfold P
  rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem normString_eq_P (δ : GL (Fin 2) E) :
    AutomorphicForm.normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem mul_P_eq (δ t : GL (Fin 2) E) (h : t * δ = δ * AutomorphicForm.sigmaGL K L A σ t) (k : ℕ) :
    t * P K L A σ δ k = P K L A σ δ k * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t := by
  induction k with
  | zero => simp [P]
  | succ k ih =>
      have hk : (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ =
          (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k + 1] t := by
        rw [← iterate_map_mul, h, iterate_map_mul, Function.iterate_succ_apply]
      rw [P_succ, ← mul_assoc, ih, mul_assoc, hk, ← mul_assoc]

theorem P_apply (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (k : ℕ) :
    ((P K L A σ δ k : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 ∧
    ((P K L A σ δ k : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 ∧
    ((P K L A σ δ k : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 0 0 =
      ∏ i ∈ Finset.range k, (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ∧
    ((P K L A σ δ k : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 1 1 =
      ∏ i ∈ Finset.range k, (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) := by
  induction k with
  | zero =>
      rw [P_zero]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  | succ k ih =>
      obtain ⟨ih10, ih01, ih00, ih11⟩ := ih
      have hs10 : (((⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
        rw [sigmaGL_iterate_apply, h10, iterate_map_zero]
      have hs01 : (((⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
        rw [sigmaGL_iterate_apply, h01, iterate_map_zero]
      have hs00 := sigmaGL_iterate_apply K L A σ k δ 0 0
      have hs11 := sigmaGL_iterate_apply K L A σ k δ 1 1
      rw [P_succ, Units.val_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Matrix.mul_apply, Fin.sum_univ_two, ih10, hs10, zero_mul, mul_zero, add_zero]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, ih01, hs01, zero_mul, mul_zero, add_zero]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, ih00, ih01, hs00, zero_mul, add_zero, Finset.prod_range_succ]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, ih10, ih11, hs11, zero_mul, zero_add, Finset.prod_range_succ]

variable [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
include hgen

theorem normString_apply (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) :
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 0 0 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) 1 1 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) := by
  obtain ⟨p10, p01, p00, p11⟩ := P_apply K L A σ δ h10 h01 (Module.finrank K L)
  rw [normString_eq_P]
  exact ⟨p10, p01, by rw [p00, prod_range_iterate_eq_one_tmul_norm K L A σ hgen],
    by rw [p11, prod_range_iterate_eq_one_tmul_norm K L A σ hgen]⟩

theorem normString_eq_toTensorGL (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) :
    ∃ γ : GL (Fin 2) A, (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) A) 0 0 = Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) ∧
      (γ : Matrix (Fin 2) (Fin 2) A) 1 1 = Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) ∧
      AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A γ := by

  have hd : (δ : Matrix (Fin 2) (Fin 2) E) * ((δ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h00 := congrFun (congrFun hd 0) 0
  have h11 := congrFun (congrFun hd 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at h00 h11
  have hu0 : IsUnit ((δ : Matrix (Fin 2) (Fin 2) E) 0 0) := IsUnit.of_mul_eq_one _ h00
  have hu1 : IsUnit ((δ : Matrix (Fin 2) (Fin 2) E) 1 1) := IsUnit.of_mul_eq_one _ h11
  have hn0 : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 0 0)) := hu0.map (Algebra.norm A (S := L ⊗[K] A))
  have hn1 : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) E) 1 1)) := hu1.map (Algebra.norm A (S := L ⊗[K] A))
  obtain ⟨a, ha⟩ := hn0
  obtain ⟨b, hb⟩ := hn1
  let γ : GL (Fin 2) A :=
    { val := !![(a : A), 0; 0, (b : A)]
      inv := !![((a⁻¹ : Aˣ) : A), 0; 0, ((b⁻¹ : Aˣ) : A)]
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  obtain ⟨p10, p01, p00, p11⟩ := normString_apply K L A σ hgen δ h10 h01
  refine ⟨γ, rfl, rfl, ha, hb, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change _ = (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) i j)
  fin_cases i <;> fin_cases j
  · change _ = (1 : L) ⊗ₜ (a : A); rw [ha]; exact p00
  · change _ = (1 : L) ⊗ₜ (0 : A); rw [TensorProduct.tmul_zero]; exact p01
  · change _ = (1 : L) ⊗ₜ (0 : A); rw [TensorProduct.tmul_zero]; exact p10
  · change _ = (1 : L) ⊗ₜ (b : A); rw [hb]; exact p11

end NormString

section Centralizer

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L) [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "E" => L ⊗[K] A

theorem toTensorGL_apply (s : GL (Fin 2) A) (i j : Fin 2) :
    (AutomorphicForm.toTensorGL K L A s : Matrix (Fin 2) (Fin 2) E) i j =
      (1 : L) ⊗ₜ ((s : Matrix (Fin 2) (Fin 2) A) i j) := rfl

include hgen in
theorem sigmaGL_iterate_finrank (t : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[Module.finrank K L] t = t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate_finrank K L A σ hgen]

include hgen in

theorem of_mem (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (hN : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) -
      Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)))
    (t : GL (Fin 2) (L ⊗[K] A)) (ht : t ∈ AutomorphicForm.twistedCentralizer K L A σ δ) :
    (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 ∈
        Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ∧
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 ∈
        Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  obtain ⟨γ, hγ10, hγ01, hγ00, hγ11, hNγ⟩ := normString_eq_toTensorGL K L A σ hgen δ h10 h01
  set γE : GL (Fin 2) E := AutomorphicForm.toTensorGL K L A γ with hγE
  have ht' : t * δ = δ * AutomorphicForm.sigmaGL K L A σ t := by
    have := (AutomorphicForm.mem_sigmaCentralizer_iff).1 ht
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this

  have hcomm : t * γE = γE * t := by
    have h := mul_P_eq K L A σ δ t ht' (Module.finrank K L)
    rw [← normString_eq_P, sigmaGL_iterate_finrank K L A σ hgen, hNγ] at h
    exact h
  have hcommM : (t : Matrix (Fin 2) (Fin 2) E) * (γE : Matrix (Fin 2) (Fin 2) E) =
      (γE : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E) := by
    rw [← Units.val_mul, hcomm, Units.val_mul]
  have e00 : (γE : Matrix (Fin 2) (Fin 2) E) 0 0 = (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 0 0) := rfl
  have e11 : (γE : Matrix (Fin 2) (Fin 2) E) 1 1 = (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 1 1) := rfl
  have e01 : (γE : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by rw [hγE, toTensorGL_apply, hγ01, TensorProduct.tmul_zero]
  have e10 : (γE : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by rw [hγE, toTensorGL_apply, hγ10, TensorProduct.tmul_zero]
  have c01 := congrFun (congrFun hcommM 0) 1
  have c10 := congrFun (congrFun hcommM 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, mul_zero, zero_mul, add_zero, zero_add]
    at c01 c10

  obtain ⟨u, hu⟩ := (hN.neg).map (Algebra.TensorProduct.includeRight : A →ₐ[K] E)
  have hu' : (u : E) = (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 1 1) - (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 0 0) := by
    rw [hu, Algebra.TensorProduct.includeRight_apply, neg_sub, hγ00, hγ11, TensorProduct.tmul_sub]
  have ht01 : (t : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
    have : (t : Matrix (Fin 2) (Fin 2) E) 0 1 *
        ((1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 1 1) - (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 0 0)) = 0 := by
      rw [mul_sub, c01, mul_comm ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) 0 0)) ((t : Matrix (Fin 2) (Fin 2) E) 0 1),
        sub_self]
    rw [← hu'] at this
    exact (Units.mul_left_eq_zero u).1 this
  have ht10 : (t : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    have : (t : Matrix (Fin 2) (Fin 2) E) 1 0 *
        ((1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 1 1) - (1 : L) ⊗ₜ ((γ : Matrix (Fin 2) (Fin 2) A) 0 0)) = 0 := by
      rw [mul_sub, c10, mul_comm ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) 1 1)) ((t : Matrix (Fin 2) (Fin 2) E) 1 0),
        sub_self]
    rw [← hu'] at this
    exact (Units.mul_left_eq_zero u).1 this

  have hd : (δ : Matrix (Fin 2) (Fin 2) E) * ((δ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have d00 := congrFun (congrFun hd 0) 0
  have d11 := congrFun (congrFun hd 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at d00 d11
  obtain ⟨α, hα⟩ := IsUnit.of_mul_eq_one _ d00
  obtain ⟨β, hβ⟩ := IsUnit.of_mul_eq_one _ d11

  have htδ : (t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E) =
      (δ : Matrix (Fin 2) (Fin 2) E) * (AutomorphicForm.sigmaGL K L A σ t : Matrix (Fin 2) (Fin 2) E) := by
    rw [← Units.val_mul, ht', Units.val_mul]
  have f00 := congrFun (congrFun htδ 0) 0
  have f11 := congrFun (congrFun htδ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, sigmaGL_apply, ht01, ht10, mul_zero, zero_mul, add_zero,
    zero_add, map_zero] at f00 f11
  have hfix0 : AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 0) =
      (t : Matrix (Fin 2) (Fin 2) E) 0 0 := by
    have : (α : E) * AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 0) =
        (α : E) * (t : Matrix (Fin 2) (Fin 2) E) 0 0 := by rw [hα, ← f00, mul_comm]
    exact (Units.mul_right_inj α).1 this
  have hfix1 : AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 1) =
      (t : Matrix (Fin 2) (Fin 2) E) 1 1 := by
    have : (β : E) * AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 1) =
        (β : E) * (t : Matrix (Fin 2) (Fin 2) E) 1 1 := by rw [hβ, ← f11, mul_comm]
    exact (Units.mul_right_inj β).1 this
  have hfixK : ∀ x : L, σ x = x → x ∈ (algebraMap K L).range := fun x hx => mem_range_of_fixed K L σ hgen x hx
  exact ⟨ht10, ht01, (AutomorphicForm.sigmaTensor_apply_eq_self_iff K L A σ hfixK _).1 hfix0,
    (AutomorphicForm.sigmaTensor_apply_eq_self_iff K L A σ hfixK _).1 hfix1⟩

theorem mem_of (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (t : GL (Fin 2) (L ⊗[K] A))
    (ht10 : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (ht00 : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 ∈
        Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A))
    (ht11 : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 ∈
        Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  obtain ⟨y₀, hy₀⟩ := ht00
  obtain ⟨y₁, hy₁⟩ := ht11
  rw [Algebra.TensorProduct.includeRight_apply] at hy₀ hy₁

  have hσt : AutomorphicForm.sigmaGL K L A σ t = t := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [sigmaGL_apply]
    fin_cases i <;> fin_cases j
    · change AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 0) = (t : Matrix (Fin 2) (Fin 2) E) 0 0
      rw [← hy₀, sigmaTensor_one_tmul]
    · change AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 1) = (t : Matrix (Fin 2) (Fin 2) E) 0 1
      rw [ht01, map_zero]
    · change AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 0) = (t : Matrix (Fin 2) (Fin 2) E) 1 0
      rw [ht10, map_zero]
    · change AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 1) = (t : Matrix (Fin 2) (Fin 2) E) 1 1
      rw [← hy₁, sigmaTensor_one_tmul]
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, hσt, mul_inv_eq_iff_eq_mul]

  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases j
  · change ((t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E)) 0 0 =
      ((δ : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E)) 0 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ht01, ht10, mul_zero, zero_mul, add_zero, mul_comm]
  · change ((t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E)) 0 1 =
      ((δ : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E)) 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ht01, ht10, mul_zero, zero_mul, add_zero]
  · change ((t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E)) 1 0 =
      ((δ : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E)) 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ht01, ht10, mul_zero, zero_mul, add_zero]
  · change ((t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E)) 1 1 =
      ((δ : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E)) 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ht01, ht10, mul_zero, zero_mul, zero_add, mul_comm]

include hgen in
theorem mem_iff (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (hN : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) -
      Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)))
    (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  ⟨of_mem K L A σ hgen δ h10 h01 hN t, fun h => mem_of K L A σ δ h10 h01 t h.1 h.2.1 h.2.2.1 h.2.2.2⟩

end Centralizer

end R4S30TwistedTorus

end

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (hN : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) -
      Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)))
    (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  R4S30TwistedTorus.mem_iff K L A σ hgen δ h10 h01 hN t

end S_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm
end P2MW
export P2MW.S_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm (solution)
