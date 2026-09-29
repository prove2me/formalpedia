-- Prove2me | solution 1 for AutomorphicForm.exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ef9d51de-557c-5d11-a738-3b8d0de37984

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace DivAlg

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_one_tmul (a : A) :
    AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((AutomorphicForm.sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = AutomorphicForm.sigmaTensor K L A σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((AutomorphicForm.sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ) := by
  ext i j
  exact sigmaGL_apply K L A σ g i j

theorem sigmaGL_sigmaGL (hσ : ∀ l : L, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.sigmaGL K L A σ g) = g := by
  ext i j
  rw [sigmaGL_apply, sigmaGL_apply, sigmaTensor_sigmaTensor K L A σ hσ]

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A γ)
      = AutomorphicForm.toTensorGL K L A γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem scalar_apply (u : (L ⊗[K] A)ˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = if i = j then (u : L ⊗[K] A) else 0 := by
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem sigmaGL_scalar (u : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) u) := by
  ext i j
  rw [sigmaGL_apply, scalar_apply, scalar_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem toTensorGL_scalar (c : Aˣ) :
    AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A)
            c) := by
  ext i j
  rw [toTensorGL_apply, scalar_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem scalar_mul_comm (u : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  push_cast
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact (Matrix.scalar_commute (u : L ⊗[K] A) (fun r' => Commute.all _ r') _).eq

theorem conj_scalar (u : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) u * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  rw [← scalar_mul_comm, mul_inv_cancel_right]

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = δ * AutomorphicForm.sigmaGL K L A σ δ := by
  simp [AutomorphicForm.normString, h2, List.range_succ]

end Twist

section H90

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

def phi (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) : Fin 2 → L ⊗[K] A :=
  (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec fun i => AutomorphicForm.sigmaTensor K L A σ (w i)

theorem phi_add (ε : GL (Fin 2) (L ⊗[K] A)) (w w' : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (w + w') = phi K L A σ ε w + phi K L A σ ε w' := by
  unfold phi
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem phi_smul (ε : GL (Fin 2) (L ⊗[K] A)) (b : L ⊗[K] A) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (b • w) = AutomorphicForm.sigmaTensor K L A σ b • phi K L A σ ε w := by
  unfold phi
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem phi_neg (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (-w) = -phi K L A σ ε w := by
  rw [← neg_one_smul (L ⊗[K] A) w, phi_smul, map_neg, map_one, neg_one_smul]

theorem phi_sub (ε : GL (Fin 2) (L ⊗[K] A)) (w w' : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (w - w') = phi K L A σ ε w - phi K L A σ ε w' := by
  rw [sub_eq_add_neg, phi_add, phi_neg, ← sub_eq_add_neg]

theorem phi_algebraMap_smul (ε : GL (Fin 2) (L ⊗[K] A)) (a : A) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (a • w) = a • phi K L A σ ε w := by
  have h1 : a • w = (algebraMap A (L ⊗[K] A) a) • w := by
    funext i; simp [Algebra.smul_def]
  have h2 : a • phi K L A σ ε w = (algebraMap A (L ⊗[K] A) a) • phi K L A σ ε w := by
    funext i; simp [Algebra.smul_def]
  rw [h1, h2, phi_smul]
  congr 1
  exact sigmaTensor_one_tmul K L A σ a

theorem phi_phi (hσ : ∀ l : L, σ (σ l) = l) (ε : GL (Fin 2) (L ⊗[K] A))
    (hε : ε * AutomorphicForm.sigmaGL K L A σ ε = 1) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (phi K L A σ ε w) = w := by
  have hmat : (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ) = 1 := by
    have := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hε
    simpa [coe_sigmaGL] using this
  unfold phi
  have hin : (fun i => AutomorphicForm.sigmaTensor K L A σ
        ((ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec
          (fun k => AutomorphicForm.sigmaTensor K L A σ (w k)) i))
      = ((ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ)).mulVec
          w := by
    funext i
    rw [RingHom.map_mulVec]
    congr 1
    funext k
    exact sigmaTensor_sigmaTensor K L A σ hσ (w k)
  rw [hin, Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

def phiLin (ε : GL (Fin 2) (L ⊗[K] A)) : (Fin 2 → L ⊗[K] A) →ₗ[A] (Fin 2 → L ⊗[K] A) where
  toFun := phi K L A σ ε
  map_add' := phi_add K L A σ ε
  map_smul' := phi_algebraMap_smul K L A σ ε

def fixedSub (ε : GL (Fin 2) (L ⊗[K] A)) : Submodule A (Fin 2 → L ⊗[K] A) :=
  LinearMap.eqLocus (phiLin K L A σ ε) LinearMap.id

theorem mem_fixedSub (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) :
    w ∈ fixedSub K L A σ ε ↔ phi K L A σ ε w = w :=
  Iff.rfl

def mulUnit (η : (L ⊗[K] A)ˣ) : (Fin 2 → L ⊗[K] A) ≃ₗ[A] (Fin 2 → L ⊗[K] A) where
  toFun w := (η : L ⊗[K] A) • w
  invFun w := ((η⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) • w
  map_add' := smul_add _
  map_smul' a w := by
    funext i
    simp [Algebra.smul_def, mul_left_comm]
  left_inv w := by
    simp [smul_smul]
  right_inv w := by
    simp [smul_smul]

variable [CharZero A]

theorem fixedSub_inf_map_eq_bot (ε : GL (Fin 2) (L ⊗[K] A)) (η : (L ⊗[K] A)ˣ)
    (hη : AutomorphicForm.sigmaTensor K L A σ η = -η) :
    fixedSub K L A σ ε ⊓ (fixedSub K L A σ ε).map (mulUnit K L A η).toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxV, hxW⟩
  obtain ⟨w, hw, rfl⟩ := hxW
  have hwV : phi K L A σ ε w = w := hw
  have hxV' : phi K L A σ ε ((η : L ⊗[K] A) • w) = (η : L ⊗[K] A) • w := hxV
  rw [phi_smul, hη, hwV, neg_smul] at hxV'

  have h2 : (2 : A) • ((η : L ⊗[K] A) • w) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hxV']
    exact neg_add_cancel _
  have := congrArg (fun y => (2 : A)⁻¹ • y) h2
  simpa [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : A) ≠ 0)] using this

theorem finrank_fixedSub_le (h2 : Module.finrank K L = 2) (ε : GL (Fin 2) (L ⊗[K] A))
    (η : (L ⊗[K] A)ˣ) (hη : AutomorphicForm.sigmaTensor K L A σ η = -η) :
    Module.finrank A (fixedSub K L A σ ε) ≤ 2 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have h4 : Module.finrank A (Fin 2 → L ⊗[K] A) = 4 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      TensorProduct.finrank_rightAlgebra, h2, smul_eq_mul]
  set V := fixedSub K L A σ ε
  set V' := V.map (mulUnit K L A η).toLinearMap
  have hV' : Module.finrank A V' = Module.finrank A V := LinearEquiv.finrank_map_eq _ _
  have hinf : Module.finrank A ↥(V ⊓ V') = 0 := by
    rw [fixedSub_inf_map_eq_bot K L A σ ε η hη, finrank_bot]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V V'
  have hle : Module.finrank A ↥(V ⊔ V') ≤ 4 := h4 ▸ Submodule.finrank_le _
  omega

omit [CharZero A] in

theorem exists_pair_of_finrank_le_two {M : Type*} [AddCommGroup M] [Module A M]
    (W : Submodule A M) [FiniteDimensional A W] (h : Module.finrank A W ≤ 2) :
    ∃ v : Fin 2 → M, (∀ j, v j ∈ W) ∧ W ≤ Submodule.span A (Set.range v) := by
  set n := Module.finrank A W
  let b := Module.finBasis A W
  let v : Fin 2 → M := fun j => if hj : (j : ℕ) < n then (b ⟨j, hj⟩ : M) else 0
  refine ⟨v, fun j => ?_, fun w hw => ?_⟩
  · by_cases hj : (j : ℕ) < n
    · simp only [v, dif_pos hj]; exact Submodule.coe_mem _
    · simp only [v, dif_neg hj]; exact zero_mem _
  · have hb : (⟨w, hw⟩ : W) ∈ Submodule.span A (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := W.subtype) hb
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    have hi : ((⟨i, by omega⟩ : Fin 2) : ℕ) < n := i.2
    simp only [v, dif_pos hi, Function.comp_apply, Submodule.coe_subtype]

theorem hilbert90 (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
    (hℓ : ∃ ℓ : L, σ ℓ ≠ ℓ) (ε : GL (Fin 2) (L ⊗[K] A))
    (hε : ε * AutomorphicForm.sigmaGL K L A σ ε = 1) :
    ∃ x : GL (Fin 2) (L ⊗[K] A), ε = x⁻¹ * AutomorphicForm.sigmaGL K L A σ x := by
  obtain ⟨ℓ, hℓ⟩ := hℓ

  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hm : ℓ - σ ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hℓ)
  let η : (L ⊗[K] A)ˣ := Units.mkOfMulEqOne ((ℓ - σ ℓ) ⊗ₜ[K] (1 : A)) ((ℓ - σ ℓ)⁻¹ ⊗ₜ[K] (1 : A))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hm, mul_one]; rfl)
  have hηval : (η : L ⊗[K] A) = (ℓ - σ ℓ) ⊗ₜ[K] (1 : A) := rfl
  have hη : s η = -η := by
    rw [hηval, hs, sigmaTensor_tmul, map_sub, hσ, ← neg_sub, TensorProduct.neg_tmul]
  set θ : L ⊗[K] A := ℓ ⊗ₜ[K] (1 : A) with hθ
  have hθη : θ - s θ = η := by
    rw [hηval, hθ, hs, sigmaTensor_tmul, TensorProduct.sub_tmul]

  set V := fixedSub K L A σ ε with hV
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  obtain ⟨v, hvV, hVle⟩ := exists_pair_of_finrank_le_two A V
    (finrank_fixedSub_le K L A σ h2 ε η hη)

  have hP : ∀ w, w + phi K L A σ ε w ∈ V := fun w => by
    rw [hV, mem_fixedSub, phi_add, phi_phi K L A σ hσ ε hε, add_comm]

  set S : Submodule (L ⊗[K] A) (Fin 2 → L ⊗[K] A) := Submodule.span (L ⊗[K] A) (Set.range v)
    with hS
  have hVS : ∀ u ∈ V, u ∈ S := fun u hu => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hVle hu)
    rw [← hc]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : c j • v j = (algebraMap A (L ⊗[K] A) (c j)) • v j := by
      funext i; simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hall : ∀ w : Fin 2 → L ⊗[K] A, w ∈ S := fun w => by
    have h1 : θ • w + phi K L A σ ε (θ • w) ∈ S := hVS _ (hP (θ • w))
    have h2' : s θ • (w + phi K L A σ ε w) ∈ S := Submodule.smul_mem _ _ (hVS _ (hP w))
    have hdiff : θ • w + phi K L A σ ε (θ • w) - s θ • (w + phi K L A σ ε w) = (η : L ⊗[K] A) • w := by
      rw [phi_smul, smul_add, ← hθη, sub_smul]
      abel
    have hηw : (η : L ⊗[K] A) • w ∈ S := hdiff ▸ Submodule.sub_mem _ h1 h2'
    have := Submodule.smul_mem S ((η⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) hηw
    rwa [smul_smul, Units.inv_mul, one_smul] at this

  set x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := Matrix.of fun i j => v j i with hx
  have hxmul : ∀ c : Fin 2 → L ⊗[K] A, x.mulVec c = ∑ j, c j • v j := fun c => by
    funext i
    simp [hx, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hsurj : Function.Surjective x.mulVec := fun w => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (L ⊗[K] A)).mp (hall w)
    exact ⟨c, (hxmul c).trans hc⟩
  obtain ⟨X, hX⟩ := Matrix.mulVec_surjective_iff_isUnit.mp hsurj

  have hfix : ε * AutomorphicForm.sigmaGL K L A σ X = X := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hj : phi K L A σ ε (v j) = v j := hvV j
    have hij := congrFun hj i
    simp only [phi, Matrix.mulVec, dotProduct] at hij
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [sigmaGL_apply, hX, hx, Matrix.of_apply]
    simpa [hX, hx] using hij
  refine ⟨X⁻¹, ?_⟩
  rw [inv_inv, map_inv, eq_mul_inv_iff_mul_eq, hfix]

end H90

section Galois

theorem sigma_involutive_and_ne_one (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∃ ℓ : L, σ ℓ ≠ ℓ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · by_contra h
    push Not at h
    have hσ1 : σ = 1 := AlgEquiv.ext h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, hσ1, one_zpow]
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

end Galois

section Aniso

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [CharZero A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "B" => L ⊗[K] A
local notation "MB" => Matrix (Fin 2) (Fin 2) (L ⊗[K] A)
local notation "GB" => GL (Fin 2) (L ⊗[K] A)

theorem exists_line_of_det_eq_zero {R : Type*} [Field R] (m : Matrix (Fin 2) (Fin 2) R) (hm : m.det = 0) (hm0 : m ≠ 0) :
    ∃ p : Fin 2 → R, p ≠ 0 ∧ (∃ e : Fin 2 → R, m.mulVec e = p) ∧ ∀ e : Fin 2 → R, ∃ μ : R, m.mulVec e = μ • p := by
  have hmv : ∀ e : Fin 2 → R, m.mulVec e = ![m 0 0 * e 0 + m 0 1 * e 1, m 1 0 * e 0 + m 1 1 * e 1] := by
    intro e; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [Matrix.det_fin_two] at hm
  by_cases hc0 : m 0 0 = 0 ∧ m 1 0 = 0
  ·
    obtain ⟨ha, hc⟩ := hc0
    have hcol1 : ¬ (m 0 1 = 0 ∧ m 1 1 = 0) := by
      rintro ⟨hb, hd⟩
      apply hm0
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    refine ⟨![m 0 1, m 1 1], ?_, ⟨![0, 1], ?_⟩, fun e => ⟨e 1, ?_⟩⟩
    · intro h
      apply hcol1
      have h0 := congrFun h 0; have h1 := congrFun h 1
      simp at h0 h1
      exact ⟨h0, h1⟩
    · rw [hmv]; funext i; fin_cases i <;> simp
    · rw [hmv]; funext i; fin_cases i <;> simp [ha, hc, mul_comm]
  ·
    refine ⟨![m 0 0, m 1 0], ?_, ⟨![1, 0], ?_⟩, fun e => ?_⟩
    · intro h
      apply hc0
      have h0 := congrFun h 0; have h1 := congrFun h 1
      simp at h0 h1
      exact ⟨h0, h1⟩
    · rw [hmv]; funext i; fin_cases i <;> simp
    · by_cases ha : m 0 0 = 0
      · have hc : m 1 0 ≠ 0 := fun hc => hc0 ⟨ha, hc⟩
        have hb : m 0 1 = 0 := by
          have : m 0 1 * m 1 0 = 0 := by rw [ha, zero_mul] at hm; linear_combination -hm
          exact (mul_eq_zero.1 this).resolve_right hc
        refine ⟨e 0 + m 1 1 / m 1 0 * e 1, ?_⟩
        rw [hmv]; funext i; fin_cases i
        · simp [ha, hb]
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Pi.smul_apply,
            smul_eq_mul]
          field_simp
          try ring
      · refine ⟨e 0 + m 0 1 / m 0 0 * e 1, ?_⟩
        have hd : m 1 1 = m 1 0 * m 0 1 / m 0 0 := by field_simp; linear_combination hm
        rw [hmv]; funext i; fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
          field_simp
          try ring
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Pi.smul_apply,
            smul_eq_mul]
          rw [hd]
          field_simp
          try ring

theorem isSigmaConjugate_scalar_of_singular (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
    (hℓ : ∃ ℓ : L, σ ℓ ≠ ℓ) (hB : IsField B) (c : Aˣ) (δ : GB)
    (hN : AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
    (m : MB) (hm : m * (δ : MB) = (δ : MB) * m.map (AutomorphicForm.sigmaTensor K L A σ)) (hm0 : m ≠ 0)
    (hdet : m.det = 0) :
    ∃ z : Bˣ, AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  letI : Field B := hB.toField
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hss : ∀ b : B, s (s b) = b := sigmaTensor_sigmaTensor K L A σ hσ

  obtain ⟨p, hp0, ⟨e₀, he₀⟩, hline⟩ := exists_line_of_det_eq_zero m hdet hm0

  have hΦp : ∃ lam : B, phi K L A σ δ p = lam • p := by
    obtain ⟨μ, hμ⟩ := hline ((δ : MB).mulVec fun i => s (e₀ i))
    refine ⟨μ, ?_⟩
    rw [← hμ]
    unfold phi
    rw [← he₀]
    have : (fun i => s (m.mulVec e₀ i)) = (m.map s).mulVec fun i => s (e₀ i) := by
      funext i; rw [RingHom.map_mulVec]; rfl
    rw [this, Matrix.mulVec_mulVec, ← hm, ← Matrix.mulVec_mulVec]
  obtain ⟨lam, hlam⟩ := hΦp

  have hNmat : (δ : MB) * (δ : MB).map s = Matrix.diagonal (fun _ => algebraMap A B (c : A)) := by
    have h := congrArg (fun g : GB => (g : MB)) hN
    simp only [normString_two K L A σ h2, Units.val_mul, coe_sigmaGL, toTensorGL_scalar] at h
    rw [h]
    ext i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rfl
  have hΦΦ : ∀ w : Fin 2 → B, phi K L A σ δ (phi K L A σ δ w) = algebraMap A B (c : A) • w := by
    intro w
    unfold phi
    have hin : (fun i => s ((δ : MB).mulVec (fun k => s (w k)) i)) = ((δ : MB).map s).mulVec w := by
      funext i
      rw [RingHom.map_mulVec]
      congr 1
      funext k
      exact hss (w k)
    rw [hin, Matrix.mulVec_mulVec, hNmat]
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  have hcc : s lam * lam = algebraMap A B (c : A) := by
    have h1 : phi K L A σ δ (phi K L A σ δ p) = (s lam * lam) • p := by
      rw [hlam, phi_smul, hlam, smul_smul]
    rw [hΦΦ] at h1

    by_contra hne
    apply hp0
    have h2' : (algebraMap A B (c : A) - s lam * lam) • p = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2').resolve_left (sub_ne_zero.2 (Ne.symm hne))

  have hlam0 : lam ≠ 0 := by
    intro h0
    have hc0 : algebraMap A B (c : A) = 0 := by rw [← hcc, h0, mul_zero]
    exact (Units.map (algebraMap A B).toMonoidHom c).ne_zero hc0

  set lamU : Bˣ := Units.mk0 lam hlam0 with hlamU
  set SL : GB := Matrix.GeneralLinearGroup.scalar (Fin 2) lamU with hSL
  set SL' : GB := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (s : B →* B) lamU) with hSL'
  have hσSL : AutomorphicForm.sigmaGL K L A σ SL = SL' := by rw [hSL, sigmaGL_scalar]
  have hprod : SL' * SL = AutomorphicForm.normString K L A σ δ := by
    rw [hN, toTensorGL_scalar, hSL, hSL', ← map_mul]
    congr 1
    ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, hlamU, Units.val_mk0]
    exact hcc
  have hε : (SL⁻¹ * δ) * AutomorphicForm.sigmaGL K L A σ (SL⁻¹ * δ) = 1 := by
    rw [map_mul, map_inv, hσSL]
    calc SL⁻¹ * δ * (SL'⁻¹ * AutomorphicForm.sigmaGL K L A σ δ)
        = SL⁻¹ * (δ * SL'⁻¹) * AutomorphicForm.sigmaGL K L A σ δ := by group
      _ = SL⁻¹ * (SL'⁻¹ * δ) * AutomorphicForm.sigmaGL K L A σ δ := by
          rw [show δ * SL'⁻¹ = SL'⁻¹ * δ from by
            rw [hSL', ← map_inv]; exact (scalar_mul_comm K L A _ δ).symm]
      _ = (SL' * SL)⁻¹ * (δ * AutomorphicForm.sigmaGL K L A σ δ) := by group
      _ = 1 := by rw [hprod, normString_two K L A σ h2, inv_mul_cancel]
  obtain ⟨x, hx⟩ := hilbert90 K L A σ h2 hσ hℓ (SL⁻¹ * δ) hε

  refine ⟨lamU, x⁻¹, ?_⟩
  have hδ' : δ = SL * (x⁻¹ * AutomorphicForm.sigmaGL K L A σ x) := by rw [← hx]; group
  rw [inv_inv, map_inv, hδ', ← hSL]
  calc SL = (x * SL * x⁻¹) * (AutomorphicForm.sigmaGL K L A σ x * (AutomorphicForm.sigmaGL K L A σ x)⁻¹) := by
        rw [conj_scalar, mul_inv_cancel, mul_one]
    _ = x * (SL * (x⁻¹ * AutomorphicForm.sigmaGL K L A σ x)) * (AutomorphicForm.sigmaGL K L A σ x)⁻¹ := by group

end Aniso

section Split

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem map_smul_ringHom {R : Type*} [CommSemiring R] (f : R →+* R) (r : R) (M : Matrix (Fin 2) (Fin 2) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp [Matrix.smul_apply]

theorem isSigmaConjugate_scalar_of_idempotent (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
    (e : L ⊗[K] A) (he : IsIdempotentElem e) (hes : e * AutomorphicForm.sigmaTensor K L A σ e = 0)
    (hsum : e + AutomorphicForm.sigmaTensor K L A σ e = 1) (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    ∃ z : (L ⊗[K] A)ˣ, AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hss : ∀ b : L ⊗[K] A, s (s b) = b := sigmaTensor_sigmaTensor K L A σ hσ
  set f : L ⊗[K] A := s e with hf
  have hsf : s f = e := hss e
  have hee : e * e = e := he.eq
  have hef : e * f = 0 := hes
  have hfe : f * e = 0 := by rw [mul_comm]; exact hes
  have hff : f * f = f := by have := congrArg s he.eq; rwa [map_mul] at this
  set c' : L ⊗[K] A := algebraMap A (L ⊗[K] A) (c : A) with hc'
  have hsc' : s c' = c' := sigmaTensor_one_tmul K L A σ (c : A)
  set D : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hD
  set Di : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hDi
  have hDDi : D * Di = 1 := by rw [hD, hDi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : Di * D = 1 := by rw [hD, hDi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmap1 : (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map s = 1 := Matrix.map_one _ (map_zero s) (map_one s)
  have hsDsDi : D.map s * Di.map s = 1 := by rw [← Matrix.map_mul, hDDi, hmap1]
  have hsDisD : Di.map s * D.map s = 1 := by rw [← Matrix.map_mul, hDiD, hmap1]
  have hmapmap : ∀ M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A), (M.map s).map s = M := fun M => by ext i j; exact hss _

  have hC : ((AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : GL (Fin 2) (L ⊗[K] A)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = c' • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    rw [toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; rfl
    · rw [mul_zero]; exact TensorProduct.tmul_zero _ _
  have hDsD : D * D.map s = c' • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have h := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hN
    simp only [normString_two K L A σ h2, Units.val_mul, coe_sigmaGL] at h
    rw [← hC]; exact h
  have hsDD : D.map s * D = c' • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => M.map s) hDsD
    simp only [Matrix.map_mul, hmapmap, map_smul_ringHom, hsc', hmap1] at this
    exact this

  have key : ∀ P Q : Matrix (Fin 2) (Fin 2) (L ⊗[K] A), P * Q = 1 →
      (e • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + f • P) * (e • 1 + f • Q) = 1 := by
    intro P Q hPQ
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, one_mul, mul_one, hPQ, hee, hef,
      hfe, hff, zero_smul, add_zero, zero_add]
    rw [← add_smul, hsum, one_smul]
  set X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := e • 1 + f • Di.map s with hX
  set X' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := e • 1 + f • D.map s with hX'
  have hXX' : X * X' = 1 := key _ _ hsDisD
  have hX'X : X' * X = 1 := by rw [hX', hX]; exact key _ _ hsDsDi
  let x : GL (Fin 2) (L ⊗[K] A) := ⟨X, X', hXX', hX'X⟩
  have hsX : X.map s = f • 1 + e • Di := by
    rw [hX]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul,
      hsf, hss]
    congr 1
    split_ifs <;> simp [hf]

  obtain ⟨ci, hci⟩ : ∃ ci : L ⊗[K] A, c' * ci = 1 := ⟨algebraMap A _ ((c⁻¹ : Aˣ) : A), by
    rw [hc', ← map_mul, Units.mul_inv, map_one]⟩
  have hz : (e + f * c') * (e + f * ci) = 1 := by
    calc (e + f * c') * (e + f * ci) = e * e + (e * f) * (ci + c') + (f * f) * (c' * ci) := by ring
      _ = e + f := by rw [hee, hef, hff, hci]; ring
      _ = 1 := hsum
  let z : (L ⊗[K] A)ˣ := ⟨e + f * c', e + f * ci, hz, by rw [mul_comm]; exact hz⟩
  refine ⟨z, x, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_sigmaGL]
  change Matrix.diagonal (fun _ => (z : L ⊗[K] A)) = X' * D * X.map s
  rw [hsX, hX']

  have hval : (e • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + f • D.map s) * D * (f • 1 + e • Di) =
      (e + f * c') • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have h1 : f * c' * e = 0 := by rw [mul_right_comm, hfe, zero_mul]
    have h2' : f * c' * f = f * c' := by rw [mul_right_comm, hff]
    have hstep : (e • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + f • D.map s) * D = e • D + (f * c') • 1 := by
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hsDD, smul_smul]
    rw [hstep]
    have h1' : e * (f * c') = 0 := by rw [← mul_assoc, hef, zero_mul]
    have h2'' : f * (f * c') = f * c' := by rw [← mul_assoc, hff]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hDDi, hee, hef,
      hfe, h1, h1', h2', h2'', zero_smul, zero_add, add_zero]
    rw [← add_smul, add_comm]
  rw [hval]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

end Split

section Card

theorem charZero_adicCompletion' (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

theorem exists_isSigmaConjugate_scalar_of_not_isField
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
    (hF : ¬ IsField (L ⊗[K] v.adicCompletion K)) :
    ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  haveI := charZero_adicCompletion' K v
  obtain ⟨hσσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  have hσ1 : σ ≠ 1 := by obtain ⟨ℓ, hℓ⟩ := hℓ; intro h; exact hℓ (by rw [h]; rfl)
  have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
  rcases AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion K L hprime σ hσ1 v with
    ⟨e, he, horth, hsum⟩ | hfield
  · have hes : e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e = 0 := by
      have := horth 1 one_pos (by rw [h2]; norm_num)
      rwa [Function.iterate_one] at this
    have hsum' : e + AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e = 1 := by
      rw [h2] at hsum; simpa [Finset.sum_range_succ] using hsum
    exact isSigmaConjugate_scalar_of_idempotent K L (v.adicCompletion K) σ h2 hσσ e he hes hsum' c δ hN
  · exact absurd hfield hF

theorem charZero_adicCompletion (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

theorem normString_eq_of_isNormOf_scalar
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) (c : Aˣ)
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ) :
    AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  obtain ⟨y, hy⟩ := hδ
  unfold AutomorphicForm.IsNormConjugator at hy
  rw [toTensorGL_scalar] at hy ⊢
  calc AutomorphicForm.normString K L A σ δ
      = y * Matrix.GeneralLinearGroup.scalar (Fin 2) _ * y⁻¹ := by rw [hy]; group
    _ = _ := conj_scalar K L A _ y

private theorem _root_.DivAlg.card
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hm : m * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).mapMatrix m)
    (hm0 : m ≠ 0) :
    IsUnit m := by
  haveI := charZero_adicCompletion K v
  obtain ⟨hσσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  have hN := normString_eq_of_isNormOf_scalar K L (v.adicCompletion K) σ δ c hδ
  by_cases hF : IsField (L ⊗[K] v.adicCompletion K)
  · by_contra hu
    letI : Field (L ⊗[K] v.adicCompletion K) := hF.toField
    have hdet : m.det = 0 := by
      by_contra hd
      exact hu ((Matrix.isUnit_iff_isUnit_det m).2 (isUnit_iff_ne_zero.2 hd))
    obtain ⟨z, hz⟩ := isSigmaConjugate_scalar_of_singular K L (v.adicCompletion K) σ h2 hσσ hℓ hF c δ hN m hm hm0 hdet
    exact hδq z hz
  · obtain ⟨z, hz⟩ := exists_isSigmaConjugate_scalar_of_not_isField K L h2 σ hgen v c δ hN hF
    exact absurd hz (hδq z)

p2m_export "DivAlg" "card"
end Card

end DivAlg

namespace Matrix
p2m_export "Matrix" "diagonal_apply mulVec_surjective_iff_isUnit ext empty_val' add sub_apply map_apply cons_val_zero zero cons_val' map_smul' one_apply_ne cons_val_one scalar one_mulVec trace_mul_cycle isUnit_iff_isUnit_det GeneralLinearGroup.scalar det_fin_two GeneralLinearGroup.val_scalar_apply scalar_commute det_fin_two_of mulVec_mulVec det_mul of_apply GeneralLinearGroup mulVec_diagonal ext_iff one_apply smul_apply det one_zpow GeneralLinearGroup.mkOfDetNeZero diagonal add_apply comp_apply of smul_mul sum_apply map GeneralLinearGroup.ext scalar_apply cons_val_fin_one GeneralLinearGroup.map_apply one mulVec_add mul_apply head_cons trace trace_fin_two_of mulVec_smul trace_fin_two mulVec"
namespace Disc2
p2m_open "Matrix"

theorem mul_shift_eq_zero {R : Type*} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (L₁ L₂ : R)
    (hsum : L₁ + L₂ = m.trace) (hmul : L₁ * L₂ = m.det) :
    (m - L₁ • (1 : Matrix (Fin 2) (Fin 2) R)) * (m - L₂ • (1 : Matrix (Fin 2) (Fin 2) R)) = 0 := by
  rw [Matrix.trace_fin_two] at hsum
  rw [Matrix.det_fin_two] at hmul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination (-(m 0 0)) * hsum + hmul
  · linear_combination (-(m 0 1)) * hsum
  · linear_combination (-(m 1 0)) * hsum
  · linear_combination (-(m 1 1)) * hsum + hmul

variable {S R : Type*} [Field S] [CommRing R] [Algebra S R]

theorem not_isSquare_disc (h2 : (2 : S) ≠ 0) (hinj : Function.Injective (algebraMap S R))
    (m : Matrix (Fin 2) (Fin 2) R) (t d : S) (ht : m.trace = algebraMap S R t) (hd : m.det = algebraMap S R d)
    (hunit : ∀ x : S, IsUnit (m - algebraMap S R x • (1 : Matrix (Fin 2) (Fin 2) R))) :
    ¬ IsSquare (t ^ 2 - 4 * d) := by
  haveI : Nontrivial R := hinj.nontrivial
  rintro ⟨q, hq⟩
  have h4 : (4 : S) ≠ 0 := by
    have h : (4 : S) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have hsumS : (t + q) / 2 + (t - q) / 2 = t := by
    field_simp
    ring
  have hmulS : (t + q) / 2 * ((t - q) / 2) = d := by
    field_simp
    linear_combination hq
  have hsum : algebraMap S R ((t + q) / 2) + algebraMap S R ((t - q) / 2) = m.trace := by
    rw [← map_add, hsumS, ht]
  have hmul : algebraMap S R ((t + q) / 2) * algebraMap S R ((t - q) / 2) = m.det := by
    rw [← map_mul, hmulS, hd]
  have hu := (hunit ((t + q) / 2)).mul (hunit ((t - q) / 2))
  rw [mul_shift_eq_zero m _ _ hsum hmul] at hu
  exact not_isUnit_zero hu

theorem disc_ne_zero (h2 : (2 : S) ≠ 0) (hinj : Function.Injective (algebraMap S R))
    (m : Matrix (Fin 2) (Fin 2) R) (t d : S) (ht : m.trace = algebraMap S R t) (hd : m.det = algebraMap S R d)
    (hunit : ∀ x : S, IsUnit (m - algebraMap S R x • (1 : Matrix (Fin 2) (Fin 2) R))) :
    t ^ 2 - 4 * d ≠ 0 := fun h =>
  not_isSquare_disc h2 hinj m t d ht hd hunit ⟨0, by rw [h, mul_zero]⟩

theorem disc_ne_zero_and_not_isSquare (h2 : (2 : S) ≠ 0) (hinj : Function.Injective (algebraMap S R))
    (m : Matrix (Fin 2) (Fin 2) R) (t d : S) (ht : m.trace = algebraMap S R t) (hd : m.det = algebraMap S R d)
    (hunit : ∀ x : S, IsUnit (m - algebraMap S R x • (1 : Matrix (Fin 2) (Fin 2) R))) :
    t ^ 2 - 4 * d ≠ 0 ∧ ¬ IsSquare (t ^ 2 - 4 * d) :=
  ⟨disc_ne_zero h2 hinj m t d ht hd hunit, not_isSquare_disc h2 hinj m t d ht hd hunit⟩

end Matrix.Disc2

namespace MPartner

section Fix

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

private theorem _root_.MPartner.sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

p2m_export "MPartner" "sigmaTensor_tmul"

theorem sigma_facts (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∀ l : L, ∃ k : K, l + σ l = algebraMap K L k := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, fun l => ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · set m := l + σ l with hm
    have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hσσ : σ (σ l) = l := by
      have := AlgEquiv.congr_fun hpow l
      rwa [pow_two, AlgEquiv.mul_apply] at this
    have hσm : σ m = m := by rw [hm, map_add, hσσ, add_comm]
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) m :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, hσm])
    have hfix : ∀ τ : L ≃ₐ[K] L, τ m = m := fun τ => by
      have := hle (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have hmem : m ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun τ _ => hfix τ
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩

theorem exists_add_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    ∃ r : A, e + AutomorphicForm.sigmaTensor K L A σ e = algebraMap A (L ⊗[K] A) r := by
  obtain ⟨-, htr⟩ := sigma_facts K L σ h2 hgen
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := htr l
      refine ⟨k • a, ?_⟩
      rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, hk, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      change (1 : L) ⊗ₜ[K] (k • a) = (k • a) • ((1 : L) ⊗ₜ[K] (1 : A))
      rw [TensorProduct.RightActions.smul_def]
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      obtain ⟨r₁, h₁⟩ := hx
      obtain ⟨r₂, h₂⟩ := hy
      refine ⟨r₁ + r₂, ?_⟩
      rw [map_add, map_add, ← h₁, ← h₂]
      abel

theorem exists_eq_algebraMap_of_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A}
    (he : AutomorphicForm.sigmaTensor K L A σ e = e) :
    ∃ r : A, e = algebraMap A (L ⊗[K] A) r := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨r, hr⟩ := exists_add_sigmaTensor_eq K L A σ h2 hgen e
  rw [he] at hr
  refine ⟨2⁻¹ * r, ?_⟩
  rw [map_mul, ← hr]
  have h2A : algebraMap A (L ⊗[K] A) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap A (L ⊗[K] A)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc e = (algebraMap A (L ⊗[K] A) 2⁻¹ * 2) * e := by rw [h2A, one_mul]
    _ = algebraMap A (L ⊗[K] A) 2⁻¹ * (e + e) := by rw [mul_assoc, two_mul]

end Fix

section Tele

variable (K L : Type) [Field K] [Field L] [Algebra K L] (F : Type) [CommRing F] [Algebra K F]
variable (σ : L ≃ₐ[K] L)

local notation "E" => L ⊗[K] F
local notation "GE" => GL (Fin 2) (L ⊗[K] F)
local notation "ME" => Matrix (Fin 2) (Fin 2) (L ⊗[K] F)

noncomputable def pns (δ : GE) (k : ℕ) : GE := ((List.range k).map fun i => (⇑(AutomorphicForm.sigmaGL K L F σ))^[i] δ).prod

theorem pns_zero (δ : GE) : pns K L F σ δ 0 = 1 := by simp [pns]

theorem pns_succ (δ : GE) (k : ℕ) :
    pns K L F σ δ (k + 1) = pns K L F σ δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by
  simp [pns, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pns (δ : GE) : AutomorphicForm.normString K L F σ δ = pns K L F σ δ (Module.finrank K L) := rfl

theorem mem_twistedCentralizer_iff (δ t : GE) :
    t ∈ AutomorphicForm.twistedCentralizer K L F σ δ ↔ t * δ = δ * AutomorphicForm.sigmaGL K L F σ t := by
  show t * δ * (AutomorphicForm.sigmaGL K L F σ t)⁻¹ = δ ↔ _
  rw [mul_inv_eq_iff_eq_mul]

theorem mul_pns_eq (δ t : GE) (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (k : ℕ) :
    t * pns K L F σ δ k = pns K L F σ δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t := by
  have htδ : t * δ = δ * AutomorphicForm.sigmaGL K L F σ t := (mem_twistedCentralizer_iff K L F σ δ t).mp ht
  induction k with
  | zero => simp [pns_zero]
  | succ k ih =>
    have hk : (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ =
        (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k + 1] t := by
      rw [← iterate_map_mul, htδ, iterate_map_mul, ← Function.iterate_succ_apply]
    rw [pns_succ, ← mul_assoc, ih, mul_assoc, hk, ← mul_assoc]

theorem pns_mul (δ t : GE) (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (k : ℕ) :
    pns K L F σ (t * δ) k = t ^ k * pns K L F σ δ k := by
  induction k with
  | zero => simp [pns_zero]
  | succ k ih =>
    rw [pns_succ, ih, iterate_map_mul, pow_succ, pns_succ]
    have := mul_pns_eq K L F σ δ t ht k

    calc t ^ k * pns K L F σ δ k * ((⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ)
        = t ^ k * (pns K L F σ δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t) * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by
          group
      _ = t ^ k * (t * pns K L F σ δ k) * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by rw [this]
      _ = t ^ k * t * (pns K L F σ δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ) := by group

theorem normString_mul_of_mem_twistedCentralizer (δ t : GE)
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) :
    AutomorphicForm.normString K L F σ (t * δ) = t ^ Module.finrank K L * AutomorphicForm.normString K L F σ δ := by
  rw [normString_eq_pns, normString_eq_pns, pns_mul K L F σ δ t ht]

end Tele

section TwoByTwo

variable {R : Type*} [CommRing R]

theorem ch2 (m : Matrix (Fin 2) (Fin 2) R) : m * m = m.trace • m - m.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem det_smul_one_add_smul (m : Matrix (Fin 2) (Fin 2) R) (x y : R) :
    (x • (1 : Matrix (Fin 2) (Fin 2) R) + y • m).det = x ^ 2 + x * y * m.trace + y ^ 2 * m.det := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  ring

theorem trace_smul_one_add_smul (m : Matrix (Fin 2) (Fin 2) R) (x y : R) :
    (x • (1 : Matrix (Fin 2) (Fin 2) R) + y • m).trace = 2 * x + y * m.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  ring

theorem eq_smul_one_of_entries (Z : Matrix (Fin 2) (Fin 2) R) (h01 : Z 0 1 = 0) (h10 : Z 1 0 = 0) (hdiag : Z 0 0 = Z 1 1) :
    Z = Z 0 0 • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.one_apply, h01, h10, hdiag]

end TwoByTwo

section Companion

variable {R : Type*} [CommRing R]

theorem exists_units_mul_eq_mul_companion (hfield : ∀ x : R, x ≠ 0 → IsUnit x)
    (Z : Matrix (Fin 2) (Fin 2) R) (hZ : ∀ e : R, Z ≠ e • (1 : Matrix (Fin 2) (Fin 2) R)) :
    ∃ y : GL (Fin 2) R, Z * (y : Matrix (Fin 2) (Fin 2) R) = (y : Matrix (Fin 2) (Fin 2) R) * !![0, -Z.det; 1, Z.trace] := by

  obtain ⟨e, he⟩ : ∃ e : Fin 2 → R, e 0 * (Z 1 0 * e 0 + Z 1 1 * e 1) - (Z 0 0 * e 0 + Z 0 1 * e 1) * e 1 ≠ 0 := by
    by_cases h10 : Z 1 0 = 0
    · by_cases h01 : Z 0 1 = 0
      · have hdiag : Z 0 0 ≠ Z 1 1 := fun h => hZ (Z 0 0) (eq_smul_one_of_entries Z h01 h10 h)
        refine ⟨![1, 1], ?_⟩
        simp [h10, h01]
        exact sub_ne_zero.2 (Ne.symm hdiag)
      · refine ⟨![0, 1], ?_⟩
        simpa [h10] using h01
    · refine ⟨![1, 0], ?_⟩
      simpa using h10

  set f : Fin 2 → R := Z.mulVec e with hf
  have hf0 : f 0 = Z 0 0 * e 0 + Z 0 1 * e 1 := by simp [hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hf1 : f 1 = Z 1 0 * e 0 + Z 1 1 * e 1 := by simp [hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set Y : Matrix (Fin 2) (Fin 2) R := !![e 0, f 0; e 1, f 1] with hY
  have hdet : Y.det ≠ 0 := by
    rw [hY, Matrix.det_fin_two_of, hf0, hf1]; exact he
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 (hfield _ hdet)
  refine ⟨hYu.unit, ?_⟩
  rw [hYu.unit_spec]

  have hCH := ch2 Z
  have h00 := congrFun (congrFun hCH 0) 0
  have h01 := congrFun (congrFun hCH 0) 1
  have h10 := congrFun (congrFun hCH 1) 0
  have h11 := congrFun (congrFun hCH 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h00 h01 h10 h11
  simp only [Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, mul_one, mul_zero] at h00 h01 h10 h11
  ext i j
  rw [hY]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hf0, hf1]
  · linear_combination e 0 * h00 + e 1 * h01
  · linear_combination e 0 * h10 + e 1 * h11

end Companion

section CompanionTensor

variable (K L : Type) [Field K] [Field L] [Algebra K L] (F : Type) [CommRing F] [Algebra K F]

theorem coe_toTensorGL_companion (g : GL (Fin 2) F) (Δ T : F)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = !![0, -Δ; 1, T]) :
    ((AutomorphicForm.toTensorGL K L F g : GL (Fin 2) (L ⊗[K] F)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) =
      !![0, -(algebraMap F (L ⊗[K] F) Δ); 1, algebraMap F (L ⊗[K] F) T] := by
  ext i j
  rw [DivAlg.toTensorGL_apply, hg]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact TensorProduct.tmul_zero _ _
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← map_neg]; rfl
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rfl

theorem isNormOf_of_mul_eq (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) F) (δ' y : GL (Fin 2) (L ⊗[K] F))
    (h : AutomorphicForm.normString K L F σ δ' * y = y * AutomorphicForm.toTensorGL K L F γ) :
    AutomorphicForm.IsNormOf K L F σ γ δ' := by
  refine ⟨y, ?_⟩
  unfold AutomorphicForm.IsNormConjugator
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

end CompanionTensor

section Main

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (F : Type) [Field F] [Algebra K F]
variable (σ : L ≃ₐ[K] L)

local notation "E" => L ⊗[K] F
local notation "GE" => GL (Fin 2) (L ⊗[K] F)
local notation "GF" => GL (Fin 2) F
local notation "ME" => Matrix (Fin 2) (Fin 2) (L ⊗[K] F)
local notation "MF" => Matrix (Fin 2) (Fin 2) F

theorem exists_nonscalar_mem_commutant (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (c : Fˣ) (δ : GE)
    (hN : AutomorphicForm.normString K L F σ δ = AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    ∃ m : ME, m * (δ : ME) = (δ : ME) * (AutomorphicForm.sigmaTensor K L F σ).mapMatrix m ∧
      ∀ e : E, m ≠ e • (1 : ME) := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨hσσ, ⟨ℓ, hℓ⟩⟩ := DivAlg.sigma_involutive_and_ne_one K L h2 σ hgen
  set s := AutomorphicForm.sigmaTensor K L F σ with hs
  have hss : ∀ b : E, s (s b) = b := DivAlg.sigmaTensor_sigmaTensor K L F σ hσσ

  set θ : E := (ℓ - σ ℓ) ⊗ₜ[K] (1 : F) with hθ
  set θ' : E := (ℓ - σ ℓ)⁻¹ ⊗ₜ[K] (1 : F) with hθ'
  have hθ'θ : θ' * θ = 1 := by
    rw [hθ, hθ', Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hℓ)), mul_one]; rfl
  have hsθ : s θ = -θ := by
    rw [hθ, hs, DivAlg.sigmaTensor_tmul, map_sub, hσσ, ← TensorProduct.neg_tmul, neg_sub]
  have h2E : (2 : E) ≠ 0 := by
    rw [show (2 : E) = algebraMap F E 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ (algebraMap F E).injective).2 two_ne_zero

  set c' : E := algebraMap F E (c : F) with hc'
  set c'' : E := algebraMap F E ((c⁻¹ : Fˣ) : F) with hc''
  have hcc : c' * c'' = 1 := by rw [hc', hc'', ← map_mul, Units.mul_inv, map_one]
  set D : ME := (δ : ME) with hD
  set Di : ME := ((δ⁻¹ : GE) : ME) with hDi
  have hDDi : D * Di = 1 := by rw [hD, hDi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : Di * D = 1 := by rw [hD, hDi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmap1 : (1 : ME).map s = 1 := Matrix.map_one _ (map_zero s) (map_one s)
  have hsDsDi : D.map s * Di.map s = 1 := by rw [← Matrix.map_mul, hDDi, hmap1]
  have hmapmap : ∀ M : ME, (M.map s).map s = M := fun M => by ext i j; exact hss _
  have hC : ((AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : GE) : ME) = c' • (1 : ME) := by
    ext i j
    rw [DivAlg.toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; rfl
    · rw [mul_zero]; exact TensorProduct.tmul_zero _ _
  have hDsD : D * D.map s = c' • (1 : ME) := by
    have h := congrArg (fun g : GE => (g : ME)) hN
    simp only [DivAlg.normString_two K L F σ h2, Units.val_mul, DivAlg.coe_sigmaGL] at h
    rw [← hC]; exact h
  have hsD : D.map s = c' • Di := by
    calc D.map s = Di * (D * D.map s) := by rw [← mul_assoc, hDiD, one_mul]
      _ = c' • Di := by rw [hDsD, Matrix.mul_smul, mul_one]
  have hsDi : Di.map s = c'' • D := by
    have h1 : c' • (Di * Di.map s) = 1 := by rw [← Matrix.smul_mul, ← hsD, hsDsDi]
    calc Di.map s = D * (Di * Di.map s) := by rw [← mul_assoc, hDDi, one_mul]
      _ = D * (c'' • (c' • (Di * Di.map s))) := by rw [smul_smul, mul_comm c'' c', hcc, one_smul]
      _ = c'' • D := by rw [h1, Matrix.mul_smul, mul_one]

  have memA : ∀ X : ME, (X + D * X.map s * Di) * D = D * s.mapMatrix (X + D * X.map s * Di) := by
    intro X
    have hcc' : c'' * c' = 1 := by rw [mul_comm]; exact hcc
    rw [RingHom.mapMatrix_apply, Matrix.map_add _ (map_add s), Matrix.map_mul, Matrix.map_mul, hmapmap, hsD, hsDi]
    rw [add_mul, mul_add, mul_assoc (D * X.map s) Di D, hDiD, mul_one, add_comm (X * D)]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc, hcc', one_smul]
    rw [← mul_assoc, ← mul_assoc, hDDi, one_mul]

  set X : ME := Matrix.of (fun i j : Fin 2 => if i = 0 ∧ j = 1 then (1 : E) else 0) with hX
  have hXns : ∀ e : E, (2 * θ) • X ≠ e • (1 : ME) := by
    intro e h
    have h01 := congrFun (congrFun h 0) 1
    have hX01 : X 0 1 = 1 := by rw [hX, Matrix.of_apply]; simp
    rw [Matrix.smul_apply, Matrix.smul_apply, hX01, Matrix.one_apply_ne (by decide), smul_eq_mul, smul_eq_mul, mul_one,
      mul_zero] at h01

    apply h2E
    calc (2 : E) = θ' * θ * 2 := by rw [hθ'θ, one_mul]
      _ = θ' * (2 * θ) := by ring
      _ = 0 := by rw [h01, mul_zero]
  by_cases hP : ∃ e : E, X + D * X.map s * Di = e • (1 : ME)
  · obtain ⟨e₁, he₁⟩ := hP
    refine ⟨θ • X + D * (θ • X).map s * Di, memA _, fun e₂ he₂ => ?_⟩
    have hsθX : (θ • X).map s = (-θ) • X.map s := by
      ext i j; simp [Matrix.smul_apply, map_mul, hsθ]
    rw [hsθX] at he₂

    apply hXns (θ * e₁ + e₂)
    have hrw : D * ((-θ) • X.map s) * Di = -(θ • (D * X.map s * Di)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, neg_smul]
    calc (2 * θ) • X = θ • (X + D * X.map s * Di) + (θ • X + D * ((-θ) • X.map s) * Di) := by
          rw [hrw, smul_add, two_mul, add_smul]; abel
      _ = (θ * e₁ + e₂) • (1 : ME) := by rw [he₁, he₂, smul_smul, add_smul]
  · push Not at hP
    exact ⟨X + D * X.map s * Di, memA X, hP⟩

theorem main (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (c : Fˣ) (δ : GE)
    (hδ : AutomorphicForm.IsNormOf K L F σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hF : IsField E)
    (hdiv : ∀ m : ME, m * (δ : ME) = (δ : ME) * (AutomorphicForm.sigmaTensor K L F σ).mapMatrix m → m ≠ 0 → IsUnit m) :
    ∃ u₀ ∈ AutomorphicForm.twistedCentralizer K L F σ δ, ∃ γ₀ : GF,
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      ¬ IsSquare (Matrix.trace (γ₀ : MF) ^ 2 - 4 * Matrix.det (γ₀ : MF)) ∧
      AutomorphicForm.IsNormOf K L F σ γ₀ (u₀ * δ) := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Nontrivial E := hF.nontrivial
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  set s := AutomorphicForm.sigmaTensor K L F σ with hs
  obtain ⟨hσσ, -⟩ := DivAlg.sigma_involutive_and_ne_one K L h2 σ hgen
  have hN := DivAlg.normString_eq_of_isNormOf_scalar K L F σ δ c hδ
  obtain ⟨m, hmA, hmns⟩ := exists_nonscalar_mem_commutant K L F σ h2 hgen c δ hN
  set D : ME := (δ : ME) with hD
  set Di : ME := ((δ⁻¹ : GE) : ME) with hDi
  have hDDi : D * Di = 1 := by rw [hD, hDi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : Di * D = 1 := by rw [hD, hDi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsalg : ∀ x : F, s (algebraMap F E x) = algebraMap F E x := fun x => DivAlg.sigmaTensor_one_tmul K L F σ x
  have hsmul1 : ∀ x : F, (algebraMap F E x • (1 : ME)).map s = algebraMap F E x • (1 : ME) := by
    intro x; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs
    · exact hsalg x
    · exact map_zero s

  have hm_eq : m = D * m.map s * Di := by
    calc m = m * D * Di := by rw [mul_assoc, hDDi, mul_one]
      _ = D * m.map s * Di := by rw [hmA]; rfl
  have htrfix : s m.trace = m.trace := by
    have h1 : m.trace = (m.map s).trace := by
      conv_lhs => rw [hm_eq]
      rw [Matrix.trace_mul_cycle, hDiD, one_mul]
    have h1' : (m.map s).trace = s m.trace := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl
    rw [← h1', ← h1]
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).1 ⟨δ, rfl⟩
  have hdetfix : s m.det = m.det := by
    have h1 := congrArg Matrix.det hmA
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm m.det] at h1
    have h2' := hDunit.mul_left_cancel h1

    rw [← RingHom.map_det] at h2'
    exact h2'.symm
  obtain ⟨t, ht⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L F σ h2 hgen htrfix
  obtain ⟨d, hd⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L F σ h2 hgen hdetfix

  have hshiftA : ∀ x : F, (m - algebraMap F E x • (1 : ME)) * D = D * s.mapMatrix (m - algebraMap F E x • (1 : ME)) := by
    intro x
    rw [RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub s), hsmul1, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, ← RingHom.mapMatrix_apply, hmA]
  have hunit : ∀ x : F, IsUnit (m - algebraMap F E x • (1 : ME)) := fun x =>
    hdiv _ (hshiftA x) (fun h0 => hmns (algebraMap F E x) (sub_eq_zero.1 h0))
  obtain ⟨hdisc0, hdiscsq⟩ := Matrix.Disc2.disc_ne_zero_and_not_isSquare (S := F) (R := E) two_ne_zero hinj m t d ht hd hunit

  obtain ⟨α, hα⟩ : ∃ α : F, 2 * α + t ≠ 0 := by
    by_cases h0 : t = 0
    · exact ⟨1, by rw [h0, add_zero, mul_one]; exact two_ne_zero⟩
    · exact ⟨0, by rwa [mul_zero, zero_add]⟩
  set U : ME := algebraMap F E α • (1 : ME) + m with hU
  have hUA : U * D = D * s.mapMatrix U := by
    have := hshiftA (-α)
    rw [map_neg, neg_smul, sub_neg_eq_add, add_comm] at this
    exact this
  have hU0 : U ≠ 0 := by
    intro h0; apply hmns (algebraMap F E (-α))
    rw [hU] at h0
    rw [eq_neg_of_add_eq_zero_right h0, map_neg, neg_smul]
  have hUunit : IsUnit U := hdiv U hUA hU0
  obtain ⟨u₀, hu₀val⟩ : ∃ u : GE, (u : ME) = U := ⟨hUunit.unit, hUunit.unit_spec⟩
  have hu₀T : u₀ ∈ AutomorphicForm.twistedCentralizer K L F σ δ := by
    rw [mem_twistedCentralizer_iff, Units.ext_iff, Units.val_mul, Units.val_mul, DivAlg.coe_sigmaGL, hu₀val]
    rw [RingHom.mapMatrix_apply] at hUA
    exact hUA

  set a : F := α ^ 2 - d with ha
  set b : F := 2 * α + t with hb
  have hCH : m * m = m.trace • m - m.det • (1 : ME) := ch2 m
  have hUU : U * U = algebraMap F E a • (1 : ME) + algebraMap F E b • m := by
    rw [hU, add_mul, mul_add, mul_add, hCH, ht, hd, ha, hb, map_sub, map_add, map_mul, map_pow, map_ofNat]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    generalize algebraMap F E α = α' at *
    generalize algebraMap F E t = t' at *
    generalize algebraMap F E d = d' at *
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply, smul_eq_mul, Fin.isValue,
        Fin.zero_eta, Fin.mk_one, if_true, if_false, one_ne_zero, zero_ne_one, mul_one, mul_zero] <;> ring

  have hZ : AutomorphicForm.normString K L F σ (u₀ * δ) = u₀ ^ 2 * AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [normString_mul_of_mem_twistedCentralizer K L F σ δ u₀ hu₀T, h2, hN]

  have hC : ((AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : GE) : ME) =
      algebraMap F E (c : F) • (1 : ME) := by
    ext i j
    rw [DivAlg.toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; rfl
    · rw [mul_zero]; exact TensorProduct.tmul_zero _ _
  set A : F := (c : F) * a with hA
  set B : F := (c : F) * b with hB
  have hB0 : B ≠ 0 := mul_ne_zero c.ne_zero hα
  set ZM : ME := algebraMap F E A • (1 : ME) + algebraMap F E B • m with hZM
  have hZval : ((AutomorphicForm.normString K L F σ (u₀ * δ) : GE) : ME) = ZM := by
    rw [hZ, Units.val_mul, Units.val_pow_eq_pow_val, hu₀val, pow_two, hUU, hC, hZM, hA, hB, map_mul, map_mul,
      Matrix.mul_smul, mul_one, smul_add, smul_smul, smul_smul]
  have htrZ : ZM.trace = algebraMap F E (2 * A + B * t) := by
    rw [hZM, trace_smul_one_add_smul, ht]
    simp only [map_add, map_mul, map_ofNat]
  have hdetZ : ZM.det = algebraMap F E (A ^ 2 + A * B * t + B ^ 2 * d) := by
    rw [hZM, det_smul_one_add_smul, ht, hd]
    simp only [map_add, map_mul, map_pow]
  set T₀ : F := 2 * A + B * t with hT₀
  set Δ₀ : F := A ^ 2 + A * B * t + B ^ 2 * d with hΔ₀
  have hdisc : T₀ ^ 2 - 4 * Δ₀ = B ^ 2 * (t ^ 2 - 4 * d) := by rw [hT₀, hΔ₀]; ring
  have hΔ0 : Δ₀ ≠ 0 := by
    intro h0
    have hu : IsUnit ZM.det := by
      rw [← hZval]; exact (Matrix.isUnit_iff_isUnit_det _).1 ⟨_, rfl⟩
    rw [hdetZ, h0, map_zero] at hu
    exact not_isUnit_zero hu
  set γM : MF := !![0, -Δ₀; 1, T₀] with hγM
  have hγdet : γM.det = Δ₀ := by rw [hγM, Matrix.det_fin_two_of]; ring
  have hγtr : γM.trace = T₀ := by rw [hγM, Matrix.trace_fin_two_of]; ring
  obtain ⟨γ₀, hγ₀val⟩ : ∃ g : GF, (g : MF) = γM :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γM (by rw [hγdet]; exact hΔ0), rfl⟩
  refine ⟨u₀, hu₀T, γ₀, ?_, ?_, ?_⟩
  ·
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, hγ₀val, hγtr, hγdet, hdisc]
    exact mul_ne_zero (pow_ne_zero 2 hB0) hdisc0
  ·
    rw [hγ₀val, hγtr, hγdet, hdisc]
    rintro ⟨r, hr⟩
    apply hdiscsq
    refine ⟨r / B, ?_⟩
    field_simp
    linear_combination hr
  ·
    have hfield : ∀ x : E, x ≠ 0 → IsUnit x := fun x hx => by
      obtain ⟨x', hx'⟩ := hF.mul_inv_cancel hx
      exact IsUnit.of_mul_eq_one x' hx'
    have hZns : ∀ e : E, ZM ≠ e • (1 : ME) := by
      intro e he
      obtain ⟨uB, huB⟩ := hfield _ ((map_ne_zero_iff _ hinj).2 hB0)
      apply hmns (((uB⁻¹ : Eˣ) : E) * (e - algebraMap F E A))
      have h1 : algebraMap F E B • m = (e - algebraMap F E A) • (1 : ME) := by
        rw [sub_smul, ← he, hZM, add_sub_cancel_left]
      calc m = ((uB⁻¹ : Eˣ) : E) • (algebraMap F E B • m) := by rw [smul_smul, ← huB, Units.inv_mul, one_smul]
        _ = _ := by rw [h1, smul_smul]
    obtain ⟨y, hy⟩ := exists_units_mul_eq_mul_companion hfield ZM hZns
    have hγ₀M : (γ₀ : MF) = !![0, -Δ₀; 1, T₀] := by rw [hγ₀val, hγM]
    have hunits : AutomorphicForm.normString K L F σ (u₀ * δ) * y = y * AutomorphicForm.toTensorGL K L F γ₀ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hZval, hy, hdetZ, htrZ, coe_toTensorGL_companion K L F γ₀ Δ₀ T₀ hγ₀M]
    exact isNormOf_of_mul_eq K L F σ γ₀ (u₀ * δ) y hunits
end Main

section Kv

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

theorem mainKv (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ γ₀ : GL (Fin 2) (v.adicCompletion K),
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      ¬ IsSquare (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
          4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) := by
  have hN := DivAlg.normString_eq_of_isNormOf_scalar K L (v.adicCompletion K) σ δ c hδ
  have hF : IsField (L ⊗[K] v.adicCompletion K) := by
    by_contra hF
    obtain ⟨z, hz⟩ := DivAlg.exists_isSigmaConjugate_scalar_of_not_isField K L h2 σ hgen v c δ hN hF
    exact hδq z hz
  exact main K L (v.adicCompletion K) σ h2 hgen c δ hδ hF
    (fun m hm hm0 => DivAlg.card K L h2 σ hgen v c δ hδ hδq m hm hm0)

end Kv

end MPartner

end

open MeasureTheory NumberField IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ γ₀ : GL (Fin 2) (v.adicCompletion K),
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      ¬ IsSquare (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
          4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) :=
  MPartner.mainKv K L σ v h2 hgen c δ hδ hδq

end S_AutomorphicForm_exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
