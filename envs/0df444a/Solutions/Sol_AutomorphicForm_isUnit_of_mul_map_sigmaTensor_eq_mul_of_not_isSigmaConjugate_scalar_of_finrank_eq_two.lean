-- Prove2me | solution 1 for AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fdd68fbd-870f-5778-b0cb-0ca5c2d0c941

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mSigmaElliptic

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

section Fixed

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem exists_add_sigma_eq (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (l : L) : ∃ k : K, l + σ l = algebraMap K L k := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  obtain ⟨hσσ, -⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  set m := l + σ l with hm
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
    ∃ r : A, e + AutomorphicForm.sigmaTensor K L A σ e = (1 : L) ⊗ₜ[K] r := by
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := exists_add_sigma_eq K L σ h2 hgen l
      refine ⟨k • a, ?_⟩
      rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, hk, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨r₁, h₁⟩ := hx
      obtain ⟨r₂, h₂⟩ := hy
      refine ⟨r₁ + r₂, ?_⟩
      rw [map_add, TensorProduct.tmul_add, ← h₁, ← h₂]
      abel

theorem exists_eq_tmul_of_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A}
    (he : AutomorphicForm.sigmaTensor K L A σ e = e) :
    ∃ r : A, e = (1 : L) ⊗ₜ[K] r := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨r, hr⟩ := exists_add_sigmaTensor_eq K L A σ h2 hgen e
  rw [he] at hr
  refine ⟨2⁻¹ * r, ?_⟩
  have h2E : ((1 : L) ⊗ₜ[K] (2⁻¹ : A)) * 2 = 1 := by
    rw [show (2 : L ⊗[K] A) = (1 : L) ⊗ₜ[K] (2 : A) by
      rw [← map_ofNat (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) 2]; rfl,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ two_ne_zero]
    rfl
  calc e = ((1 : L) ⊗ₜ[K] (2⁻¹ : A)) * 2 * e := by rw [h2E, one_mul]
    _ = ((1 : L) ⊗ₜ[K] (2⁻¹ : A)) * (e + e) := by rw [mul_assoc, two_mul]
    _ = (1 : L) ⊗ₜ[K] (2⁻¹ * r) := by rw [hr, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [CharZero K] in

theorem isUnit_one_tmul_iff {r : A} : IsUnit ((1 : L) ⊗ₜ[K] r : L ⊗[K] A) ↔ r ≠ 0 := by
  constructor
  · rintro hu rfl
    rw [TensorProduct.tmul_zero] at hu
    exact not_isUnit_zero hu
  · intro hr
    exact (IsUnit.mk0 r hr).map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)

end Fixed

section Split

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem map_smul_sigma (a : L ⊗[K] A) (N : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    (a • N).map (AutomorphicForm.sigmaTensor K L A σ) =
      AutomorphicForm.sigmaTensor K L A σ a • N.map (AutomorphicForm.sigmaTensor K L A σ) := by
  ext i j
  simp [Matrix.map_apply]

theorem coe_scalar_eq_smul_one (u : (L ⊗[K] A)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = (u : L ⊗[K] A) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  ext i j
  rw [scalar_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem isSigmaConjugate_scalar_of_idempotent (δ : GL (Fin 2) (L ⊗[K] A)) (cE : (L ⊗[K] A)ˣ)
    (hN : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ) =
        (cE : L ⊗[K] A) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
    {ε : L ⊗[K] A} (hε : ε * ε = ε) (hsε : AutomorphicForm.sigmaTensor K L A σ ε = 1 - ε) :
    ∃ z : (L ⊗[K] A)ˣ,
      AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  set D : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hD
  set D' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hε1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have hε2 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  have hε3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, mul_one, hε2, sub_zero]

  set X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ε • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + (1 - ε) • D
    with hX
  set X' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ε • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + (1 - ε) • D'
    with hX'
  have hXX' : X * X' = 1 := by
    rw [hX, hX']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      Matrix.one_mul, Matrix.mul_one, hDD', hε, hε1, hε2, hε3, zero_smul, add_zero, zero_add]
    rw [← add_smul, add_sub_cancel, one_smul]
  have hX'X : X' * X = 1 := by
    rw [hX, hX']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      Matrix.one_mul, Matrix.mul_one, hD'D, hε, hε1, hε2, hε3, zero_smul, add_zero, zero_add]
    rw [← add_smul, add_sub_cancel, one_smul]
  let Xg : GL (Fin 2) (L ⊗[K] A) := ⟨X, X', hXX', hX'X⟩

  set w : L ⊗[K] A := ε * (cE : L ⊗[K] A) + (1 - ε) with hw
  set w' : L ⊗[K] A := ε * ((cE⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) + (1 - ε) with hw'
  have hww' : w * w' = 1 := by
    rw [hw, hw']
    have hc : (cE : L ⊗[K] A) * ((cE⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (ε * (cE : L ⊗[K] A) + (1 - ε)) * (ε * ((cE⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) + (1 - ε))
        = (ε * ε) * ((cE : L ⊗[K] A) * ((cE⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A)) +
            (ε * (1 - ε)) * (cE : L ⊗[K] A) + ((1 - ε) * ε) * ((cE⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) +
              (1 - ε) * (1 - ε) := by ring
      _ = 1 := by rw [hε, hc, hε1, hε2, hε3]; ring
  let wU : (L ⊗[K] A)ˣ := Units.mkOfMulEqOne w w' hww'

  have hsX : X.map s = (1 - ε) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) + ε • D.map s := by
    rw [hX, Matrix.map_add _ (map_add s), map_smul_sigma, map_smul_sigma, ← hs, hsε,
      Matrix.map_one _ (map_zero s) (map_one s), map_sub, map_one, hsε, sub_sub_cancel]
  have hkey : D * X.map s = X * (w • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) := by
    rw [hsX, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, hN, smul_smul, hX,
      Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, smul_smul, hw]
    have e1 : ε * (ε * (cE : L ⊗[K] A) + (1 - ε)) = ε * (cE : L ⊗[K] A) := by
      rw [mul_add, ← mul_assoc, hε, hε1, add_zero]
    have e2 : (1 - ε) * (ε * (cE : L ⊗[K] A) + (1 - ε)) = 1 - ε := by
      rw [mul_add, ← mul_assoc, hε2, zero_mul, zero_add, hε3]
    rw [e1, e2, add_comm]
  refine ⟨wU, Xg, ?_⟩

  have hGL : δ * AutomorphicForm.sigmaGL K L A σ Xg = Xg * Matrix.GeneralLinearGroup.scalar (Fin 2) wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_sigmaGL, coe_scalar_eq_smul_one]
    exact hkey
  rw [mul_assoc, hGL, inv_mul_cancel_left]

theorem exists_idempotent_of_not_isUnit (hσ : ∀ l : L, σ (σ l) = l)
    (hfix : ∀ e : L ⊗[K] A, AutomorphicForm.sigmaTensor K L A σ e = e → ∃ r : A, e = (1 : L) ⊗ₜ[K] r)
    (η : (L ⊗[K] A)ˣ) (hη : AutomorphicForm.sigmaTensor K L A σ η = -η)
    {e : L ⊗[K] A} (he0 : e ≠ 0) (heu : ¬ IsUnit e) :
    ∃ ε : L ⊗[K] A, ε * ε = ε ∧ AutomorphicForm.sigmaTensor K L A σ ε = 1 - ε := by
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hss : ∀ b, s (s b) = b := sigmaTensor_sigmaTensor K L A σ hσ

  have hn0 : e * s e = 0 := by
    have hf : s (e * s e) = e * s e := by rw [map_mul, hss, mul_comm]
    obtain ⟨r, hr⟩ := hfix _ hf
    by_contra hne
    have hr0 : r ≠ 0 := by rintro rfl; rw [TensorProduct.tmul_zero] at hr; exact hne hr
    have hu : IsUnit (e * s e) := by rw [hr]; exact (isUnit_one_tmul_iff K L A).mpr hr0
    exact heu (isUnit_of_mul_isUnit_left hu)

  have hfa : s (e + s e) = e + s e := by rw [map_add, hss, add_comm]
  obtain ⟨a, ha⟩ := hfix _ hfa
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, add_eq_zero_iff_eq_neg] at ha

    have hse : s e = -e := by rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero]; exact ha
    have hfηe : s ((η : L ⊗[K] A) * e) = (η : L ⊗[K] A) * e := by
      rw [map_mul, hη, hse, neg_mul_neg]
    obtain ⟨r, hr⟩ := hfix _ hfηe
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [TensorProduct.tmul_zero] at hr
      exact he0 ((Units.mul_right_eq_zero η).mp hr)
    have hu : IsUnit ((η : L ⊗[K] A) * e) := by rw [hr]; exact (isUnit_one_tmul_iff K L A).mpr hr0
    exact heu (isUnit_of_mul_isUnit_right hu)

  have he2 : e * e = ((1 : L) ⊗ₜ[K] a) * e := by
    have : e * (e + s e) = e * e := by rw [mul_add, hn0, add_zero]
    rw [← this, ha, mul_comm]
  refine ⟨((1 : L) ⊗ₜ[K] a⁻¹) * e, ?_, ?_⟩
  · calc (1 : L) ⊗ₜ[K] a⁻¹ * e * ((1 : L) ⊗ₜ[K] a⁻¹ * e)
        = (1 : L) ⊗ₜ[K] a⁻¹ * ((1 : L) ⊗ₜ[K] a⁻¹ * (e * e)) := by ring
      _ = (1 : L) ⊗ₜ[K] a⁻¹ * ((1 : L) ⊗ₜ[K] a⁻¹ * ((1 : L) ⊗ₜ[K] a) * e) := by rw [he2, mul_assoc]
      _ = (1 : L) ⊗ₜ[K] a⁻¹ * e := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ha0]
          change (1 : L) ⊗ₜ[K] a⁻¹ * ((1 : L ⊗[K] A) * e) = _
          rw [one_mul]
  · rw [map_mul, show s ((1 : L) ⊗ₜ[K] a⁻¹) = (1 : L) ⊗ₜ[K] a⁻¹ from sigmaTensor_one_tmul K L A σ _]
    have hse : s e = (1 : L) ⊗ₜ[K] a - e := eq_sub_of_add_eq' ha
    rw [hse, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ha0]
    rfl

end Split

section FieldCase

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem exists_factor (hE : ∀ e : L ⊗[K] A, e ≠ 0 → IsUnit e) (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hy : y ≠ 0) (hdet : y 0 0 * y 1 1 - y 0 1 * y 1 0 = 0) :
    ∃ (w ρ : Fin 2 → L ⊗[K] A) (j₀ : Fin 2), ρ j₀ = 1 ∧ (∃ i, w i ≠ 0) ∧ ∀ i j, y i j = w i * ρ j := by
  by_cases hcol : y 0 0 = 0 ∧ y 1 0 = 0
  ·
    obtain ⟨h00, h10⟩ := hcol
    have hne : ∃ i, y i 1 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hy
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, hall]
    refine ⟨fun i => y i 1, ![0, 1], 1, rfl, hne, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [h00, h10]
  ·
    rw [not_and_or] at hcol
    have hne : ∃ i, y i 0 ≠ 0 := by
      rcases hcol with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨μ, h01, h11⟩ : ∃ μ : L ⊗[K] A, y 0 1 = y 0 0 * μ ∧ y 1 1 = y 1 0 * μ := by
      by_cases hp : y 0 0 = 0
      · have hr : y 1 0 ≠ 0 := by
          rcases hcol with h | h
          · exact absurd hp h
          · exact h
        obtain ⟨u, hu⟩ := hE _ hr
        have hq : y 0 1 = 0 := by
          rw [hp, zero_mul, zero_sub, neg_eq_zero] at hdet
          rcases (hu ▸ hdet : y 0 1 * ↑u = 0) |> (Units.mul_left_eq_zero u).mp with h
          exact h
        refine ⟨((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * y 1 1, ?_, ?_⟩
        · rw [hp, hq, zero_mul]
        · rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
      · obtain ⟨u, hu⟩ := hE _ hp
        refine ⟨((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * y 0 1, ?_, ?_⟩
        · rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
        · have h1 : y 0 0 * y 1 1 = y 0 1 * y 1 0 := sub_eq_zero.mp hdet
          calc y 1 1 = ((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (y 0 0 * y 1 1) := by
                rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
            _ = y 1 0 * (((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * y 0 1) := by rw [h1]; ring
    refine ⟨fun i => y i 0, ![1, μ], 0, rfl, hne, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [h01, h11]

theorem phi_phi_eq_smul (hσ : ∀ l : L, σ (σ l) = l) (δ : GL (Fin 2) (L ⊗[K] A)) (cE : L ⊗[K] A)
    (hN : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ) =
        cE • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
    (w : Fin 2 → L ⊗[K] A) : phi K L A σ δ (phi K L A σ δ w) = cE • w := by
  unfold phi
  have hin : (fun i => AutomorphicForm.sigmaTensor K L A σ
        ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec
          (fun k => AutomorphicForm.sigmaTensor K L A σ (w k)) i))
      = ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ)).mulVec
          w := by
    funext i
    rw [RingHom.map_mulVec]
    congr 1
    funext k
    exact sigmaTensor_sigmaTensor K L A σ hσ (w k)
  rw [hin, Matrix.mulVec_mulVec, hN, Matrix.smul_mulVec, Matrix.one_mulVec]

end FieldCase

section Main

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem main (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] A)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hy : y ≠ 0)
    (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hyk : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * y.map (AutomorphicForm.sigmaTensor K L A σ) =
      y * k) :
    IsUnit y := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨hσσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  set sG := AutomorphicForm.sigmaGL K L A σ with hsG
  have hfix : ∀ e : L ⊗[K] A, s e = e → ∃ r : A, e = (1 : L) ⊗ₜ[K] r :=
    fun e he => exists_eq_tmul_of_sigmaTensor_eq K L A σ h2 hgen he

  obtain ⟨ℓ, hℓ⟩ := hℓ
  have hm : ℓ - σ ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hℓ)
  let η : (L ⊗[K] A)ˣ := Units.mkOfMulEqOne ((ℓ - σ ℓ) ⊗ₜ[K] (1 : A)) ((ℓ - σ ℓ)⁻¹ ⊗ₜ[K] (1 : A))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hm, mul_one]; rfl)
  have hη : s η = -η := by
    show s ((ℓ - σ ℓ) ⊗ₜ[K] (1 : A)) = -((ℓ - σ ℓ) ⊗ₜ[K] (1 : A))
    rw [hs, sigmaTensor_tmul, map_sub, hσσ, ← neg_sub, TensorProduct.neg_tmul]

  set C := AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) with hC
  have hNδ : δ * sG δ = C := by
    obtain ⟨y₀, hy₀⟩ := hδ
    unfold AutomorphicForm.IsNormConjugator at hy₀
    rw [normString_two K L A σ h2, ← hC, ← hsG] at hy₀
    have hcen : y₀ * C * y₀⁻¹ = C := by
      rw [hC, toTensorGL_scalar, conj_scalar]
    rw [← hcen, hy₀]
    group
  set cE : L ⊗[K] A := (1 : L) ⊗ₜ[K] (c : A) with hcE
  have hcEu : IsUnit cE := (isUnit_one_tmul_iff K L A).mpr c.ne_zero
  have hCcoe : (C : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = cE • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    rw [hC, toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs
    · rfl
    · exact TensorProduct.tmul_zero _ _
  have hNM : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map s = cE • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hNδ
    simp only [Units.val_mul] at this
    rw [hsG, coe_sigmaGL] at this
    rw [this, hCcoe]

  by_cases hE : ∀ e : L ⊗[K] A, e ≠ 0 → IsUnit e
  swap
  · exfalso
    push Not at hE
    obtain ⟨e, he0, heu⟩ := hE
    obtain ⟨ε, hε, hsε⟩ := exists_idempotent_of_not_isUnit K L A σ hσσ hfix η hη he0 heu
    obtain ⟨z, hz⟩ := isSigmaConjugate_scalar_of_idempotent K L A σ δ hcEu.unit
      (by rw [IsUnit.unit_spec]; exact hNM) hε hsε
    exact hδq z hz

  by_contra hyu
  have hdet : y 0 0 * y 1 1 - y 0 1 * y 1 0 = 0 := by
    rw [← Matrix.det_fin_two]
    by_contra hd
    exact hyu ((Matrix.isUnit_iff_isUnit_det y).mpr (hE _ hd))
  obtain ⟨w, ρ, j₀, hρ, ⟨i₀, hi₀⟩, hfac⟩ := exists_factor K L A hE y hy hdet

  set lam : L ⊗[K] A := ∑ l, ρ l * k l j₀ with hlam
  have hΦ : phi K L A σ δ w = lam • w := by
    funext i
    have h := congrFun (congrFun hyk i) j₀
    simp only [Matrix.mul_apply, Matrix.map_apply, hfac, Fin.sum_univ_two, hρ, mul_one] at h
    simp only [phi, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, hlam]
    linear_combination h

  have hΦΦ := phi_phi_eq_smul K L A σ hσσ δ cE hNM w
  rw [hΦ, phi_smul, hΦ, smul_smul, ← hs] at hΦΦ
  have hlamc : s lam * lam = cE := by
    have h := congrFun hΦΦ i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h
    obtain ⟨u, hu⟩ := hE _ hi₀
    rw [← hu] at h
    exact (Units.mul_left_inj u).mp h
  have hlamu : IsUnit lam := isUnit_of_mul_isUnit_right (hlamc ▸ hcEu)

  set uU : (L ⊗[K] A)ˣ := hlamu.unit with huU'
  have huU : (uU : L ⊗[K] A) = lam := hlamu.unit_spec
  have huu : (uU : L ⊗[K] A) * s uU = (1 : L) ⊗ₜ[K] (c : A) := by rw [huU, mul_comm, hlamc]
  set Su := Matrix.GeneralLinearGroup.scalar (Fin 2) uU with hSu
  set Ssu := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (s : L ⊗[K] A →* L ⊗[K] A) uU)
    with hSsu
  have hCscal : C = Ssu * Su := by
    rw [hC, toTensorGL_scalar, hSsu, hSu, ← map_mul]
    congr 1
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    rw [mul_comm, huu]
    rfl
  set ε := Su⁻¹ * δ with hε
  have hcomm : Ssu * δ = δ * Ssu := scalar_mul_comm K L A _ δ
  have hcomm' : δ * Ssu⁻¹ = Ssu⁻¹ * δ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hεc : ε * sG ε = 1 := by
    calc ε * sG ε = Su⁻¹ * δ * (Ssu⁻¹ * sG δ) := by
            rw [hε, map_mul, map_inv, hsG, hSu, sigmaGL_scalar]
      _ = Su⁻¹ * (δ * Ssu⁻¹) * sG δ := by group
      _ = Su⁻¹ * (Ssu⁻¹ * δ) * sG δ := by rw [hcomm']
      _ = Su⁻¹ * Ssu⁻¹ * (δ * sG δ) := by group
      _ = Su⁻¹ * Ssu⁻¹ * (Ssu * Su) := by rw [hNδ, hCscal]
      _ = 1 := by group
  obtain ⟨x, hx⟩ := hilbert90 K L A σ h2 hσσ ⟨ℓ, hℓ⟩ ε hεc
  refine hδq uU ⟨x⁻¹, ?_⟩
  rw [inv_inv, map_inv, ← hsG, ← hSu]
  have hδeq : δ = x⁻¹ * Su * sG x := by
    rw [hSu, ← scalar_mul_comm K L A uU x⁻¹, ← hSu, mul_assoc, ← inv_mul_eq_iff_eq_mul, ← hε, hx]
  rw [hδeq]
  group

end Main

end P2mSigmaElliptic

end

theorem solution
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [Field A] [Algebra K A]
    (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] A)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hy : y ≠ 0)
    (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hyk : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * y.map (AutomorphicForm.sigmaTensor K L A σ) =
      y * k) :
    IsUnit y :=
  P2mSigmaElliptic.main K L A σ h2 hgen c δ hδ hδq y hy k hyk

end S_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
