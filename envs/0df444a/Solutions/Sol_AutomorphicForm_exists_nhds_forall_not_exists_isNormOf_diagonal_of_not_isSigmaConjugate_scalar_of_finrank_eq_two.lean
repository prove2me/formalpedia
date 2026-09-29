-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/318662c5-9758-5ccf-b94e-aed5614b7b01

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace R1NonNormDiag

section Squares

theorem exists_nhds_one_forall_exists_sq {F : Type*} [NormedField F] [CompleteSpace F]
    [IsUltrametricDist F] (h2 : (2 : F) ≠ 0) :
    ∃ U ∈ nhds (1 : F), ∀ a ∈ U, ∃ b : F, b ^ 2 = a := by
  have h2n : 0 < ‖(2 : F)‖ := norm_pos_iff.mpr h2
  set r : ℝ := ‖(2 : F)‖ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hr2 : r ≤ ‖(2 : F)‖ := by rw [hr_def]; linarith
  refine ⟨Metric.closedBall (1 : F) (‖(2 : F)‖ * r), Metric.closedBall_mem_nhds _ (by positivity),
    ?_⟩
  intro a ha
  rw [Metric.mem_closedBall, dist_eq_norm] at ha
  set t : F := a - 1 with ht_def
  set D : Set F := Metric.closedBall (0 : F) r with hD_def
  haveI hDc : IsClosed D := Metric.isClosed_closedBall
  haveI : CompleteSpace D := IsClosed.completeSpace_coe
  haveI : Nonempty D := ⟨⟨0, Metric.mem_closedBall_self hr.le⟩⟩
  have hmem : ∀ z : F, z ∈ D ↔ ‖z‖ ≤ r := fun z => by
    rw [hD_def, Metric.mem_closedBall, dist_zero_right]
  have hstep : ∀ z : F, ‖z‖ ≤ r → ‖(2 : F)⁻¹ * (t - z ^ 2)‖ ≤ r := by
    intro z hz
    have hz2 : ‖z ^ 2‖ ≤ ‖(2 : F)‖ * r := by
      rw [norm_pow, sq]
      exact mul_le_mul (hz.trans hr2) hz (norm_nonneg _) (norm_nonneg _)
    have htz : ‖t - z ^ 2‖ ≤ ‖(2 : F)‖ * r := by
      calc ‖t - z ^ 2‖ = ‖t + -(z ^ 2)‖ := by rw [sub_eq_add_neg]
        _ ≤ max ‖t‖ ‖-(z ^ 2)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ‖(2 : F)‖ * r := max_le ha (by rw [norm_neg]; exact hz2)
    rw [norm_mul, norm_inv]
    calc ‖(2 : F)‖⁻¹ * ‖t - z ^ 2‖ ≤ ‖(2 : F)‖⁻¹ * (‖(2 : F)‖ * r) := by gcongr
      _ = r := by field_simp
  let T : D → D := fun z =>
    ⟨(2 : F)⁻¹ * (t - (z : F) ^ 2), (hmem _).mpr (hstep z ((hmem _).mp z.2))⟩
  have hT : ContractingWith (1 / 2) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' => ?_⟩
    have hz : ‖(z : F)‖ ≤ r := (hmem _).mp z.2
    have hz' : ‖(z' : F)‖ ≤ r := (hmem _).mp z'.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖(2 : F)⁻¹ * (t - (z : F) ^ 2) - (2 : F)⁻¹ * (t - (z' : F) ^ 2)‖ ≤ _
    have hsum : ‖(z' : F) + z‖ ≤ r :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz' hz)
    rw [show (2 : F)⁻¹ * (t - (z : F) ^ 2) - (2 : F)⁻¹ * (t - (z' : F) ^ 2)
        = (2 : F)⁻¹ * (((z' : F) + z) * ((z' : F) - z)) by ring]
    rw [norm_mul, norm_inv, norm_mul, norm_sub_rev (z' : F) z]
    calc ‖(2 : F)‖⁻¹ * (‖(z' : F) + z‖ * ‖(z : F) - z'‖)
        ≤ ‖(2 : F)‖⁻¹ * (r * ‖(z : F) - z'‖) := by gcongr
      _ = ((1 / 2 : NNReal) : ℝ) * ‖(z : F) - z'‖ := by
          rw [hr_def]
          push_cast
          field_simp
  obtain ⟨z, hz⟩ : ∃ z : D, T z = z := ⟨_, hT.fixedPoint_isFixedPt⟩
  refine ⟨1 + (z : F), ?_⟩
  have hz' : (2 : F)⁻¹ * (t - (z : F) ^ 2) = z := congrArg Subtype.val hz
  have h2z : (2 : F) * z = t - (z : F) ^ 2 := by
    calc (2 : F) * z = 2 * ((2 : F)⁻¹ * (t - (z : F) ^ 2)) := by rw [hz']
      _ = t - (z : F) ^ 2 := mul_inv_cancel_left₀ h2 _
  linear_combination h2z + ht_def

end Squares

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

section Diagonal

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem exists_mul_sigma_eq_of_isNormOf_diagonal (h2 : Module.finrank K L = 2)
    (hσ : ∀ l : L, σ (σ l) = l) (α β : A) (hαβ : IsUnit (α - β)) (γ : GL (Fin 2) A)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) A) = !![α, 0; 0, β]) (δ' : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ') :
    ∃ d : L ⊗[K] A, d * AutomorphicForm.sigmaTensor K L A σ d = (1 : L) ⊗ₜ[K] α := by
  obtain ⟨y, hy⟩ := h
  unfold AutomorphicForm.IsNormConjugator at hy
  rw [normString_two K L A σ h2] at hy
  set sG := AutomorphicForm.sigmaGL K L A σ with hsG
  set G := AutomorphicForm.toTensorGL K L A γ with hG
  set δ₂ := y⁻¹ * δ' * sG y with hδ₂
  have hN : δ₂ * sG δ₂ = G := by
    rw [hy, hδ₂, map_mul, map_mul, map_inv, hsG, sigmaGL_sigmaGL K L A σ hσ]
    group
  have hGfix : sG G = G := sigmaGL_toTensorGL K L A σ γ
  have hcomm : G * δ₂ = δ₂ * G := by
    have h1 : sG δ₂ * δ₂ = G := by
      have := congrArg sG hN
      rwa [map_mul, hsG, sigmaGL_sigmaGL K L A σ hσ, ← hsG, hGfix] at this
    calc G * δ₂ = δ₂ * sG δ₂ * δ₂ := by rw [hN]
      _ = δ₂ * (sG δ₂ * δ₂) := by rw [mul_assoc]
      _ = δ₂ * G := by rw [h1]

  have hG00 : (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 = (1 : L) ⊗ₜ[K] α := by
    rw [hG, toTensorGL_apply, hγ]; simp
  have hG01 : (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
    rw [hG, toTensorGL_apply, hγ]; simp
  have hG10 : (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
    rw [hG, toTensorGL_apply, hγ]; simp
  have hG11 : (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 = (1 : L) ⊗ₜ[K] β := by
    rw [hG, toTensorGL_apply, hγ]; simp
  set m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := (δ₂ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hm
  have hcommM : (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * m
      = m * (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
      hcomm
    simpa using this
  have h01 : ((1 : L) ⊗ₜ[K] α - (1 : L) ⊗ₜ[K] β) * m 0 1 = 0 := by
    have := congrFun (congrFun hcommM 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hG00, hG01, hG11, zero_mul, add_zero,
      mul_zero, zero_add] at this
    rw [sub_mul, this, mul_comm, sub_self]
  have hunit : IsUnit ((1 : L) ⊗ₜ[K] α - (1 : L) ⊗ₜ[K] β) := by
    rw [← TensorProduct.tmul_sub]
    exact hαβ.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
  have hm01 : m 0 1 = 0 := (hunit.mul_right_eq_zero).mp h01
  refine ⟨m 0 0, ?_⟩
  have h00 := congrArg
    (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) hN
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00
  rw [hsG, sigmaGL_apply, sigmaGL_apply, ← hm, hm01, zero_mul, add_zero] at h00
  rw [h00, hG00]

end Diagonal

section Key

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem not_isNormOf_diagonal (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] A)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (a : Aˣ) (b : A) (hb : b ^ 2 = a) (ha2 : (a : A) ^ 2 ≠ 1)
    (γ : GL (Fin 2) A) (hγ : (γ : Matrix (Fin 2) (Fin 2) A) = !![(c : A) * a, 0; 0, (c : A) * ↑a⁻¹])
    (δ' : GL (Fin 2) (L ⊗[K] A)) (hδ' : AutomorphicForm.IsNormOf K L A σ γ δ') : False := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective

  obtain ⟨hσσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by rw [← hb]; ring)

  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hne : IsUnit ((c : A) * (a : A) - (c : A) * ((a⁻¹ : Aˣ) : A)) := by
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro h
    have haa : (a : A) = ((a⁻¹ : Aˣ) : A) := mul_left_cancel₀ c.ne_zero h
    apply ha2
    calc (a : A) ^ 2 = (a : A) * ((a⁻¹ : Aˣ) : A) := by rw [sq, ← haa]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨d, hd⟩ := exists_mul_sigma_eq_of_isNormOf_diagonal K L A σ h2 hσσ _ _ hne γ hγ δ' hδ'

  set u : L ⊗[K] A := d * ((1 : L) ⊗ₜ[K] b⁻¹) with hu
  have hsb : s ((1 : L) ⊗ₜ[K] b⁻¹) = (1 : L) ⊗ₜ[K] b⁻¹ := sigmaTensor_one_tmul K L A σ _
  have huu : u * s u = (1 : L) ⊗ₜ[K] (c : A) := by
    rw [hu, map_mul, hsb, mul_mul_mul_comm, hd, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, ← hb]
    congr 1
    field_simp
  have huinv : u * (s u * ((1 : L) ⊗ₜ[K] ((c⁻¹ : Aˣ) : A))) = 1 := by
    rw [← mul_assoc, huu, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.mul_inv]
    rfl
  let uU : (L ⊗[K] A)ˣ := Units.mkOfMulEqOne _ _ huinv
  have huU : (uU : L ⊗[K] A) = u := rfl

  set sG := AutomorphicForm.sigmaGL K L A σ with hsG
  set Su := Matrix.GeneralLinearGroup.scalar (Fin 2) uU with hSu
  set Ssu := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (s : L ⊗[K] A →* L ⊗[K] A) uU)
    with hSsu
  set C := AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) with hC
  have hCscal : C = Ssu * Su := by
    rw [hC, toTensorGL_scalar, hSsu, hSu, ← map_mul]
    congr 1
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, huU]
    rw [mul_comm, huu]
    rfl

  have hNδ : δ * sG δ = C := by
    obtain ⟨y₀, hy₀⟩ := hδ
    unfold AutomorphicForm.IsNormConjugator at hy₀
    rw [normString_two K L A σ h2, ← hC, ← hsG] at hy₀
    have hcen : y₀ * C * y₀⁻¹ = C := by
      rw [hCscal]
      calc y₀ * (Ssu * Su) * y₀⁻¹ = (y₀ * Ssu * y₀⁻¹) * (y₀ * Su * y₀⁻¹) := by group
        _ = Ssu * Su := by rw [conj_scalar, conj_scalar]
    rw [← hcen, hy₀]
    group

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

  obtain ⟨x, hx⟩ := hilbert90 K L A σ h2 hσσ hℓ ε hεc
  refine hδq uU ⟨x⁻¹, ?_⟩
  rw [inv_inv, map_inv, ← hsG, ← hSu]
  have hδeq : δ = x⁻¹ * Su * sG x := by
    rw [hSu, ← scalar_mul_comm K L A uU x⁻¹, ← hSu, mul_assoc, ← inv_mul_eq_iff_eq_mul, ← hε, hx]
  rw [hδeq]
  group

end Key

end R1NonNormDiag

end

open R1NonNormDiag in
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
    ∃ U ∈ nhds (1 : (v.adicCompletion K)), ∀ a : (v.adicCompletion K)ˣ, (a : (v.adicCompletion K)) ∈ U → (a : (v.adicCompletion K)) ^ 2 ≠ 1 →
      ∀ γ : GL (Fin 2) (v.adicCompletion K),
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          !![(c : (v.adicCompletion K)) * (a : (v.adicCompletion K)), 0; 0, (c : (v.adicCompletion K)) * ((a⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))] →
        ¬ ∃ δ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K), AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ' := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨U, hU, hsq⟩ :=
    exists_nhds_one_forall_exists_sq (F := v.adicCompletion K) two_ne_zero
  refine ⟨U, hU, fun a haU ha2 γ hγ hex => ?_⟩
  obtain ⟨δ', hδ'⟩ := hex
  obtain ⟨b, hb⟩ := hsq (a : v.adicCompletion K) haU
  exact not_isNormOf_diagonal K L (v.adicCompletion K) σ h2 hgen c δ hδ hδq a b hb ha2 γ hγ δ' hδ'

end S_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
