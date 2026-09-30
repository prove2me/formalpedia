-- Prove2me | solution 1 for AndersonAccel.Safe.abs_det_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:54:26.304075+00:00
-- url     : https://prove2.me/submissions/80b1f5af-04b3-4848-8c1d-a3f3d6df649d

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_AndersonAccel_Safe_windowB
import Mathlib.Tactic
open scoped RealInnerProductSpace
open InnerProductSpace AndersonAccel.Safe

private theorem gs_inner {n : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    ⟪windowShat s i,s i⟫ = ‖windowShat s i‖^2 := by
  rw [gramSchmidt_def'' ℝ s i]
  simp only [inner_add_right,inner_sum,real_inner_smul_right,RCLike.ofReal_real_eq_id, id_eq]
  have hz : ∑ j ∈ Finset.Iio i, (⟪gramSchmidt ℝ s j,s i⟫/‖gramSchmidt ℝ s j‖^2)*
      ⟪windowShat s i,gramSchmidt ℝ s j⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [show ⟪windowShat s i,gramSchmidt ℝ s j⟫ = 0 from
      gramSchmidt_orthogonal ℝ s (by have := Finset.mem_Iio.mp hj; omega)]
    simp
  rw [hz,add_zero]
  exact real_inner_self_eq_norm_sq _


private theorem det_one_rank {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    LinearMap.det ((1+rankOne ℝ v w : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap) = 1+⟪w,v⟫ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [← LinearMap.det_toMatrix b.toBasis]
  simp only [ContinuousLinearMap.toLinearMap_add,ContinuousLinearMap.toLinearMap_one,map_add,
    LinearMap.toMatrix_one,toMatrix_rankOne]
  rw [Matrix.vecMulVec_eq Unit,Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  change w i*v i=v i*w i
  ring

private theorem det_rank_update {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsUnit B)
    (v w : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    LinearMap.det ((B+a • rankOne ℝ v w).toLinearMap) =
      LinearMap.det B.toLinearMap*(1+a*⟪w,(Ring.inverse B) v⟫) := by
  have hv : B ((Ring.inverse B) v) = v := by
    have hh := congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => f v)
      (Ring.mul_inverse_cancel B hB)
    simpa using hh
  have he : B+a • rankOne ℝ v w = B*(1+rankOne ℝ (a • (Ring.inverse B) v) w) := by
    ext x
    simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.add_apply,
      one_apply_eq_self,rankOne_apply,map_add,map_smul,
      ContinuousLinearMap.smul_apply,hv]
  rw [he,ContinuousLinearMap.toLinearMap_mul,map_mul,det_one_rank,real_inner_smul_right]

private theorem phi_det (θ η : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    θ ≤ |1-phiTheta θ η+phiTheta θ η*η| := by
  unfold phiTheta
  split_ifs with h
  · simpa using h
  · have hη := abs_lt.mp (lt_of_not_ge h)
    have hd : 1-η ≠ 0 := by linarith
    have he : 1-(1-signOne η*θ)/(1-η)+(1-signOne η*θ)/(1-η)*η = signOne η*θ := by
      field_simp; ring
    rw [he,abs_mul]
    simp only [signOne]
    split_ifs <;> simp [abs_of_pos hθ0]


private theorem det_window_step {n : ℕ} (θ : ℝ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hB : IsUnit (windowB θ s y i)) (hwd : ⟪windowShat s i,s i⟫ ≠ 0) :
    LinearMap.det (windowB θ s y (i+1)).toLinearMap =
      LinearMap.det (windowB θ s y i).toLinearMap*
        (1-phiTheta θ (⟪windowShat s i,(Ring.inverse (windowB θ s y i)) (y i)⟫/‖windowShat s i‖^2)+
          phiTheta θ (⟪windowShat s i,(Ring.inverse (windowB θ s y i)) (y i)⟫/‖windowShat s i‖^2)*
            (⟪windowShat s i,(Ring.inverse (windowB θ s y i)) (y i)⟫/‖windowShat s i‖^2)) := by
  let B := windowB θ s y i
  let sh := windowShat s i
  let η := ⟪sh,(Ring.inverse B) (y i)⟫/‖sh‖^2
  let t := phiTheta θ η
  have hv : (Ring.inverse B) (B (s i)) = s i := by
    have hh := congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => f (s i))
      (Ring.inverse_mul_cancel B hB)
    simpa using hh
  rw [windowB,det_rank_update _ hB]
  change LinearMap.det B.toLinearMap*(1+⟪sh,s i⟫⁻¹*
    ⟪sh,(Ring.inverse B) (t • y i+(1-t) • B (s i)-B (s i))⟫) =
    LinearMap.det B.toLinearMap*(1-t+t*η)
  congr 1
  simp only [map_sub,map_add,map_smul,hv,inner_sub_right,inner_add_right,real_inner_smul_right]
  have hgs : ⟪sh,s i⟫ = ‖sh‖^2 := gs_inner s i
  have hn : ‖sh‖ ≠ 0 := by intro he; apply hwd; rw [hgs,he]; norm_num
  rw [hgs]
  dsimp [η]
  field_simp
  <;> ring

theorem solution {n : ℕ} (θbar : ℝ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0) :
    θbar ^ mk ≤ |LinearMap.det (windowB θbar s y mk :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| ∧
      0 < θbar ^ mk ∧ IsUnit (windowB θbar s y mk) := by
  have hi : ∀ i ≤ mk, θbar^i ≤ |LinearMap.det (windowB θbar s y i).toLinearMap| ∧
      IsUnit (windowB θbar s y i) := by
    intro i
    induction i with
    | zero => intro _; simp [windowB]
    | succ i ih =>
      intro hik
      have him : i < mk := by omega
      obtain ⟨hd,hunit⟩ := ih (by omega)
      have hn : θbar^(i+1) ≤ |LinearMap.det (windowB θbar s y (i+1)).toLinearMap| := by
        rw [det_window_step θbar s y i hunit (hwd i him),abs_mul,pow_succ]
        exact mul_le_mul hd (phi_det θbar _ hθ0 hθ1) hθ0.le (abs_nonneg _)
      refine ⟨hn,?_⟩
      apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
      apply (LinearMap.isUnit_iff_isUnit_det _).mpr
      apply isUnit_iff_ne_zero.mpr
      exact abs_pos.mp (lt_of_lt_of_le (pow_pos hθ0 _) hn)
  exact ⟨(hi mk le_rfl).1,pow_pos hθ0 _,(hi mk le_rfl).2⟩
