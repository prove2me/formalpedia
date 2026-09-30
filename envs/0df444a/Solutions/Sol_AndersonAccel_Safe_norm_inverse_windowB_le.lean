-- Prove2me | solution 1 for AndersonAccel.Safe.norm_inverse_windowB_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:57:49.41598+00:00
-- url     : https://prove2.me/submissions/8bb33bd4-6149-4135-9e7c-5b25d50a5616

import Definitions.Def_AndersonAccel_Safe_windowB
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic
open scoped RealInnerProductSpace
open InnerProductSpace

private theorem inverse_norm_bound {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsUnit B)
    (K d : ℝ) (hK : 0 < K) (hd : 0 < d) (hBK : ‖B‖ ≤ K)
    (hdet : d ≤ |LinearMap.det B.toLinearMap|) :
    ‖Ring.inverse B‖ ≤ K^(n-1)/d := by
  let T := B.toLinearMap.adjoint ∘ₗ B.toLinearMap
  have hT : T.IsSymmetric := B.toLinearMap.isSymmetric_adjoint_comp_self
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let e := hT.eigenvalues hdim
  let v := hT.eigenvectorBasis hdim
  have hev : ∀ i,T (v i)=e i • v i := hT.apply_eigenvectorBasis hdim
  have hquad (x : EuclideanSpace ℝ (Fin n)) : ⟪T x,x⟫=‖B x‖^2 := by
    dsimp [T]
    rw [LinearMap.adjoint_inner_left]
    exact real_inner_self_eq_norm_sq _
  have hepos (i : Fin n) : 0 ≤ e i := by
    have hh := hquad (v i)
    rw [hev,real_inner_smul_left,real_inner_self_eq_norm_sq,v.norm_eq_one] at hh
    nlinarith [sq_nonneg ‖B (v i)‖]
  have heupper (i : Fin n) : e i ≤ K^2 := by
    have hh := hquad (v i)
    rw [hev,real_inner_smul_left,real_inner_self_eq_norm_sq,v.norm_eq_one] at hh
    have hh' := B.le_opNorm (v i)
    rw [v.norm_eq_one,mul_one] at hh'
    nlinarith [norm_nonneg (B (v i))]
  have hprod : ∏ i,e i = (LinearMap.det B.toLinearMap)^2 := by
    have heq : LinearMap.det T = ∏ i,e i := by
      simpa only [RCLike.ofReal_real_eq_id,id_eq,e] using hT.det_eq_prod_eigenvalues hdim
    rw [← heq]
    change LinearMap.det (B.toLinearMap.adjoint*B.toLinearMap) = _
    rw [map_mul]
    have ha : LinearMap.det B.toLinearMap.adjoint=LinearMap.det B.toLinearMap := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis,LinearMap.toMatrix_adjoint]
      simp [LinearMap.det_toMatrix]
    rw [ha]; ring
  have helower (i : Fin n) : d^2 ≤ e i*(K^2)^(n-1) := by
    have hrest : ∏ j ∈ Finset.univ.erase i,e j ≤ (K^2)^(n-1) := by
      calc _ ≤ ∏ j ∈ Finset.univ.erase i,K^2 := Finset.prod_le_prod (fun j _ => hepos j) (fun j _ => heupper j)
           _ = _ := by simp
    have hh := mul_le_mul_of_nonneg_left hrest (hepos i)
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i),hprod] at hh
    nlinarith [sq_abs (LinearMap.det B.toLinearMap),hdet]
  have hlower (x : EuclideanSpace ℝ (Fin n)) : d^2*‖x‖^2 ≤ (K^(n-1))^2*‖B x‖^2 := by
    have hsum : ⟪T x,x⟫ = ∑ i,e i*⟪v i,x⟫^2 := by
      rw [← v.sum_inner_mul_inner]
      apply Finset.sum_congr rfl
      intro i _
      have hh : ⟪v i,T x⟫ = e i*⟪v i,x⟫ := by rw [← hT,hev,real_inner_smul_left]
      rw [real_inner_comm (v i) (T x),hh]
      ring
    rw [← hquad,hsum,← v.sum_sq_inner_right x,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (helower i) (sq_nonneg ⟪v i,x⟫)
    rw [pow_right_comm] at hh
    nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hv : B ((Ring.inverse B) x)=x := by
    have hh := congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => f x)
      (Ring.mul_inverse_cancel B hB)
    simpa using hh
  have hh := hlower ((Ring.inverse B) x)
  rw [hv] at hh
  have hk0 : 0 ≤ K^(n-1) := (pow_pos hK _).le
  have he : K^(n-1)/d*‖x‖ = K^(n-1)*‖x‖/d := by ring
  rw [he]
  apply (le_div_iff₀ hd).mpr
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hd.le) (mul_nonneg hk0 (norm_nonneg x))).mp
  simpa only [mul_pow,mul_comm] using hh

open AndersonAccel.Safe
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

private theorem phi_bounds (θ η : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < phiTheta θ η ∧ phiTheta θ η ≤ 1+θ := by
  unfold phiTheta
  split_ifs with h
  · constructor <;> linarith
  · have hη := abs_lt.mp (lt_of_not_ge h)
    have hd : 0 < 1-η := by linarith
    unfold signOne
    split_ifs with h0
    · constructor
      · exact div_pos (by linarith) hd
      · apply (div_le_iff₀ hd).mpr
        have hh := mul_pos (by linarith : 0 < θ) (by linarith : 0 < 1-η)
        nlinarith
    · constructor
      · apply div_pos _ hd; linarith
      · apply (div_le_iff₀ hd).mpr
        nlinarith [mul_nonneg (by linarith : 0 ≤ -η) (by linarith : 0 ≤ 1+θ)]

private theorem window_step {n : ℕ} (θ τ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hτ : 0 < τ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hwd : ⟪windowShat s i,s i⟫ ≠ 0) (hy : ‖y i‖ ≤ 2*‖s i‖)
    (hs : τ*‖s i‖ ≤ ‖windowShat s i‖) :
    ‖windowB θ s y (i+1)‖+2 ≤ ((1+θ+τ)/τ)*(‖windowB θ s y i‖+2) := by
  let B := windowB θ s y i
  let sh := windowShat s i
  let η := ⟪sh,(Ring.inverse B) (y i)⟫/‖sh‖^2
  let t := phiTheta θ η
  have ht0 : 0 < t := (phi_bounds θ η hθ0 hθ1).1
  have ht1 : t ≤ 1+θ := (phi_bounds θ η hθ0 hθ1).2
  have hsh : 0 < ‖sh‖ := by
    have hh := gs_inner s i
    change ⟪windowShat s i,s i⟫ = ‖sh‖^2 at hh
    rw [hh] at hwd
    exact lt_of_le_of_ne (norm_nonneg _) (by intro he; apply hwd; rw [← he]; norm_num)
  have hs0 : 0 ≤ ‖s i‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have he : t • y i+(1-t) • B (s i)-B (s i) = t • (y i-B (s i)) := by module
  have hupdate : windowB θ s y (i+1) = B+(‖sh‖^2)⁻¹ • rankOne ℝ (t • (y i-B (s i))) sh := by
    rw [windowB]
    change B+⟪windowShat s i,s i⟫⁻¹ • rankOne ℝ (t • y i+(1-t) • B (s i)-B (s i)) sh = _
    rw [gs_inner,he]
  have hn := norm_add_le B ((‖sh‖^2)⁻¹ • rankOne ℝ (t • (y i-B (s i))) sh)
  rw [← hupdate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hsh)),
    norm_rankOne,norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at hn
  have hdiff : ‖y i-B (s i)‖ ≤ (2+‖B‖)*‖s i‖ := by
    have hh := norm_sub_le (y i) (B (s i))
    have hh' := B.le_opNorm (s i)
    nlinarith
  have hmul : (‖sh‖^2)⁻¹*(t*‖y i-B (s i)‖*‖sh‖) ≤
      (1+θ)/τ*(2+‖B‖) := by
    have hn' : (‖sh‖^2)⁻¹*(t*‖y i-B (s i)‖*‖sh‖) = t*‖y i-B (s i)‖/‖sh‖ := by field_simp <;> ring
    rw [hn']
    apply (div_le_iff₀ hsh).mpr
    have h1 := mul_le_mul_of_nonneg_left hdiff ht0.le
    have h2 := mul_le_mul_of_nonneg_right ht1 (mul_nonneg (by positivity : 0 ≤ 2+‖B‖) hs0)
    have h3 := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1+θ)/τ*(2+‖B‖) by positivity)
    have hid : (1+θ)/τ*(2+‖B‖)*(τ*‖s i‖) = (1+θ)*((2+‖B‖)*‖s i‖) := by field_simp <;> ring
    rw [hid] at h3
    nlinarith
  have hid : ((1+θ+τ)/τ)*(‖B‖+2) = ‖B‖+2+(1+θ)/τ*(2+‖B‖) := by field_simp <;> ring
  change ‖windowB θ s y (i+1)‖+2 ≤ ((1+θ+τ)/τ)*(‖B‖+2)
  rw [hid]
  linarith

private theorem norm_window_local {n : ℕ} (θbar τ : ℝ) (m : ℕ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : 1 ≤ m)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ) (hmk : mk ≤ m)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0)
    (hy : ∀ i < mk, ‖y i‖ ≤ 2 * ‖s i‖)
    (hτs : ∀ i < mk, τ * ‖s i‖ ≤ ‖windowShat s i‖) :
    ‖windowB θbar s y mk‖ ≤ 3 * ((1 + θbar + τ) / τ) ^ m - 2 := by
  let a := (1+θbar+τ)/τ
  have ha : 1 ≤ a := (le_div_iff₀ hτ0).mpr (by linarith)
  have hi : ∀ i ≤ mk,‖windowB θbar s y i‖+2 ≤ 3*a^i := by
    intro i
    induction i with
    | zero => intro _; simp only [windowB,pow_zero,mul_one]; have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)); change ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 at this; linarith
    | succ i ih =>
      intro hik
      have him : i < mk := by omega
      have hh := window_step θbar τ hθ0 hθ1 hτ0 s y i (hwd i him) (hy i him) (hτs i him)
      have hh' := mul_le_mul_of_nonneg_left (ih (by omega)) (le_trans zero_le_one ha)
      rw [pow_succ]
      change ‖windowB θbar s y (i+1)‖+2 ≤ 3*(a^i*a)
      nlinarith
  have hh := hi mk le_rfl
  have hh' := pow_le_pow_right₀ ha hmk
  change ‖windowB θbar s y mk‖ ≤ 3*a^m-2
  linarith

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

private theorem det_window_local {n : ℕ} (θbar : ℝ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
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


theorem solution {n : ℕ} (θbar τ : ℝ) (m : ℕ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : 1 ≤ m)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ) (hmk : mk ≤ m)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0)
    (hy : ∀ i < mk, ‖y i‖ ≤ 2 * ‖s i‖)
    (hτs : ∀ i < mk, τ * ‖s i‖ ≤ ‖windowShat s i‖) :
    ‖Ring.inverse (windowB θbar s y mk)‖ ≤
      (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m := by
  let K := 3*((1+θbar+τ)/τ)^m-2
  have ha : 1 ≤ (1+θbar+τ)/τ := (le_div_iff₀ hτ0).mpr (by linarith)
  have hK : 0 < K := by have hh := one_le_pow₀ ha (n := m); dsimp [K]; linarith
  obtain ⟨hdet,_,hunit⟩ := det_window_local θbar hθ0 hθ1 s y mk hwd
  apply inverse_norm_bound _ hunit K (θbar^m) hK (pow_pos hθ0 _)
    (norm_window_local θbar τ m hθ0 hθ1 hτ0 hτ1 hm s y mk hmk hwd hy hτs)
  exact le_trans (pow_le_pow_of_le_one hθ0.le hθ1.le hmk) hdet
