-- Prove2me | solution 1 for AndersonAccel.Safe.run_H_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:27:16.364147+00:00
-- url     : https://prove2.me/submissions/f17474b4-86c4-4a08-a38f-a42f6390057b

import Definitions.Def_AndersonAccel_Safe_IsAAISRun
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
open Finset
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



private theorem gs_local {n : ℕ} (I : Finset ℕ)
    (v : ℕ → EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin n))
    (horth : ∀ i ∈ I,∀ j ∈ I,i ≠ j → ⟪v i,v j⟫=0)
    (hne : ∀ i ∈ I,v i ≠ 0) :
    let sh := s-∑ j ∈ I,(⟪v j,s⟫/⟪v j,v j⟫) • v j
    (∀ i ∈ I,⟪v i,sh⟫=0) ∧ ⟪sh,s⟫=‖sh‖^2 := by
  classical
  dsimp only
  let sh := s-∑ j ∈ I,(⟪v j,s⟫/⟪v j,v j⟫) • v j
  have ho (i : ℕ) (hi : i ∈ I) : ⟪v i,sh⟫=0 := by
    dsimp [sh]
    simp only [inner_sub_right,inner_sum,real_inner_smul_right]
    rw [sum_eq_single i]
    · have hv : ⟪v i,v i⟫ ≠ 0 := by rw [real_inner_self_eq_norm_sq];exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hne i hi))
      field_simp
      ring
    · intro j hj hji
      rw [horth i hi j hj (Ne.symm hji),mul_zero]
    · exact fun hn => False.elim (hn hi)
  refine ⟨ho,?_⟩
  have hdecomp : s=sh+∑ j ∈ I,(⟪v j,s⟫/⟪v j,v j⟫) • v j := by dsimp [sh];module
  change ⟪sh,s⟫=‖sh‖^2
  rw [hdecomp,inner_add_right,inner_sum]
  have hz : ∑ j ∈ I,⟪sh,(⟪v j,s⟫/⟪v j,v j⟫) • v j⟫=0 := by
    apply sum_eq_zero
    intro j hj
    rw [real_inner_smul_right,← real_inner_comm sh (v j),ho j hj,mul_zero]
  rw [hz,add_zero,real_inner_self_eq_norm_sq]

private theorem inverse_update {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsUnit B)
    (s yt sh : EuclideanSpace ℝ (Fin n))
    (hb : ⟪sh,s⟫ ≠ 0) (ha : ⟪sh,(Ring.inverse B) yt⟫ ≠ 0)
    (hBu : IsUnit (B+⟪sh,s⟫⁻¹ • rankOne ℝ (yt-B s) sh)) :
    Ring.inverse (B+⟪sh,s⟫⁻¹ • rankOne ℝ (yt-B s) sh)=
      Ring.inverse B+⟪sh,(Ring.inverse B) yt⟫⁻¹ •
        ((rankOne ℝ (s-(Ring.inverse B) yt) sh).comp (Ring.inverse B)) := by
  let H:=Ring.inverse B
  let b:=⟪sh,s⟫
  let a:=⟪sh,H yt⟫
  let Bu:=B+b⁻¹ • rankOne ℝ (yt-B s) sh
  let Hu:=H+a⁻¹ • ((rankOne ℝ (s-H yt) sh).comp H)
  have hHB (z : EuclideanSpace ℝ (Fin n)) : H (B z)=z := by
    have hh:=congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A z) (Ring.inverse_mul_cancel B hB)
    simpa [H] using hh
  have hprod : Hu*Bu=1 := by
    ext1 z
    have he : H (Bu z)=z+(b⁻¹*⟪sh,z⟫) • (H yt-s) := by
      change H (B z+b⁻¹ • (⟪sh,z⟫ • (yt-B s)))=z+(b⁻¹*⟪sh,z⟫) • (H yt-s)
      simp only [map_add,map_smul,map_sub,hHB]
      module
    have hi : ⟪sh,H (Bu z)⟫=b⁻¹*⟪sh,z⟫*a := by
      rw [he,inner_add_right,real_inner_smul_right,inner_sub_right]
      change ⟪sh,z⟫+(b⁻¹*⟪sh,z⟫)*(a-b)=b⁻¹*⟪sh,z⟫*a
      dsimp [b] at *
      field_simp
      <;> ring
    change Hu (Bu z)=z
    change H (Bu z)+a⁻¹ • (⟪sh,H (Bu z)⟫ • (s-H yt))=z
    rw [hi,he]
    have hc : a⁻¹*(b⁻¹*⟪sh,z⟫*a)=b⁻¹*⟪sh,z⟫ := by
      dsimp [a,H] at *
      field_simp
    rw [smul_smul,hc]
    module
  have heq := congrArg (fun A => A*Ring.inverse Bu) hprod
  rw [mul_assoc,Ring.mul_inverse_cancel Bu hBu,mul_one,one_mul] at heq
  exact heq.symm


private theorem update_bounds {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsUnit B)
    (θ τ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hτ : 0 < τ)
    (s y sh : EuclideanSpace ℝ (Fin n)) (hsne : s ≠ 0)
    (hgs : ⟪sh,s⟫=‖sh‖^2) (hy : ‖y‖ ≤ 2*‖s‖) (hs : τ*‖s‖ ≤ ‖sh‖) :
    let η:=⟪sh,(Ring.inverse B) y⟫/‖sh‖^2
    let t:=phiTheta θ η
    let yt:=t • y+(1-t) • B s
    let Bu:=B+⟪sh,s⟫⁻¹ • rankOne ℝ (yt-B s) sh
    IsUnit Bu ∧ θ*|LinearMap.det B.toLinearMap| ≤ |LinearMap.det Bu.toLinearMap| ∧
      ‖Bu‖+2 ≤ ((1+θ+τ)/τ)*(‖B‖+2) ∧
      Ring.inverse Bu=Ring.inverse B+⟪sh,(Ring.inverse B) yt⟫⁻¹ •
        ((rankOne ℝ (s-(Ring.inverse B) yt) sh).comp (Ring.inverse B)) := by
  dsimp only
  let η:=⟪sh,(Ring.inverse B) y⟫/‖sh‖^2
  let t:=phiTheta θ η
  let yt:=t • y+(1-t) • B s
  let Bu:=B+⟪sh,s⟫⁻¹ • rankOne ℝ (yt-B s) sh
  have ht0 : 0 < t := (phi_bounds θ η hθ0 hθ1).1
  have ht1 : t ≤ 1+θ := (phi_bounds θ η hθ0 hθ1).2
  have hsh : 0 < ‖sh‖ := lt_of_lt_of_le (mul_pos hτ (norm_pos_iff.mpr hsne)) hs
  have hwd : ⟪sh,s⟫ ≠ 0 := by rw [hgs];exact ne_of_gt (sq_pos_of_pos hsh)
  have hv : (Ring.inverse B) (B s)=s := by
    have hh:=congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A s) (Ring.inverse_mul_cancel B hB)
    simpa using hh
  have hdet : LinearMap.det Bu.toLinearMap=LinearMap.det B.toLinearMap*(1-t+t*η) := by
    change LinearMap.det (B+⟪sh,s⟫⁻¹ • rankOne ℝ (yt-B s) sh).toLinearMap= _
    rw [det_rank_update _ hB]
    congr 1
    dsimp [yt]
    simp only [map_sub,map_add,map_smul,hv,inner_sub_right,inner_add_right,real_inner_smul_right]
    rw [hgs]
    dsimp [η]
    field_simp
    <;> ring
  have hdetle : θ*|LinearMap.det B.toLinearMap| ≤ |LinearMap.det Bu.toLinearMap| := by
    rw [hdet,abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (phi_det θ η hθ0 hθ1) (abs_nonneg (LinearMap.det B.toLinearMap))
  have hBu : IsUnit Bu := by
    apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
    apply (LinearMap.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    have hd : LinearMap.det B.toLinearMap ≠ 0 :=
      isUnit_iff_ne_zero.mp ((LinearMap.isUnit_iff_isUnit_det _).mp
        (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mp hB))
    exact abs_pos.mp (lt_of_lt_of_le (mul_pos hθ0 (abs_pos.mpr hd)) hdetle)
  have hnorm : ‖Bu‖+2 ≤ ((1+θ+τ)/τ)*(‖B‖+2) := by
    have hs0 : 0 ≤ ‖s‖ := norm_nonneg _
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
    have he : t • y+(1-t) • B s-B s=t • (y-B s) := by module
    have hupdate : Bu=B+(‖sh‖^2)⁻¹ • rankOne ℝ (t • (y-B s)) sh := by dsimp [Bu,yt];rw [hgs,he]
    have hn:=norm_add_le B ((‖sh‖^2)⁻¹ • rankOne ℝ (t • (y-B s)) sh)
    rw [← hupdate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hsh)),norm_rankOne,norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at hn
    have hdiff : ‖y-B s‖ ≤ (2+‖B‖)*‖s‖ := by
      have hh:=norm_sub_le y (B s)
      have hh':=B.le_opNorm s
      nlinarith
    have hmul : (‖sh‖^2)⁻¹*(t*‖y-B s‖*‖sh‖) ≤ (1+θ)/τ*(2+‖B‖) := by
      have hn' : (‖sh‖^2)⁻¹*(t*‖y-B s‖*‖sh‖)=t*‖y-B s‖/‖sh‖ := by field_simp <;> ring
      rw [hn']
      apply (div_le_iff₀ hsh).mpr
      have h1:=mul_le_mul_of_nonneg_left hdiff ht0.le
      have h2:=mul_le_mul_of_nonneg_right ht1 (mul_nonneg (by positivity : 0 ≤ 2+‖B‖) hs0)
      have h3:=mul_le_mul_of_nonneg_left hs (show 0 ≤ (1+θ)/τ*(2+‖B‖) by positivity)
      have hid : (1+θ)/τ*(2+‖B‖)*(τ*‖s‖)=(1+θ)*((2+‖B‖)*‖s‖) := by field_simp <;> ring
      rw [hid] at h3
      nlinarith
    have hid : ((1+θ+τ)/τ)*(‖B‖+2)=‖B‖+2+(1+θ)/τ*(2+‖B‖) := by field_simp <;> ring
    rw [hid]
    linarith
  have hq : 1-t+t*η ≠ 0 := by
    have h:=phi_det θ η hθ0 hθ1
    intro he
    change θ ≤ |1-t+t*η| at h
    rw [he,abs_zero] at h
    linarith
  have hden : ⟪sh,(Ring.inverse B) yt⟫=‖sh‖^2*(1-t+t*η) := by
    dsimp [yt]
    simp only [map_add,map_smul,hv,inner_add_right,real_inner_smul_right,hgs]
    dsimp [η]
    field_simp
    <;> ring
  exact ⟨hBu,hdetle,hnorm,inverse_update B hB s yt sh hwd (by rw [hden];exact mul_ne_zero (ne_of_gt (sq_pos_of_pos hsh)) hq) hBu⟩


private theorem run_invariants {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θ τ α D ε : ℝ) (m : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θ τ α D ε m x xt s y shat ytil H mem nAA)
    (hnosol : ∀ k,f (x k) ≠ x k) :
    ∀ k,mem k ≤ m ∧ mem k ≤ k ∧ (1 ≤ k → 1 ≤ mem k) ∧
      (∀ i ∈ Ico (k-mem k) k,∀ j ∈ Ico (k-mem k) k,i ≠ j → ⟪shat i,shat j⟫=0) ∧
      (∀ i ∈ Ico (k-mem k) k,shat i ≠ 0) ∧
      ∃ B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        IsUnit B ∧ H k=Ring.inverse B ∧
        ‖B‖+2 ≤ 3*((1+θ+τ)/τ)^(mem k) ∧ θ^(mem k) ≤ |LinearMap.det B.toLinearMap| := by
  classical
  let A := (1+θ+τ)/τ
  have hA : 1 ≤ A := (le_div_iff₀ hτ0).mpr (by linarith)
  have hgn (k : ℕ) : residual f (x k) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hnosol k))
  have hBH (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (hB : IsUnit B) (z : EuclideanSpace ℝ (Fin n)) : B ((Ring.inverse B) z)=z := by
    have he:=congrArg (fun C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => C z) (Ring.mul_inverse_cancel B hB)
    simpa using he
  intro k
  induction k with
  | zero =>
    rw [hrun.2.1]
    refine ⟨by omega,le_rfl,(by omega),(by simp),(by simp),1,isUnit_one,?_,?_,?_⟩
    · simpa using hrun.1
    · simp only [pow_zero,mul_one]
      have hh:=ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=EuclideanSpace ℝ (Fin n))
      change ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 at hh
      linarith
    · simp
  | succ k ih =>
    obtain ⟨hmk,hkk,hmp,ho,hn,B,hB,hHB,hBn,hBd⟩ := ih
    let I:=Ico (k-mem k) k
    let sg:=s k-∑ j ∈ I,(⟪shat j,s k⟫/⟪shat j,shat j⟫) • shat j
    let restart : Prop := mem k+1=m+1 ∨ ‖sg‖ < τ*‖s k‖
    let Hp := if restart then (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) else H k
    let t:=phiTheta θ (⟪shat k,Hp (y k)⟫/‖shat k‖^2)
    have hstep:=hrun.2.2.2.2.2 (k+1) (by omega)
    dsimp only at hstep
    simp only [Nat.add_sub_cancel,Nat.add_sub_add_right] at hstep
    change s k=xt (k+1)-x k ∧ y k=residual f (xt (k+1))-residual f (x k) ∧
      mem (k+1)=(if restart then 1 else mem k+1) ∧
      shat k=(if restart then s k else sg) ∧
      ytil k=(if mem (k+1)=1 then t • y k+(1-t) • s k else t • y k-(1-t) • residual f (x k)) ∧
      H (k+1)=Hp+⟪shat k,Hp (ytil k)⟫⁻¹ • ((rankOne ℝ (s k-Hp (ytil k)) (shat k)).comp Hp) ∧
      xt (k+1+1)=x (k+1)-H (k+1) (residual f (x (k+1))) ∧ _ at hstep
    obtain ⟨hs,hy,hmem,hsh,hyt,hH,hxt,htail⟩ := hstep
    have hsB (hk : 1 ≤ k) : B (s k)=-residual f (x k) := by
      have hxprev:xt (k+1)=x k-H k (residual f (x k)) := (hrun.2.2.2.2.2 k hk).2.2.2.2.2.2.1
      rw [hs,hxprev,hHB]
      have he : x k-(Ring.inverse B) (residual f (x k))-x k= -((Ring.inverse B) (residual f (x k))) := by module
      rw [he,map_neg,hBH B hB]
    have hsne : s k ≠ 0 := by
      by_cases hk : k=0
      · subst k
        have he : s 0= -α • residual f (x 0) := by
          rw [hs,hrun.2.2.2.2.1]
          unfold fAlpha AndersonAccel.Safe.residual
          module
        rw [he]
        exact smul_ne_zero (neg_ne_zero.mpr (ne_of_gt hα0)) (hgn 0)
      · intro hz
        have he:=hsB (by omega)
        rw [hz,map_zero] at he
        exact hgn k (neg_eq_zero.mp he.symm)
    have hynorm : ‖y k‖ ≤ 2*‖s k‖ := by
      rw [hy,hs]
      have hh:=hf.norm_sub_le (xt (k+1)) (x k)
      have he : residual f (xt (k+1))-residual f (x k)=(xt (k+1)-x k)-(f (xt (k+1))-f (x k)) := by unfold AndersonAccel.Safe.residual;module
      rw [he]
      have hb:=norm_sub_le (xt (k+1)-x k) (f (xt (k+1))-f (x k))
      norm_num at hh
      linarith
    let l:=if restart then 0 else mem k
    let Bp:=if restart then (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) else B
    have hl : l ≤ mem k := by dsimp [l];split_ifs <;> omega
    have hmnew : mem (k+1)=l+1 := by rw [hmem];dsimp [l];split_ifs <;> rfl
    have hBp : IsUnit Bp := by dsimp [Bp];split_ifs;exact isUnit_one;exact hB
    have hHp : Hp=Ring.inverse Bp := by dsimp [Hp,Bp];split_ifs <;> simp [hHB]
    have hBpnorm : ‖Bp‖+2 ≤ 3*A^l := by
      by_cases hr : restart
      · simp only [Bp,l,if_pos hr,pow_zero,mul_one]
        have hh:=ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=EuclideanSpace ℝ (Fin n))
        change ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 at hh
        linarith
      · simpa [Bp,l,hr,A] using hBn
    have hBpdet : θ^l ≤ |LinearMap.det Bp.toLinearMap| := by
      by_cases hr : restart
      · simp [Bp,l,hr]
      · simpa [Bp,l,hr] using hBd
    have hg := gs_local I shat (s k) ho hn
    have hgs : ⟪shat k,s k⟫=‖shat k‖^2 := by
      by_cases hr : restart
      · rw [hsh,if_pos hr,real_inner_self_eq_norm_sq]
      · simpa only [hsh,if_neg hr] using hg.2
    have hτs : τ*‖s k‖ ≤ ‖shat k‖ := by
      by_cases hr : restart
      · rw [hsh,if_pos hr];nlinarith [norm_nonneg (s k)]
      · rw [hsh,if_neg hr]
        exact le_of_not_gt (fun hh => hr (Or.inr hh))
    have hshne : shat k ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hτ0 (norm_pos_iff.mpr hsne)) hτs)
    have holdnew : ∀ i ∈ Ico (k-l) k,⟪shat i,shat k⟫=0 := by
      intro i hi
      by_cases hr : restart
      · simp [l,hr] at hi
      · rw [hsh,if_neg hr]
        exact hg.1 i (by simpa [l,hr,I] using hi)
    have hyt' : ytil k=t • y k+(1-t) • Bp (s k) := by
      rw [hyt]
      split_ifs with hm1
      · have hBpone : Bp=1 := by
          by_cases hr : restart
          · simp [Bp,hr]
          · have hmzero : mem k=0 := by simpa [hmem,hr] using hm1
            have hkzero : k=0 := by by_contra hk;have := hmp (by omega);omega
            have he : Ring.inverse B=1 := by rw [← hHB,hkzero,hrun.1]
            have he' := congrArg Ring.inverse he
            rw [Ring.inverse_inverse hB,Ring.inverse_one] at he'
            simpa [Bp,hr] using he'
        rw [hBpone,one_apply_eq_self]
      · have hnr : ¬ restart := by intro hr;apply hm1;simp [hmem,hr]
        have hkpos : 1 ≤ k := by
          by_contra hk
          have hk0 : k=0 := by omega
          subst k
          apply hm1
          rw [hmem,if_neg hnr,hrun.2.1]
        rw [show Bp=B by simp [Bp,hnr],hsB hkpos,smul_neg,sub_eq_add_neg]
    let Bu:=Bp+⟪shat k,s k⟫⁻¹ • rankOne ℝ (ytil k-Bp (s k)) (shat k)
    have hyt0 : ytil k=phiTheta θ (⟪shat k,(Ring.inverse Bp) (y k)⟫/‖shat k‖^2) • y k+
        (1-phiTheta θ (⟪shat k,(Ring.inverse Bp) (y k)⟫/‖shat k‖^2)) • Bp (s k) := by
      simpa only [t,hHp] using hyt'
    have hu:=update_bounds Bp hBp θ τ hθ0 hθ1 hτ0 (s k) (y k) (shat k) hsne hgs hynorm hτs
    dsimp only at hu
    rw [← hyt0] at hu
    change IsUnit Bu ∧ θ*|LinearMap.det Bp.toLinearMap| ≤ |LinearMap.det Bu.toLinearMap| ∧
      ‖Bu‖+2 ≤ A*(‖Bp‖+2) ∧ Ring.inverse Bu=Ring.inverse Bp+⟪shat k,(Ring.inverse Bp) (ytil k)⟫⁻¹ •
      ((rankOne ℝ (s k-(Ring.inverse Bp) (ytil k)) (shat k)).comp (Ring.inverse Bp)) at hu
    have hHnew : H (k+1)=Ring.inverse Bu := by rw [hH,hHp];exact hu.2.2.2.symm
    refine ⟨?_,?_,(by omega),?_,?_,Bu,hu.1,hHnew,?_,?_⟩
    · rw [hmnew]
      by_cases hr : restart
      · simp only [l,if_pos hr];omega
      · have hnr : mem k+1 ≠ m+1 := fun he => hr (Or.inl he)
        simp only [l,if_neg hr];omega
    · rw [hmnew];omega
    · intro i hi j hj hij
      rw [hmnew,Nat.add_sub_add_right] at hi hj
      have hil:=mem_Ico.mp hi
      have hjl:=mem_Ico.mp hj
      by_cases hik : i=k
      · subst i
        rw [← real_inner_comm]
        exact holdnew j (mem_Ico.mpr ⟨hjl.1,by omega⟩)
      · by_cases hjk : j=k
        · subst j;exact holdnew i (mem_Ico.mpr ⟨hil.1,by omega⟩)
        · exact ho i (mem_Ico.mpr ⟨by omega,by omega⟩) j (mem_Ico.mpr ⟨by omega,by omega⟩) hij
    · intro i hi
      rw [hmnew,Nat.add_sub_add_right] at hi
      obtain ⟨hil,hik⟩ := mem_Ico.mp hi
      by_cases he : i=k
      · simpa [he] using hshne
      · exact hn i (mem_Ico.mpr ⟨by omega,by omega⟩)
    · rw [hmnew,pow_succ]
      have hmul:=mul_le_mul_of_nonneg_left hBpnorm (le_trans zero_le_one hA)
      change ‖Bu‖+2 ≤ 3*(A^l*A)
      linarith [hu.2.2.1]
    · rw [hmnew,pow_succ]
      have hmul:=mul_le_mul_of_nonneg_left hBpdet hθ0.le
      linarith [hu.2.1]


theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hX : ∃ z, f z = z)
    (hnosol : ∀ k, f (x k) ≠ x k) :
    ∀ k, IsUnit (H k) ∧
      ‖H k‖ ≤ (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m ∧
      ‖H k‖ * ‖Ring.inverse (H k)‖ ≤ (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ n / θbar ^ m  := by
  intro k
  obtain ⟨hmk,hkk,hmp,ho,hn,B,hB,hHB,hBn,hBd⟩:=
    run_invariants f hf θbar τ α D ε m hθ0 hθ1 hτ0 hτ1 hα0 hm x xt s y shat ytil H mem nAA hrun hnosol k
  let A:=(1+θbar+τ)/τ
  let K:=3*A^m-2
  have hA : 1 ≤ A := (le_div_iff₀ hτ0).mpr (by linarith)
  have hK : 0 < K := by have := one_le_pow₀ hA (n:=m);dsimp [K];linarith
  have hnorm : ‖B‖ ≤ K := by
    have hp:=pow_le_pow_right₀ hA hmk
    change ‖B‖+2 ≤ 3*A^(mem k) at hBn
    dsimp [K];linarith
  have hdet : θbar^m ≤ |LinearMap.det B.toLinearMap| :=
    (pow_le_pow_of_le_one hθ0.le hθ1.le hmk).trans hBd
  have hbound:=inverse_norm_bound B hB K (θbar^m) hK (pow_pos hθ0 _) hnorm hdet
  have hnpos : 1 ≤ n := by
    by_contra hn
    have hn0 : n=0 := by omega
    subst n
    exact hnosol 0 (Subsingleton.elim _ _)
  rw [hHB]
  refine ⟨hB.ringInverse,hbound,?_⟩
  rw [Ring.inverse_inverse hB]
  calc
    ‖Ring.inverse B‖*‖B‖ ≤ (K^(n-1)/θbar^m)*K := mul_le_mul hbound hnorm (norm_nonneg _) (by positivity)
    _ = K^n/θbar^m := by
      rw [div_mul_eq_mul_div,← pow_succ,Nat.sub_add_cancel hnpos]
    _ = _ := rfl
