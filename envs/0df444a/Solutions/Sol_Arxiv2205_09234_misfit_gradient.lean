-- Prove2me | solution 1 for Arxiv2205_09234.misfit_gradient
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:51:24.683968+00:00
-- url     : https://prove2.me/submissions/d6a3ce56-a3f1-486e-bedd-9bad33ec4c52

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

set_option autoImplicit false

namespace S74MG
open Arxiv2205_09234

lemma omega_neg (N : ℕ) [NeZero N] (k j : Fin N) :
    dftMat N (-k) j = star (dftMat N k j) := by
  unfold dftMat
  rw [RCLike.star_def, ← Complex.exp_conj]
  by_cases hk : k = 0
  · subst hk; simp
  · have hkv : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    have hcoe : ((-k : Fin N) : ℕ) = N - k := by
      rw [Fin.coe_neg]
      exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
    rw [hcoe, Nat.cast_sub k.isLt.le]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have : -(2 * Real.pi * Complex.I * (((N : ℕ) : ℂ) - (k : ℕ)) * ((j : ℕ) : ℂ) / (N : ℂ)) =
        (-(j : ℕ) : ℤ) * (2 * Real.pi * Complex.I) +
          (starRingEnd ℂ) (-(2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))) := by
      simp only [map_neg, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast,
        map_ofNat]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

lemma coe_negk (N : ℕ) [NeZero N] (k : Fin N) (hkv : (k : ℕ) ≠ 0) :
    ((-k : Fin N) : ℕ) = N - k := by
  rw [Fin.coe_neg]
  exact Nat.mod_eq_of_lt (by have := k.isLt; omega)

lemma A_real (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (i j : Fin N) :
    (((dftMat N).conjTranspose * weightMat w * dftMat N) i j).im = 0 := by
  have : NeZero N := ⟨hN.ne'⟩
  have hwneg : ∀ k : Fin N, w (-k) = w k := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp
    · have hkv : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
      have hcoe : ((-k : Fin N) : ℕ) = N - k := coe_negk N k hkv
      have hkl := k.isLt
      have hf : |sampleFreq N dt (-k)| = |sampleFreq N dt k| := by
        by_cases heq : 2 * (k : ℕ) = N
        · have : -k = k := Fin.ext (by rw [hcoe]; omega)
          rw [this]
        · unfold sampleFreq
          rw [hcoe]
          by_cases h2 : 2 * (k : ℕ) < N
          · rw [if_neg (show ¬ (2 * (N - (k:ℕ)) < N) by omega), if_pos h2, Nat.cast_sub hkl.le,
              ← abs_neg]; congr 1; ring
          · rw [if_pos (show 2 * (N - (k:ℕ)) < N by omega), if_neg h2, Nat.cast_sub hkl.le,
              ← abs_neg]; congr 1; ring
      have hfk : sampleFreq N dt k ≠ 0 := by
        unfold sampleFreq
        have hNr : (0:ℝ) < N := by exact_mod_cast hN
        have hnum : (if 2 * (k : ℕ) < N then ((k : ℕ) : ℝ) else ((k : ℕ) : ℝ) - N) ≠ 0 := by
          split_ifs
          · exact_mod_cast hkv
          · have : ((k : ℕ) : ℝ) < N := by exact_mod_cast hkl
            linarith
        have : (0:ℝ) < N * dt := by positivity
        have hpi := Real.pi_pos
        intro h0
        rw [div_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · linarith
          · exact hnum h0
        · linarith
      have hfk' : sampleFreq N dt (-k) ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hf; exact hfk (abs_eq_zero.1 hf.symm)
      rw [hw.2 _ (Or.inl hfk'), hw.2 _ (Or.inl hfk), hf]
  have hentry : ((dftMat N).conjTranspose * weightMat w * dftMat N) i j =
      ∑ k, star (dftMat N k i) * (w k : ℂ) * dftMat N k j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold weightMat
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [hentry]
  set S := ∑ k, star (dftMat N k i) * (w k : ℂ) * dftMat N k j with hS
  have hSS : S = star S := by
    have h1 : S = ∑ k, star (dftMat N (-k) i) * (w (-k) : ℂ) * dftMat N (-k) j := by
      rw [hS]
      exact (Equiv.sum_comp (Equiv.neg (Fin N)) (fun k => star (dftMat N k i) * (w k : ℂ) * dftMat N k j)).symm
    conv_lhs => rw [h1]
    rw [hS, star_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [omega_neg, omega_neg, hwneg, star_star, star_mul, star_mul, star_star]
    simp only [RCLike.star_def, Complex.conj_ofReal]
    ring
  have := congrArg Complex.im hSS
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

lemma metric_sq (N : ℕ) (hN : 0 < N) (dt α : ℝ) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dm dobs : Fin N → ℝ) :
    ((discreteMetric N 2 w dm dobs ^ 2 : ℝ) : ℂ) =
      (fun j => ((dm j - dobs j : ℝ) : ℂ)) ⬝ᵥ ((dftMat N).conjTranspose * weightMat w * dftMat N).mulVec
        (fun j => ((dm j - dobs j : ℝ) : ℂ)) := by
  set rhat : Fin N → ℂ := fun k => dft N dm k - dft N dobs k with hrh
  set r : Fin N → ℂ := fun j => ((dm j - dobs j : ℝ) : ℂ) with hr
  have hrhat : rhat = (dftMat N).mulVec r := by
    funext k
    show dft N dm k - dft N dobs k = _
    have hd : ∀ (x : Fin N → ℝ), dft N x k = ∑ j, dftMat N k j * (x j : ℂ) := fun x => rfl
    rw [hd, hd, ← Finset.sum_sub_distrib]
    show _ = ∑ j, dftMat N k j * r j
    congr 1; funext j; simp only [r]; push_cast; ring
  have h1 : ((discreteMetric N 2 w dm dobs ^ 2 : ℝ) : ℂ) = star rhat ⬝ᵥ (weightMat w).mulVec rhat := by
    unfold discreteMetric
    have e : ∀ k, ‖rhat k‖ ^ (2:ℝ) = ‖rhat k‖ ^ (2:ℕ) := fun k => by
      exact_mod_cast Real.rpow_natCast _ 2
    simp only [rhat] at e
    simp only [e]
    have hnn : 0 ≤ ∑ k, w k * ‖dft N dm k - dft N dobs k‖ ^ 2 :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hw.1 k) (sq_nonneg _))
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
    push_cast
    unfold weightMat dotProduct
    congr 1; funext k
    rw [Matrix.mulVec_diagonal]
    simp only [Pi.star_apply, rhat]
    rw [← Complex.conj_mul']
    simp only [RCLike.star_def]
    ring
  rw [h1, hrhat, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hs : star r = r := by
    funext j; simp [r, Complex.conj_ofReal]
  rw [hs, Matrix.mul_assoc]

lemma A_symm (N : ℕ) (w : Fin N → ℝ) (i j : Fin N) :
    (((dftMat N).conjTranspose * weightMat w * dftMat N) j i).re =
      (((dftMat N).conjTranspose * weightMat w * dftMat N) i j).re := by
  have hH : ((dftMat N).conjTranspose * weightMat w * dftMat N).IsHermitian := by
    unfold Matrix.IsHermitian weightMat
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    have hst : (star fun k => ((w k : ℝ) : ℂ)) = fun k => ((w k : ℝ) : ℂ) := by
      funext k; simp
    rw [hst]
  rw [← hH.apply i j]
  simp

end S74MG

open Arxiv2205_09234 S74MG in
theorem solution (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dobs : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    let A : Matrix (Fin N) (Fin N) ℂ := (dftMat N).conjTranspose * weightMat w * dftMat N
    let r : Fin N → ℂ := fun j => ((x j - dobs j : ℝ) : ℂ)
    (∀ j, (A.mulVec r j).im = 0) ∧
      HasGradientAt
        (fun y : EuclideanSpace ℝ (Fin N) => discreteMetric N 2 w (fun j => y j) dobs ^ 2)
        (WithLp.toLp 2 (fun j => 2 * (A.mulVec r j).re)) x := by
  intro A r
  set B : Fin N → Fin N → ℝ := fun i j => (A i j).re with hB
  have hAr : ∀ i, A.mulVec r i = ((∑ j, B i j * (x j - dobs j) : ℝ) : ℂ) := by
    intro i
    apply Complex.ext
    · simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.ofReal_re, r, hB]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    · simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.ofReal_im, r]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        A_real N hN dt α hdt w hw i j, zero_mul]
  refine ⟨fun j => by rw [hAr]; exact Complex.ofReal_im _, ?_⟩
  have hf : (fun y : EuclideanSpace ℝ (Fin N) => discreteMetric N 2 w (fun j => y j) dobs ^ 2) =
      fun y => ∑ i, ∑ j, B i j * ((y i - dobs i) * (y j - dobs j)) := by
    funext y
    have h := metric_sq N hN dt α w hw (fun j => y j) dobs
    apply Complex.ofReal_injective
    rw [h]
    push_cast
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hij : A i j = ((B i j : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hB]
      · simp only [Complex.ofReal_im]; exact A_real N hN dt α hdt w hw i j
    rw [show (dftMat N).conjTranspose * weightMat w * dftMat N = A from rfl, hij]
    ring
  rw [hf, hasGradientAt_iff_hasFDerivAt]
  have hp : ∀ i : Fin N, HasFDerivAt (fun y : EuclideanSpace ℝ (Fin N) => y i - dobs i)
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) x :=
    fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).hasFDerivAt.sub_const _
  have hD := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((hp i).fun_mul (hp j)).const_mul (B i j)))
  refine hD.congr_fderiv ?_
  symm
  ext v
  rw [InnerProductSpace.toDual_apply_apply]
  have hpr : ∀ j, (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) v = v j := fun j => rfl
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, hpr]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, hAr, Complex.ofReal_re]
  have hsym : ∀ i j, B j i = B i j := fun i j => A_symm N w i j
  have e1 : ∑ i, ∑ j, B i j * ((x i - dobs i) * v j) = ∑ i, ∑ j, B i j * ((x j - dobs j) * v i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsym]
  have e2 : ∑ i, ∑ j, B i j * ((x i - dobs i) * v j + (x j - dobs j) * v i) =
      ∑ i, ∑ j, B i j * ((x i - dobs i) * v j) + ∑ i, ∑ j, B i j * ((x j - dobs j) * v i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [e2, e1, ← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring
