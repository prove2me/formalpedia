-- Prove2me | solution 1 for Arxiv2205_09423.single_particle_amplitude_rotation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T11:25:33.70036+00:00
-- url     : https://prove2.me/submissions/c46de75e-cca8-4b07-906b-bd92138f4b1e

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open Matrix

noncomputable section

namespace ROT
open Arxiv2205_09423

lemma rotM_zero : rotM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, one_apply]

lemma signedAngle_self (eth ek : Fin 3 → ℝ) (h : dotProduct eth eth = 1) :
    signedAngle eth eth ek = 0 := by
  unfold signedAngle
  have hc : crossProduct eth eth = 0 := cross_self eth
  have hC : (⟨dotProduct eth eth, dotProduct (crossProduct eth eth) ek⟩ : ℂ) = 1 := by
    apply Complex.ext <;> simp [h, hc]
  rw [hC, Complex.arg_one]

lemma eq_of_unit_parallel {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hj : dotProduct uj uj = 1)
    (hanti : uj ≠ -ui) (hcr : crossProduct ui uj = 0) :
    uj = ui := by
  have h0 : crossProduct ui (crossProduct ui uj) = 0 := by simp [hcr]
  have hexp := cross_cross_eq_smul_sub_smul' ui ui uj
  have hsub : (dotProduct ui uj) • ui - uj = 0 := by
    have : (dotProduct ui uj) • ui - (dotProduct ui ui) • uj = 0 := by
      simpa [h0] using hexp.symm
    rwa [hi, one_smul] at this
  have hmul : uj = (dotProduct ui uj) • ui :=
    (sub_eq_zero.mp hsub).symm
  have ht : (dotProduct ui uj) ^ 2 = 1 := by
    have hvv := congrArg (fun v => dotProduct v v) hmul
    rw [hj] at hvv
    simpa [smul_dotProduct, dotProduct_smul, hi, smul_eq_mul, mul_one, sq] using hvv.symm
  have ht1 : dotProduct ui uj = 1 ∨ dotProduct ui uj = -1 :=
    sq_eq_one_iff.mp ht
  rcases ht1 with h1 | h1
  · rw [hmul, h1, one_smul]
  · rw [hmul, h1, neg_one_smul] at hanti
    exact (hanti rfl).elim

lemma eParIn_of_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj = 0) :
    eParIn ui uj = eTheta ui := by
  simp [eParIn, hcr]

lemma eParOut_of_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj = 0) :
    eParOut ui uj = eTheta uj := by
  simp [eParOut, hcr]

lemma ePerp_of_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj = 0) :
    ePerp ui uj = ePhi ui := by
  simp [ePerp, hcr]

lemma dotProduct_self_nonneg' (v : Fin 3 → ℝ) : 0 ≤ dotProduct v v := by
  simp [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

lemma vnorm_sq (v : Fin 3 → ℝ) : vnorm v ^ 2 = dotProduct v v := by
  unfold vnorm
  exact Real.sq_sqrt (dotProduct_self_nonneg' v)

lemma vnorm_eq_zero_iff (v : Fin 3 → ℝ) : vnorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have : dotProduct v v = 0 := by
      have := congrArg (fun x => x ^ 2) h
      simpa [vnorm_sq] using this
    have hsum : ∑ i : Fin 3, v i ^ 2 = 0 := by
      simpa [dotProduct, sq] using this
    ext i
    have hi : v i ^ 2 ≤ ∑ j : Fin 3, v j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have : v i ^ 2 = 0 := le_antisymm (hi.trans_eq hsum) (sq_nonneg _)
    exact sq_eq_zero_iff.mp this
  · intro h; simp [vnorm, h]

lemma vnorm_smul (c : ℝ) (v : Fin 3 → ℝ) : vnorm (c • v) = |c| * vnorm v := by
  unfold vnorm
  have : dotProduct (c • v) (c • v) = c ^ 2 * dotProduct v v := by
    simp [dotProduct_smul, smul_dotProduct, smul_eq_mul, sq]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma vnorm_normalize {v : Fin 3 → ℝ} (hv : v ≠ 0) : vnorm (Arxiv2205_09423.normalize v) = 1 := by
  unfold Arxiv2205_09423.normalize
  have hn : vnorm v ≠ 0 := (vnorm_eq_zero_iff v).not.mpr hv
  rw [vnorm_smul, abs_inv, abs_of_nonneg (by unfold vnorm; exact Real.sqrt_nonneg _),
    inv_mul_cancel₀ hn]

lemma zhat_cross (e : Fin 3 → ℝ) :
    crossProduct zhat e = ![-(e 1), e 0, 0] := by
  ext i; fin_cases i <;> simp [zhat, cross_apply]

lemma ePhi_unit (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    dotProduct (ePhi e) (ePhi e) = 1 := by
  unfold ePhi
  split_ifs with h hz
  · simp [dotProduct, Fin.sum_univ_three]
  · simp [dotProduct, Fin.sum_univ_three]
  · have hne : crossProduct zhat e ≠ 0 := by
      intro hc
      rw [zhat_cross] at hc
      have : e 0 = 0 ∧ e 1 = 0 := by
        have h0 := congr_fun hc 0
        have h1 := congr_fun hc 1
        simp at h0 h1
        exact ⟨h1, h0⟩
      exact h this
    have hn := vnorm_normalize hne
    have : vnorm (Arxiv2205_09423.normalize (crossProduct zhat e)) ^ 2 = 1 := by
      rw [hn, one_pow]
    rw [vnorm_sq] at this
    exact this

lemma ePhi_orthogonal (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    dotProduct (ePhi e) e = 0 := by
  unfold ePhi
  split_ifs with h hz
  · -- e 0 = e 1 = 0, ePhi = ŷ, e = ![0,0,e2], ŷ·e = 0
    have : e 0 = 0 ∧ e 1 = 0 := h
    simp [dotProduct, Fin.sum_univ_three, this]
  · have : e 0 = 0 ∧ e 1 = 0 := h
    simp [dotProduct, Fin.sum_univ_three, this]
  · -- normalize (zhat ⨯ e) · e = (zhat ⨯ e) · e / |zhat ⨯ e| = 0
    have hne : crossProduct zhat e ≠ 0 := by
      intro hc
      rw [zhat_cross] at hc
      have : e 0 = 0 ∧ e 1 = 0 := by
        have h0 := congr_fun hc 0
        have h1 := congr_fun hc 1
        simp at h0 h1
        exact ⟨h1, h0⟩
      exact h this
    unfold Arxiv2205_09423.normalize
    simp [smul_dotProduct, smul_eq_mul]
    have : dotProduct (crossProduct zhat e) e = 0 := by
      rw [dotProduct_comm]
      exact dot_cross_self zhat e
    simp [this]

lemma eTheta_unit (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    dotProduct (eTheta e) (eTheta e) = 1 := by
  unfold eTheta
  have hφ := ePhi_unit e he
  have hor := ePhi_orthogonal e he
  have hne : crossProduct (ePhi e) e ≠ 0 := by
    intro hc
    have hnorm : dotProduct (crossProduct (ePhi e) e) (crossProduct (ePhi e) e) = 0 := by
      simp [hc]
    have : dotProduct (ePhi e) (ePhi e) * dotProduct e e -
        dotProduct (ePhi e) e * dotProduct e (ePhi e) = 0 := by
      simpa [cross_dot_cross] using hnorm
    simp [hφ, he, hor, dotProduct_comm] at this
  have hn := vnorm_normalize hne
  have : vnorm (Arxiv2205_09423.normalize (crossProduct (ePhi e) e)) ^ 2 = 1 := by
    rw [hn, one_pow]
  rwa [vnorm_sq] at this

lemma rotM_mul_one (t : ℝ) : rotM t * (1 : Matrix (Fin 2) (Fin 2) ℂ) = rotM t := by
  simp

lemma sigmaZ_sq : sigmaZ * sigmaZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, one_apply]


lemma reduce_eq_sigmaZ_amp_of_eq (X : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℝ) :
    reduce X u u = sigmaZ * ampScatPlane X u u * sigmaZ := by
  have hIn : eParIn u u = eTheta u := eParIn_of_parallel (cross_self u)
  have hOut : eParOut u u = eTheta u := eParOut_of_parallel (cross_self u)
  have hP : ePerp u u = ePhi u := ePerp_of_parallel (cross_self u)
  ext m n
  fin_cases m <;> fin_cases n
  all_goals
    simp [reduce, ampScatPlane, polarBasis, sigmaZ, hIn, hOut, hP, Matrix.mul_apply,
      Matrix.of_apply, cons_val_zero, cons_val_one, Fin.sum_univ_three]
    try abel

lemma parallel_case (X : Fin 3 → Fin 3 → ℂ) {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hj : dotProduct uj uj = 1)
    (hanti : uj ≠ -ui) (hcr : crossProduct ui uj = 0) :
    reduce X ui uj =
      rotM (-signedAngle (eTheta uj) (eParOut ui uj) uj) * sigmaZ * ampScatPlane X ui uj *
        sigmaZ * rotM (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  have huj : uj = ui := eq_of_unit_parallel hi hj hanti hcr
  rw [huj]
  have hθi : signedAngle (eTheta ui) (eParIn ui ui) ui = 0 := by
    rw [eParIn_of_parallel (cross_self ui)]
    exact signedAngle_self _ _ (eTheta_unit ui hi)
  have hθj : signedAngle (eTheta ui) (eParOut ui ui) ui = 0 := by
    rw [eParOut_of_parallel (cross_self ui)]
    exact signedAngle_self _ _ (eTheta_unit ui hi)
  rw [hθi, hθj, rotM_zero, neg_zero, rotM_zero, Matrix.mul_one, Matrix.one_mul]
  exact reduce_eq_sigmaZ_amp_of_eq X ui

lemma ePerp_of_not_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    ePerp ui uj = Arxiv2205_09423.normalize (crossProduct ui uj) := by
  simp [ePerp, hcr]

lemma ePerp_unit {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePerp ui uj) (ePerp ui uj) = 1 := by
  rw [ePerp_of_not_parallel hcr, ← vnorm_sq, vnorm_normalize hcr, one_pow]

lemma eParIn_of_not_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    eParIn ui uj = crossProduct (ePerp ui uj) ui := by
  simp [eParIn, hcr]

lemma eParOut_of_not_parallel {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    eParOut ui uj = crossProduct (ePerp ui uj) uj := by
  simp [eParOut, hcr]

lemma eParIn_dot_ePerp {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParIn ui uj) (ePerp ui uj) = 0 := by
  rw [eParIn_of_not_parallel hcr]
  -- (ePerp ⨯ ui) · ePerp = 0
  have := dot_self_cross (ePerp ui uj) ui
  rw [dotProduct_comm]
  simpa using this

lemma eParIn_dot_ui {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParIn ui uj) ui = 0 := by
  rw [eParIn_of_not_parallel hcr, dotProduct_comm]
  exact dot_cross_self (ePerp ui uj) ui

lemma eParIn_unit {ui uj : Fin 3 → ℝ} (hi : dotProduct ui ui = 1)
    (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParIn ui uj) (eParIn ui uj) = 1 := by
  rw [eParIn_of_not_parallel hcr]
  have hor : dotProduct (ePerp ui uj) ui = 0 := by
    rw [ePerp_of_not_parallel hcr]
    unfold Arxiv2205_09423.normalize
    simp [smul_dotProduct, smul_eq_mul]
    have : dotProduct (crossProduct ui uj) ui = 0 := by
      rw [dotProduct_comm]
      exact dot_self_cross ui uj
    simp [this]
  have : dotProduct (crossProduct (ePerp ui uj) ui) (crossProduct (ePerp ui uj) ui) =
      dotProduct (ePerp ui uj) (ePerp ui uj) * dotProduct ui ui -
        dotProduct (ePerp ui uj) ui * dotProduct ui (ePerp ui uj) :=
    cross_dot_cross (ePerp ui uj) ui (ePerp ui uj) ui
  rw [this, ePerp_unit hcr, hi, hor]
  simp


lemma ePerp_dot_ui {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePerp ui uj) ui = 0 := by
  rw [ePerp_of_not_parallel hcr]
  unfold Arxiv2205_09423.normalize
  simp [smul_dotProduct, smul_eq_mul]
  have : dotProduct (crossProduct ui uj) ui = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross ui uj
  simp [this]

lemma ePerp_dot_uj {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePerp ui uj) uj = 0 := by
  rw [ePerp_of_not_parallel hcr]
  unfold Arxiv2205_09423.normalize
  simp [smul_dotProduct, smul_eq_mul]
  have : dotProduct (crossProduct ui uj) uj = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self ui uj
  simp [this]

lemma eParOut_dot_ePerp {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParOut ui uj) (ePerp ui uj) = 0 := by
  rw [eParOut_of_not_parallel hcr, dotProduct_comm]
  exact dot_self_cross (ePerp ui uj) uj

lemma eParOut_dot_uj {ui uj : Fin 3 → ℝ} (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParOut ui uj) uj = 0 := by
  rw [eParOut_of_not_parallel hcr, dotProduct_comm]
  exact dot_cross_self (ePerp ui uj) uj

lemma eParOut_unit {ui uj : Fin 3 → ℝ} (hj : dotProduct uj uj = 1)
    (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eParOut ui uj) (eParOut ui uj) = 1 := by
  rw [eParOut_of_not_parallel hcr]
  have this := cross_dot_cross (ePerp ui uj) uj (ePerp ui uj) uj
  rw [this, ePerp_unit hcr, hj, ePerp_dot_uj hcr]
  simp

lemma vnorm_ePhi_cross_e (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    vnorm (crossProduct (ePhi e) e) = 1 := by
  have hsq : vnorm (crossProduct (ePhi e) e) ^ 2 = 1 := by
    rw [vnorm_sq, cross_dot_cross, ePhi_unit e he, he, ePhi_orthogonal e he]
    simp [dotProduct_comm]
  have hnn : 0 ≤ vnorm (crossProduct (ePhi e) e) := by
    unfold vnorm; exact Real.sqrt_nonneg _
  have hcases := sq_eq_one_iff.mp hsq
  rcases hcases with h | h
  · exact h
  · linarith

lemma eTheta_eq_cross (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    eTheta e = crossProduct (ePhi e) e := by
  unfold eTheta Arxiv2205_09423.normalize
  rw [vnorm_ePhi_cross_e e he, inv_one, one_smul]

lemma eTheta_dot_e (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    dotProduct (eTheta e) e = 0 := by
  rw [eTheta_eq_cross e he, dotProduct_comm]
  exact dot_cross_self (ePhi e) e

lemma eTheta_dot_ePhi (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    dotProduct (eTheta e) (ePhi e) = 0 := by
  rw [eTheta_eq_cross e he, dotProduct_comm]
  exact dot_self_cross (ePhi e) e

lemma cross_anticomm (u v : Fin 3 → ℝ) : crossProduct u v = - crossProduct v u := by
  ext k
  fin_cases k <;> simp [cross_apply] <;> ring

lemma e_eq_eTheta_cross_ePhi (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    e = crossProduct (eTheta e) (ePhi e) := by
  rw [eTheta_eq_cross e he]
  have h := cross_cross_eq_smul_sub_smul' (ePhi e) (ePhi e) e
  rw [cross_anticomm, h, ePhi_unit e he, ePhi_orthogonal e he]
  simp [one_smul]

lemma triad_parseval {p q k v : Fin 3 → ℝ}
    (hp : dotProduct p p = 1) (hq : dotProduct q q = 1) (hk : dotProduct k k = 1)
    (hpq : dotProduct p q = 0) (hpk : dotProduct p k = 0) (hqk : dotProduct q k = 0) :
    (dotProduct v p) ^ 2 + (dotProduct v q) ^ 2 + (dotProduct v k) ^ 2 = dotProduct v v := by
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![p 0, p 1, p 2; q 0, q 1, q 2; k 0, k 1, k 2]
  have hqp : dotProduct q p = 0 := by rw [dotProduct_comm]; exact hpq
  have hkp : dotProduct k p = 0 := by rw [dotProduct_comm]; exact hpk
  have hkq : dotProduct k q = 0 := by rw [dotProduct_comm]; exact hqk
  have hMT : M * M.transpose = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hp
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hpq
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hpk
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hqp
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hq
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hqk
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hkp
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hkq
    · simpa [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
        dotProduct] using hk
  letI : Invertible M.transpose := invertibleOfLeftInverse M.transpose M hMT
  have hTM : M.transpose * M = 1 := mul_invOf_self M.transpose
  have hpvec : (![p 0, p 1, p 2] : Fin 3 → ℝ) = p := by ext t; fin_cases t <;> rfl
  have hqvec : (![q 0, q 1, q 2] : Fin 3 → ℝ) = q := by ext t; fin_cases t <;> rfl
  have hkvec : (![k 0, k 1, k 2] : Fin 3 → ℝ) = k := by ext t; fin_cases t <;> rfl
  have hcol : ∀ i j : Fin 3, p i * p j + q i * q j + k i * k j = if i = j then 1 else 0 := by
    intro i j
    have hij := congr_fun (congr_fun hTM i) j
    simp [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
      hpvec, hqvec, hkvec] at hij
    exact hij
  have hexp :
      (dotProduct v p) ^ 2 + (dotProduct v q) ^ 2 + (dotProduct v k) ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (p i * p j + q i * q j + k i * k j) := by
    simp [dotProduct, Fin.sum_univ_three, pow_two]
    ring
  rw [hexp]
  have hδ :
      ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (p i * p j + q i * q j + k i * k j) =
        ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * (if i = j then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hcol]
  rw [hδ]
  simp [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, dotProduct, Fin.sum_univ_three, pow_two]

lemma eq_zero_of_dot_self {v : Fin 3 → ℝ} (h : dotProduct v v = 0) : v = 0 := by
  have hsum : ∑ i : Fin 3, v i ^ 2 = 0 := by simpa [dotProduct, sq] using h
  ext i
  have hi : v i ^ 2 ≤ ∑ j : Fin 3, v j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have : v i ^ 2 = 0 := le_antisymm (hi.trans_eq hsum) (sq_nonneg _)
  exact sq_eq_zero_iff.mp this

lemma decomp_in_plane {p q k v : Fin 3 → ℝ}
    (hp : dotProduct p p = 1) (hq : dotProduct q q = 1) (hk : dotProduct k k = 1)
    (hpq : dotProduct p q = 0) (hpk : dotProduct p k = 0) (hqk : dotProduct q k = 0)
    (hvk : dotProduct v k = 0) :
    v = (dotProduct v p) • p + (dotProduct v q) • q := by
  set w := v - (dotProduct v p) • p - (dotProduct v q) • q
  have hwp : dotProduct w p = 0 := by
    simp [w, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hp, hpq, dotProduct_comm]
  have hwq : dotProduct w q = 0 := by
    simp [w, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hq, hpq, dotProduct_comm]
  have hwk : dotProduct w k = 0 := by
    simp [w, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hpk, hqk, dotProduct_comm, hvk]
    -- leftover may be k·v = 0
    try (rw [dotProduct_comm]; exact hvk)
  have hwparse := triad_parseval (v := w) hp hq hk hpq hpk hqk
  have hwsq : dotProduct w w = 0 := by
    simpa [hwp, hwq, hwk] using hwparse.symm
  have hw0 : w = 0 := eq_zero_of_dot_self hwsq
  have hw' : v - (dotProduct v p) • p - (dotProduct v q) • q = 0 := by
    simpa [w] using hw0
  rw [sub_sub, sub_eq_zero] at hw'
  exact hw'

lemma eq_smul_of_cross_eq_zero {v n : Fin 3 → ℝ}
    (hn : dotProduct n n = 1) (h : crossProduct v n = 0) :
    v = (dotProduct v n) • n := by
  have hexp := cross_cross_eq_smul_sub_smul' n n v
  have hL : crossProduct n (crossProduct n v) = 0 := by
    have : crossProduct n v = - crossProduct v n := cross_anticomm n v
    simp [this, h]
  have h' : (dotProduct n v) • n - (dotProduct n n) • v = 0 := by
    rw [← hexp, hL]
  rw [hn, one_smul, sub_eq_zero] at h'
  have hcomm : dotProduct n v = dotProduct v n := dotProduct_comm _ _
  rw [hcomm] at h'
  exact h'.symm

lemma cross_parallel_to_normal {eth epar ek : Fin 3 → ℝ}
    (hek : dotProduct ek ek = 1)
    (h1k : dotProduct eth ek = 0) (h2k : dotProduct epar ek = 0) :
    crossProduct eth epar = (dotProduct (crossProduct eth epar) ek) • ek := by
  have hcross : crossProduct (crossProduct eth epar) ek = 0 := by
    rw [cross_anticomm]
    have hcc := cross_cross_eq_smul_sub_smul' ek eth epar
    rw [hcc]
    have h1 : dotProduct ek eth = 0 := by rw [dotProduct_comm]; exact h1k
    have h2 : dotProduct ek epar = 0 := by rw [dotProduct_comm]; exact h2k
    rw [h2, h1k, zero_smul, zero_smul, sub_zero, neg_zero]
  exact eq_smul_of_cross_eq_zero hek hcross

lemma signedAngle_normSq {eth epar ek : Fin 3 → ℝ}
    (h1 : dotProduct eth eth = 1) (h2 : dotProduct epar epar = 1)
    (hek : dotProduct ek ek = 1)
    (h1k : dotProduct eth ek = 0) (h2k : dotProduct epar ek = 0) :
    Complex.normSq (⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩ : ℂ) = 1 := by
  have hpar := cross_parallel_to_normal hek h1k h2k
  have hcr : dotProduct (crossProduct eth epar) (crossProduct eth epar) =
      1 - (dotProduct eth epar) ^ 2 := by
    have hcc := cross_dot_cross eth epar eth epar
    have hcomm : dotProduct epar eth = dotProduct eth epar := dotProduct_comm _ _
    rw [hcc, h1, h2, one_mul, hcomm]
    ring
  have hIm : (dotProduct (crossProduct eth epar) ek) ^ 2 =
      1 - (dotProduct eth epar) ^ 2 := by
    have hnorm := congrArg (fun v => dotProduct v v) hpar
    have hs : dotProduct ((dotProduct (crossProduct eth epar) ek) • ek)
        ((dotProduct (crossProduct eth epar) ek) • ek) =
        (dotProduct (crossProduct eth epar) ek) ^ 2 * (dotProduct ek ek) := by
      simp [smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two]
      ring
    rw [hs, hek, mul_one] at hnorm
    linarith
  rw [Complex.normSq_mk]
  linarith

lemma signedAngle_ne_zero {eth epar ek : Fin 3 → ℝ}
    (h1 : dotProduct eth eth = 1) (h2 : dotProduct epar epar = 1)
    (hek : dotProduct ek ek = 1)
    (h1k : dotProduct eth ek = 0) (h2k : dotProduct epar ek = 0) :
    (⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩ : ℂ) ≠ 0 := by
  intro hz
  have hz0 : Complex.normSq (⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩ : ℂ) = 0 := by
    simp [hz]
  have := signedAngle_normSq h1 h2 hek h1k h2k
  linarith

lemma norm_eq_one_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, h]
  have hnn : 0 ≤ ‖z‖ := norm_nonneg z
  rcases (sq_eq_one_iff.mp this) with h' | h'
  · exact h'
  · linarith

lemma signedAngle_cos {eth epar ek : Fin 3 → ℝ}
    (h1 : dotProduct eth eth = 1) (h2 : dotProduct epar epar = 1)
    (hek : dotProduct ek ek = 1)
    (h1k : dotProduct eth ek = 0) (h2k : dotProduct epar ek = 0) :
    Real.cos (signedAngle eth epar ek) = dotProduct eth epar := by
  unfold signedAngle
  set z : ℂ := ⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩
  have hz : z ≠ 0 := signedAngle_ne_zero h1 h2 hek h1k h2k
  have hn : ‖z‖ = 1 := norm_eq_one_of_normSq (signedAngle_normSq h1 h2 hek h1k h2k)
  have hcos := Complex.cos_arg hz
  rw [hcos, hn]
  simp [z]

lemma signedAngle_sin {eth epar ek : Fin 3 → ℝ}
    (h1 : dotProduct eth eth = 1) (h2 : dotProduct epar epar = 1)
    (hek : dotProduct ek ek = 1)
    (h1k : dotProduct eth ek = 0) (h2k : dotProduct epar ek = 0) :
    Real.sin (signedAngle eth epar ek) = dotProduct (crossProduct eth epar) ek := by
  unfold signedAngle
  set z : ℂ := ⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩
  have hn : ‖z‖ = 1 := norm_eq_one_of_normSq (signedAngle_normSq h1 h2 hek h1k h2k)
  have hsin := Complex.sin_arg z
  rw [hsin, hn]
  simp [z]

lemma scalar_triple (a b c : Fin 3 → ℝ) :
    dotProduct (crossProduct a b) c = dotProduct a (crossProduct b c) := by
  simp [dotProduct, cross_apply, Fin.sum_univ_three]
  ring

lemma eParIn_cross_ui {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    crossProduct (eParIn ui uj) ui = - ePerp ui uj := by
  rw [eParIn_of_not_parallel hcr, cross_anticomm]
  have hcc := cross_cross_eq_smul_sub_smul' ui (ePerp ui uj) ui
  have hor : dotProduct ui (ePerp ui uj) = 0 := by rw [dotProduct_comm]; exact ePerp_dot_ui hcr
  rw [hcc, hi, ePerp_dot_ui hcr, one_smul, zero_smul, sub_zero]

lemma ePhi_eq_cross (e : Fin 3 → ℝ) (he : dotProduct e e = 1) :
    ePhi e = crossProduct e (eTheta e) := by
  rw [eTheta_eq_cross e he]
  have hcc := cross_cross_eq_smul_sub_smul' e (ePhi e) e
  have hor : dotProduct e (ePhi e) = 0 := by rw [dotProduct_comm]; exact ePhi_orthogonal e he
  rw [hcc, he, ePhi_orthogonal e he, one_smul, zero_smul, sub_zero]

lemma eTheta_dot_eParIn_eq_cos {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eTheta ui) (eParIn ui uj) =
      Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  exact (signedAngle_cos (eTheta_unit ui hi) (eParIn_unit hi hcr) hi
    (eTheta_dot_e ui hi) (eParIn_dot_ui hcr)).symm

lemma eTheta_dot_ePerp_eq_neg_sin {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eTheta ui) (ePerp ui uj) =
      - Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  have hsin := signedAngle_sin (eTheta_unit ui hi) (eParIn_unit hi hcr) hi
    (eTheta_dot_e ui hi) (eParIn_dot_ui hcr)
  have hst := scalar_triple (eTheta ui) (eParIn ui uj) ui
  have : Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) =
      dotProduct (eTheta ui) (crossProduct (eParIn ui uj) ui) := by
    rw [← hst, hsin]
  rw [eParIn_cross_ui hi hcr] at this
  have hneg : dotProduct (eTheta ui) (- ePerp ui uj) =
      - dotProduct (eTheta ui) (ePerp ui uj) := by
    simp [dotProduct, Pi.neg_apply, Fin.sum_univ_three]
  linarith

lemma eTheta_decomp {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    eTheta ui =
      Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • eParIn ui uj +
        (- Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui)) • ePerp ui uj := by
  have hdec := decomp_in_plane (eParIn_unit hi hcr) (ePerp_unit hcr) hi
    (eParIn_dot_ePerp hcr) (eParIn_dot_ui hcr) (ePerp_dot_ui hcr) (eTheta_dot_e ui hi)
  have hc := eTheta_dot_eParIn_eq_cos hi hcr
  have hs := eTheta_dot_ePerp_eq_neg_sin hi hcr
  calc eTheta ui
      = (dotProduct (eTheta ui) (eParIn ui uj)) • eParIn ui uj +
          (dotProduct (eTheta ui) (ePerp ui uj)) • ePerp ui uj := hdec
    _ = Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • eParIn ui uj +
          (- Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui)) • ePerp ui uj := by
        rw [hc, hs]

lemma eParIn_cross_ePerp {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    crossProduct (eParIn ui uj) (ePerp ui uj) = ui := by
  rw [eParIn_of_not_parallel hcr, cross_anticomm]
  have hcc := cross_cross_eq_smul_sub_smul' (ePerp ui uj) (ePerp ui uj) ui
  -- ePerp ⨯ (ePerp ⨯ ui) = (ePerp·ui) ePerp - (ePerp·ePerp) ui = -ui
  -- so (ePerp ⨯ ui) ⨯ ePerp = ui
  rw [hcc, ePerp_dot_ui hcr, ePerp_unit hcr, zero_smul, one_smul, zero_sub, neg_neg]

lemma ePhi_dot_eParIn_eq_sin {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePhi ui) (eParIn ui uj) =
      Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  rw [ePhi_eq_cross ui hi]
  have hst := scalar_triple ui (eTheta ui) (eParIn ui uj)
  have hsin := signedAngle_sin (eTheta_unit ui hi) (eParIn_unit hi hcr) hi
    (eTheta_dot_e ui hi) (eParIn_dot_ui hcr)
  have hcomm : dotProduct (crossProduct (eTheta ui) (eParIn ui uj)) ui =
      dotProduct ui (crossProduct (eTheta ui) (eParIn ui uj)) :=
    dotProduct_comm _ _
  rw [hst, ← hcomm, hsin]

lemma ePhi_dot_ePerp_eq_cos {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePhi ui) (ePerp ui uj) =
      Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  rw [ePhi_eq_cross ui hi]
  have hst := scalar_triple ui (eTheta ui) (ePerp ui uj)
  rw [hst]
  -- ui · (eθ ⨯ ePerp) ; expand eθ
  have hth := eTheta_decomp hi hcr
  have hcross : crossProduct (eTheta ui) (ePerp ui uj) =
      Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • ui := by
    nth_rw 1 [hth]
    have hlin : crossProduct
        (Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • eParIn ui uj +
          (- Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui)) • ePerp ui uj)
        (ePerp ui uj) =
        Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) •
          crossProduct (eParIn ui uj) (ePerp ui uj) +
          (- Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui)) •
            crossProduct (ePerp ui uj) (ePerp ui uj) := by
      ext i
      simp [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      try ring
    rw [hlin, eParIn_cross_ePerp hi hcr, cross_self, smul_zero, add_zero]
  rw [hcross]
  simp [smul_dotProduct, smul_eq_mul, hi]

lemma ePhi_decomp {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) :
    ePhi ui =
      Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) • eParIn ui uj +
        Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • ePerp ui uj := by
  have hdec := decomp_in_plane (eParIn_unit hi hcr) (ePerp_unit hcr) hi
    (eParIn_dot_ePerp hcr) (eParIn_dot_ui hcr) (ePerp_dot_ui hcr) (ePhi_orthogonal ui hi)
  have hs := ePhi_dot_eParIn_eq_sin hi hcr
  have hc := ePhi_dot_ePerp_eq_cos hi hcr
  calc ePhi ui
      = (dotProduct (ePhi ui) (eParIn ui uj)) • eParIn ui uj +
          (dotProduct (ePhi ui) (ePerp ui uj)) • ePerp ui uj := hdec
    _ = Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) • eParIn ui uj +
          Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) • ePerp ui uj := by
        rw [hs, hc]

lemma eParOut_cross_uj {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    crossProduct (eParOut ui uj) uj = - ePerp ui uj := by
  rw [eParOut_of_not_parallel hcr, cross_anticomm]
  have hcc := cross_cross_eq_smul_sub_smul' uj (ePerp ui uj) uj
  rw [hcc, hj, ePerp_dot_uj hcr, one_smul, zero_smul, sub_zero]

lemma eTheta_dot_eParOut_eq_cos {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eTheta uj) (eParOut ui uj) =
      Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) := by
  exact (signedAngle_cos (eTheta_unit uj hj) (eParOut_unit hj hcr) hj
    (eTheta_dot_e uj hj) (eParOut_dot_uj hcr)).symm

lemma eTheta_dot_ePerp_out_eq_neg_sin {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (eTheta uj) (ePerp ui uj) =
      - Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) := by
  have hsin := signedAngle_sin (eTheta_unit uj hj) (eParOut_unit hj hcr) hj
    (eTheta_dot_e uj hj) (eParOut_dot_uj hcr)
  have hst := scalar_triple (eTheta uj) (eParOut ui uj) uj
  have : Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) =
      dotProduct (eTheta uj) (crossProduct (eParOut ui uj) uj) := by
    rw [← hst, hsin]
  rw [eParOut_cross_uj hj hcr] at this
  have hneg : dotProduct (eTheta uj) (- ePerp ui uj) =
      - dotProduct (eTheta uj) (ePerp ui uj) := by
    simp [dotProduct, Pi.neg_apply, Fin.sum_univ_three]
  linarith

lemma eTheta_out_decomp {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    eTheta uj =
      Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • eParOut ui uj +
        (- Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj)) • ePerp ui uj := by
  have hdec := decomp_in_plane (eParOut_unit hj hcr) (ePerp_unit hcr) hj
    (eParOut_dot_ePerp hcr) (eParOut_dot_uj hcr) (ePerp_dot_uj hcr) (eTheta_dot_e uj hj)
  have hc := eTheta_dot_eParOut_eq_cos hj hcr
  have hs := eTheta_dot_ePerp_out_eq_neg_sin hj hcr
  calc eTheta uj
      = (dotProduct (eTheta uj) (eParOut ui uj)) • eParOut ui uj +
          (dotProduct (eTheta uj) (ePerp ui uj)) • ePerp ui uj := hdec
    _ = Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • eParOut ui uj +
          (- Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj)) • ePerp ui uj := by
        rw [hc, hs]

lemma eParOut_cross_ePerp {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    crossProduct (eParOut ui uj) (ePerp ui uj) = uj := by
  rw [eParOut_of_not_parallel hcr, cross_anticomm]
  have hcc := cross_cross_eq_smul_sub_smul' (ePerp ui uj) (ePerp ui uj) uj
  rw [hcc, ePerp_dot_uj hcr, ePerp_unit hcr, zero_smul, one_smul, zero_sub, neg_neg]

lemma ePhi_dot_eParOut_eq_sin {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePhi uj) (eParOut ui uj) =
      Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) := by
  rw [ePhi_eq_cross uj hj]
  have hst := scalar_triple uj (eTheta uj) (eParOut ui uj)
  have hsin := signedAngle_sin (eTheta_unit uj hj) (eParOut_unit hj hcr) hj
    (eTheta_dot_e uj hj) (eParOut_dot_uj hcr)
  have hcomm : dotProduct (crossProduct (eTheta uj) (eParOut ui uj)) uj =
      dotProduct uj (crossProduct (eTheta uj) (eParOut ui uj)) :=
    dotProduct_comm _ _
  rw [hst, ← hcomm, hsin]

lemma ePhi_dot_ePerp_out_eq_cos {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    dotProduct (ePhi uj) (ePerp ui uj) =
      Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) := by
  rw [ePhi_eq_cross uj hj]
  have hst := scalar_triple uj (eTheta uj) (ePerp ui uj)
  rw [hst]
  have hth := eTheta_out_decomp hj hcr
  have hcross : crossProduct (eTheta uj) (ePerp ui uj) =
      Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • uj := by
    nth_rw 1 [hth]
    have hlin : crossProduct
        (Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • eParOut ui uj +
          (- Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj)) • ePerp ui uj)
        (ePerp ui uj) =
        Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) •
          crossProduct (eParOut ui uj) (ePerp ui uj) +
          (- Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj)) •
            crossProduct (ePerp ui uj) (ePerp ui uj) := by
      ext i
      simp [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      try ring
    rw [hlin, eParOut_cross_ePerp hj hcr, cross_self, smul_zero, add_zero]
  rw [hcross]
  simp [smul_dotProduct, smul_eq_mul, hj]

lemma ePhi_out_decomp {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) :
    ePhi uj =
      Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) • eParOut ui uj +
        Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • ePerp ui uj := by
  have hdec := decomp_in_plane (eParOut_unit hj hcr) (ePerp_unit hcr) hj
    (eParOut_dot_ePerp hcr) (eParOut_dot_uj hcr) (ePerp_dot_uj hcr) (ePhi_orthogonal uj hj)
  have hs := ePhi_dot_eParOut_eq_sin hj hcr
  have hc := ePhi_dot_ePerp_out_eq_cos hj hcr
  calc ePhi uj
      = (dotProduct (ePhi uj) (eParOut ui uj)) • eParOut ui uj +
          (dotProduct (ePhi uj) (ePerp ui uj)) • ePerp ui uj := hdec
    _ = Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) • eParOut ui uj +
          Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) • ePerp ui uj := by
        rw [hs, hc]

lemma eTheta_apply {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) (a : Fin 3) :
    eTheta ui a =
      Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) * eParIn ui uj a +
        (-Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui)) * ePerp ui uj a := by
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congr_fun (eTheta_decomp hi hcr) a

lemma ePhi_apply {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) (a : Fin 3) :
    ePhi ui a =
      Real.sin (signedAngle (eTheta ui) (eParIn ui uj) ui) * eParIn ui uj a +
        Real.cos (signedAngle (eTheta ui) (eParIn ui uj) ui) * ePerp ui uj a := by
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congr_fun (ePhi_decomp hi hcr) a

lemma eTheta_out_apply {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) (a : Fin 3) :
    eTheta uj a =
      Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) * eParOut ui uj a +
        (-Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj)) * ePerp ui uj a := by
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congr_fun (eTheta_out_decomp hj hcr) a

lemma ePhi_out_apply {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) (a : Fin 3) :
    ePhi uj a =
      Real.sin (signedAngle (eTheta uj) (eParOut ui uj) uj) * eParOut ui uj a +
        Real.cos (signedAngle (eTheta uj) (eParOut ui uj) uj) * ePerp ui uj a := by
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congr_fun (ePhi_out_decomp hj hcr) a

lemma rotM_neg (t : ℝ) :
    rotM (-t) =
      !![(Real.cos t : ℂ), (-(Real.sin t) : ℂ); ((Real.sin t) : ℂ), (Real.cos t : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Real.cos_neg, Real.sin_neg]

lemma ofReal_linear (c s : ℝ) (u v : Fin 3 → ℝ) (a : Fin 3) :
    ((c * u a + s * v a : ℝ) : ℂ) = (c : ℂ) * (u a : ℂ) + (s : ℂ) * (v a : ℂ) := by
  simp [Complex.ofReal_add, Complex.ofReal_mul]

lemma mul_sigmaZ_rot (t : ℝ) (q n : Fin 2) :
    (sigmaZ * rotM t) q n = sigmaZ q q * rotM t q n := by
  fin_cases q <;> fin_cases n <;>
    simp [Matrix.mul_apply, sigmaZ, rotM, Fin.sum_univ_two]

lemma rotM_transpose (t : ℝ) (i j : Fin 2) : rotM (-t) i j = rotM t j i := by
  fin_cases i <;> fin_cases j <;> simp [rotM, Real.cos_neg, Real.sin_neg]

lemma polar_in_coord {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hcr : crossProduct ui uj ≠ 0) (n : Fin 2) (a : Fin 3) :
    (polarBasis ui n a : ℂ) =
      ∑ q : Fin 2, (sigmaZ * rotM (signedAngle (eTheta ui) (eParIn ui uj) ui)) q n *
        ((![eParIn ui uj, -ePerp ui uj] q a : ℝ) : ℂ) := by
  set θi := signedAngle (eTheta ui) (eParIn ui uj) ui
  fin_cases n
  · -- eθ
    simp [polarBasis, Matrix.mul_apply, sigmaZ, rotM, Fin.sum_univ_two,
      cons_val_zero, cons_val_one]
    have h := eTheta_apply hi hcr a
    have hC : (eTheta ui a : ℂ) =
        ((Real.cos θi * eParIn ui uj a + (-Real.sin θi) * ePerp ui uj a : ℝ) : ℂ) := by
      simp [θi, h]
    rw [hC, ofReal_linear, Complex.ofReal_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  · -- eφ
    simp [polarBasis, Matrix.mul_apply, sigmaZ, rotM, Fin.sum_univ_two,
      cons_val_zero, cons_val_one]
    have h := ePhi_apply hi hcr a
    have hC : (ePhi ui a : ℂ) =
        ((Real.sin θi * eParIn ui uj a + Real.cos θi * ePerp ui uj a : ℝ) : ℂ) := by
      simp [θi, h]
    rw [hC, ofReal_linear, Complex.ofReal_cos, Complex.ofReal_sin]
    try ring

lemma polar_out_coord {ui uj : Fin 3 → ℝ}
    (hj : dotProduct uj uj = 1) (hcr : crossProduct ui uj ≠ 0) (m : Fin 2) (a : Fin 3) :
    (polarBasis uj m a : ℂ) =
      ∑ p : Fin 2, (sigmaZ * rotM (signedAngle (eTheta uj) (eParOut ui uj) uj)) p m *
        ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ) := by
  set θj := signedAngle (eTheta uj) (eParOut ui uj) uj
  fin_cases m
  · simp [polarBasis, Matrix.mul_apply, sigmaZ, rotM, Fin.sum_univ_two,
      cons_val_zero, cons_val_one]
    have h := eTheta_out_apply hj hcr a
    have hC : (eTheta uj a : ℂ) =
        ((Real.cos θj * eParOut ui uj a + (-Real.sin θj) * ePerp ui uj a : ℝ) : ℂ) := by
      simp [θj, h]
    rw [hC, ofReal_linear, Complex.ofReal_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  · simp [polarBasis, Matrix.mul_apply, sigmaZ, rotM, Fin.sum_univ_two,
      cons_val_zero, cons_val_one]
    have h := ePhi_out_apply hj hcr a
    have hC : (ePhi uj a : ℂ) =
        ((Real.sin θj * eParOut ui uj a + Real.cos θj * ePerp ui uj a : ℝ) : ℂ) := by
      simp [θj, h]
    rw [hC, ofReal_linear, Complex.ofReal_cos, Complex.ofReal_sin]
    try ring

lemma sum_bilinear_factor (A : Fin 2 → ℂ) (B : Fin 2 → ℂ) (Y : ℂ) :
    (∑ p : Fin 2, A p) * Y * (∑ q : Fin 2, B q) =
      ∑ p : Fin 2, ∑ q : Fin 2, A p * Y * B q := by
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, Fin.sum_univ_two]
  ring

lemma sum4_comm (f : Fin 2 → Fin 2 → Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ p : Fin 2, ∑ q : Fin 2, f p q a b) =
      (∑ p : Fin 2, ∑ q : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, f p q a b) := by
  simp [Fin.sum_univ_two, Fin.sum_univ_three]
  abel

lemma general_case (X : Fin 3 → Fin 3 → ℂ) {ui uj : Fin 3 → ℝ}
    (hi : dotProduct ui ui = 1) (hj : dotProduct uj uj = 1)
    (hcr : crossProduct ui uj ≠ 0) :
    reduce X ui uj =
      rotM (-signedAngle (eTheta uj) (eParOut ui uj) uj) * sigmaZ * ampScatPlane X ui uj *
        sigmaZ * rotM (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  set θi := signedAngle (eTheta ui) (eParIn ui uj) ui
  set θj := signedAngle (eTheta uj) (eParOut ui uj) uj
  ext m n
  -- reduce_mn = ∑_ab ↑(polar_out m a) * X a b * ↑(polar_in n b)
  have hred : reduce X ui uj m n =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (polarBasis uj m a : ℂ) * X a b * (polarBasis ui n b : ℂ) := by
    simp [reduce, Matrix.of_apply]
  -- substitute polar coords
  have hswap :
      reduce X ui uj m n =
        ∑ p : Fin 2, ∑ q : Fin 2,
          (sigmaZ * rotM θj) p m * ampScatPlane X ui uj p q * (sigmaZ * rotM θi) q n := by
    rw [hred]
    -- replace polar coords
    simp only [θi, θj]
    have hin := fun b => polar_in_coord hi hcr n b
    have hout := fun a => polar_out_coord hj hcr m a
    -- ∑_ab (∑_p Qj_p m * Sout_p a) * X ab * (∑_q Qi_q n * Sin_q b)
    -- = ∑_pq Qj_p m * Qi_q n * (∑_ab Sout_p a * X ab * Sin_q b)
    -- = ∑_pq Qj_p m * amp_pq * Qi_q n
    calc
      ∑ a : Fin 3, ∑ b : Fin 3,
          (polarBasis uj m a : ℂ) * X a b * (polarBasis ui n b : ℂ)
        = ∑ a : Fin 3, ∑ b : Fin 3,
            (∑ p : Fin 2, (sigmaZ * rotM θj) p m *
              ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ)) *
            X a b *
            (∑ q : Fin 2, (sigmaZ * rotM θi) q n *
              ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ)) := by
          simp only [θi, θj]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [polar_out_coord hj hcr m a, polar_in_coord hi hcr n b]
      _ = ∑ p : Fin 2, ∑ q : Fin 2,
            (sigmaZ * rotM θj) p m * ampScatPlane X ui uj p q * (sigmaZ * rotM θi) q n := by
          have hbil : ∀ a b,
              (∑ p : Fin 2, (sigmaZ * rotM θj) p m *
                  ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ)) *
                X a b *
              (∑ q : Fin 2, (sigmaZ * rotM θi) q n *
                  ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ)) =
                ∑ p : Fin 2, ∑ q : Fin 2,
                  ((sigmaZ * rotM θj) p m *
                    ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ)) *
                  X a b *
                  ((sigmaZ * rotM θi) q n *
                    ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ)) := by
            intro a b
            simpa [mul_assoc] using
              sum_bilinear_factor
                (fun p => (sigmaZ * rotM θj) p m *
                  ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ))
                (fun q => (sigmaZ * rotM θi) q n *
                  ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ))
                (X a b)
          simp_rw [hbil]
          -- move p,q outside: ∑ a, ∑ b, ∑ p, ∑ q  =  ∑ p, ∑ q, ∑ a, ∑ b
          have hcomm :=
            sum4_comm (fun p q a b =>
              ((sigmaZ * rotM θj) p m *
                ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ)) *
              X a b *
              ((sigmaZ * rotM θi) q n *
                ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ)))
          rw [hcomm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          -- factor Qp, Qq (independent of a,b) out of the a,b sums
          -- ∑_a ∑_b (Qp * Sout_pa) * Xab * (Qq * Sin_qb) = Qp * amp_pq * Qq
          have hfact :
              (∑ a : Fin 3, ∑ b : Fin 3,
                ((sigmaZ * rotM θj) p m *
                  ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ)) *
                X a b *
                ((sigmaZ * rotM θi) q n *
                  ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ))) =
              (sigmaZ * rotM θj) p m *
                (∑ a : Fin 3, ∑ b : Fin 3,
                  ((![eParOut ui uj, -ePerp ui uj] p a : ℝ) : ℂ) * X a b *
                    ((![eParIn ui uj, -ePerp ui uj] q b : ℝ) : ℂ)) *
                (sigmaZ * rotM θi) q n := by
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
            ring
          rw [hfact]
          simp [ampScatPlane, Matrix.of_apply]
  rw [hswap]
  -- RHS_mn = ∑_{p q} rotM(-θj) m p * (σz * amp * σz) p q * rotM(θi) q n
  -- (σz * amp * σz) p q = σz p p * amp p q * σz q q
  -- (σz * rotM θj) p m = σz p p * rotM θj p m = σz p p * rotM (-θj) m p
  have hL : ∀ p, (sigmaZ * rotM θj) p m = rotM (-θj) m p * sigmaZ p p := by
    intro p
    rw [mul_sigmaZ_rot, rotM_transpose]
    ring
  have hR : ∀ q, (sigmaZ * rotM θi) q n = sigmaZ q q * rotM θi q n :=
    fun q => mul_sigmaZ_rot θi q n
  have hB : ∀ p q, (sigmaZ * ampScatPlane X ui uj * sigmaZ) p q =
      sigmaZ p p * ampScatPlane X ui uj p q * sigmaZ q q := by
    intro p q
    simp [Matrix.mul_apply, sigmaZ, Fin.sum_univ_two]
    fin_cases p <;> fin_cases q <;> simp [sigmaZ] <;> ring
  -- assemble
  have hRHS :
      (rotM (-θj) * sigmaZ * ampScatPlane X ui uj * sigmaZ * rotM θi) m n =
        ∑ p : Fin 2, ∑ q : Fin 2,
          rotM (-θj) m p * sigmaZ p p * ampScatPlane X ui uj p q * sigmaZ q q * rotM θi q n := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases m <;> fin_cases n <;> simp [sigmaZ, Fin.sum_univ_two] <;> ring
  -- compare
  simp only [θi, θj] at hswap hL hR hB hRHS ⊢
  rw [hRHS]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hL, hR]
  ring

end ROT

open ROT Arxiv2205_09423

theorem solution (X : Fin 3 → Fin 3 → ℂ) (ui uj : Fin 3 → ℝ)
    (hi : dotProduct ui ui = 1) (hj : dotProduct uj uj = 1) (hanti : uj ≠ -ui) :
    reduce X ui uj =
      rotM (-signedAngle (eTheta uj) (eParOut ui uj) uj) * sigmaZ * ampScatPlane X ui uj *
        sigmaZ * rotM (signedAngle (eTheta ui) (eParIn ui uj) ui) := by
  by_cases hcr : crossProduct ui uj = 0
  · exact parallel_case X hi hj hanti hcr
  · exact general_case X hi hj hcr
