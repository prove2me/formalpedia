-- Prove2me | solution 1 for AdaGrad.Full.display_bregman_increment
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:50:53.597212+00:00
-- url     : https://prove2.me/submissions/919d2b09-e0c4-4da7-b021-c766d295589e

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2

set_option autoImplicit false
open scoped MatrixOrder InnerProductSpace
open Matrix AdaGrad.Full

theorem symm_swap {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (u w : Fin d → ℝ) : u ⬝ᵥ (M *ᵥ w) = (M *ᵥ u) ⬝ᵥ w := by
  have h : Mᵀ = M := by simpa using hM.eq
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

theorem psd_nonneg {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef)
    (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 v
  simpa using this

theorem sqrt_mono {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : (CFC.sqrt A - CFC.sqrt B).PosSemidef := by
  have hA : A.PosSemidef := by
    have := hAB.add hB
    simpa using this
  set P := CFC.sqrt A with hPdef
  set Q := CFC.sqrt B with hQdef
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hPP : P * P = A := CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have hQQ : Q * Q = B := CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB)
  have hXh : (P - Q).IsHermitian := hP.1.sub hQ.1
  refine hXh.posSemidef_iff_eigenvalues_nonneg.mpr ?_
  intro i
  show 0 ≤ hXh.eigenvalues i
  set X := P - Q with hX
  set lam := hXh.eigenvalues i with hlam
  set v : Fin d → ℝ := (hXh.eigenvectorBasis i).ofLp with hv
  have hXv : X *ᵥ v = lam • v := hXh.mulVec_eigenvectorBasis i
  have hn : 0 < v ⬝ᵥ v := by
    have hne : v ≠ 0 := by
      intro h
      have h1 : (hXh.eigenvectorBasis i) = 0 := by
        apply WithLp.ofLp_injective
        simpa [hv] using h
      exact (hXh.eigenvectorBasis.orthonormal.ne_zero i) h1
    exact lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg _)
      (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  by_contra hneg
  push Not at hneg
  set q := v ⬝ᵥ (Q *ᵥ v) with hq
  have hq0 : 0 ≤ q := psd_nonneg Q hQ v
  have hPQ : P = Q + X := by simp [hX]
  have F2 : 0 ≤ q + lam * (v ⬝ᵥ v) := by
    have := psd_nonneg P hP v
    rw [hPQ, Matrix.add_mulVec, dotProduct_add, hXv, dotProduct_smul, smul_eq_mul] at this
    exact this
  have F1 : 0 ≤ 2 * lam * q + lam ^ 2 * (v ⬝ᵥ v) := by
    have := psd_nonneg (A - B) hAB v
    have hAB' : A - B = Q * X + X * Q + X * X := by
      rw [← hPP, ← hQQ, hPQ]
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel
    rw [hAB', Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXv,
      Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul,
      symm_swap X hXh v (Q *ᵥ v), hXv, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      dotProduct_smul, smul_eq_mul] at this
    nlinarith
  nlinarith [mul_pos hn (neg_pos.mpr hneg)]

theorem outer_psd {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) : (outer g).PosSemidef := by
  have := Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp g)
  simpa [outer] using this

theorem G_psd {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : (G g t).PosSemidef := by
  induction t with
  | zero => simpa [G] using Matrix.PosSemidef.zero
  | succ t ih =>
    have : G g (t + 1) = G g t + outer (g (t + 1)) := by
      unfold G; rw [Finset.sum_Icc_succ_top (by omega)]
    rw [this]; exact ih.add (outer_psd _)

theorem G_step {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    G g (t + 1) - G g t = outer (g (t + 1)) := by
  unfold G; rw [Finset.sum_Icc_succ_top (by omega)]; abel

theorem S_psd {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : (S g t).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

theorem S_step_psd {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    (S g (t + 1) - S g t).PosSemidef := by
  have h := sqrt_mono (G g (t + 1)) (G g t) (G_psd g t) (by rw [G_step]; exact outer_psd _)
  exact h

theorem quad_le_trace {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosSemidef)
    (a : Fin d → ℝ) : a ⬝ᵥ (D *ᵥ a) ≤ (a ⬝ᵥ a) * D.trace := by
  set R := CFC.sqrt D with hRdef
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)
  have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D (Matrix.nonneg_iff_posSemidef.mpr hD)
  have hRh : R.IsHermitian := hR.1
  have e1 : a ⬝ᵥ (D *ᵥ a) = (R *ᵥ a) ⬝ᵥ (R *ᵥ a) := by
    rw [← hRR, ← Matrix.mulVec_mulVec, symm_swap R hRh a (R *ᵥ a)]
  have hsym : ∀ i j, R j i = R i j := fun i j => by
    have := hRh.apply i j
    simpa using this
  have e2 : D.trace = ∑ i, ∑ j, R i j ^ 2 := by
    rw [← hRR]
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym i j]; ring
  rw [e1, e2]
  unfold dotProduct
  calc ∑ i, (R *ᵥ a) i * (R *ᵥ a) i
      = ∑ i, ((R *ᵥ a) i) ^ 2 := Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i, (∑ j, R i j ^ 2) * (∑ j, a j ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => R i j) (fun j => a j)
        simpa [Matrix.mulVec, dotProduct] using this
    _ = (∑ j, a j * a j) * ∑ i, ∑ j, R i j ^ 2 := by
        rw [← Finset.sum_mul]
        rw [mul_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring

theorem mInner_add {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) (a b : EuclideanSpace ℝ (Fin d)) :
    mInner (M + N) a b = mInner M a b + mInner N a b := by
  unfold mInner; simp [map_add, inner_add_right]

theorem mInner_sub {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) (a b : EuclideanSpace ℝ (Fin d)) :
    mInner (M - N) a b = mInner M a b - mInner N a b := by
  unfold mInner; simp [map_sub, inner_sub_right]

theorem mInner_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (a : EuclideanSpace ℝ (Fin d)) :
    mInner M a a = a.ofLp ⬝ᵥ (M *ᵥ a.ofLp) := by
  unfold mInner
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp [Matrix.toLpLin_apply]

theorem norm_sq_eq' {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) : ‖a‖ ^ 2 = a.ofLp ⬝ᵥ a.ofLp := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem solution {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (xstar y : EuclideanSpace ℝ (Fin d)) :
    bregman (H δ g (t + 1)) xstar y - bregman (H δ g t) xstar y
        = 1 / 2 * mInner (S g (t + 1) - S g t) (xstar - y) (xstar - y) ∧
      1 / 2 * mInner (S g (t + 1) - S g t) (xstar - y) (xstar - y)
        ≤ 1 / 2 * ‖xstar - y‖ ^ 2 * (S g (t + 1) - S g t).trace := by
  refine ⟨?_, ?_⟩
  · unfold bregman H
    rw [mInner_add, mInner_add, mInner_sub]
    ring
  · rw [mInner_eq, norm_sq_eq']
    have := quad_le_trace _ (S_step_psd g t) (xstar - y).ofLp
    nlinarith
