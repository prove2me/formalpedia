-- Prove2me | solution 1 for AdaGrad.Full.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:52:31.798055+00:00
-- url     : https://prove2.me/submissions/fc44ecf3-5f87-4683-bf97-05bc318cc8c9

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

theorem tr_mono {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    (S g t).trace ≤ (S g (t + 1)).trace := by
  have := (S_step_psd g t).trace_nonneg
  rw [Matrix.trace_sub] at this
  linarith

theorem tele {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T, ((S g (t + 1)).trace - (S g t).trace) = (S g T).trace - (S g 1).trace := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [Finset.sum_Ico_succ_top hT, ih]; ring

theorem solution {d : ℕ} (g x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T, ‖xstar - x (t + 1)‖ ^ 2 * ((S g (t + 1)).trace - (S g t).trace) ≤
      (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT) (fun t => ‖xstar - x t‖ ^ 2)
          * (S g T).trace
        - ‖xstar - x 1‖ ^ 2 * (S g 1).trace := by
  set M := (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT) (fun t => ‖xstar - x t‖ ^ 2) with hM
  have hle : ∀ t ∈ Finset.Icc 1 T, ‖xstar - x t‖ ^ 2 ≤ M := fun t ht =>
    Finset.le_sup' (fun t => ‖xstar - x t‖ ^ 2) ht
  have h1 : ∑ t ∈ Finset.Ico 1 T, ‖xstar - x (t + 1)‖ ^ 2 * ((S g (t + 1)).trace - (S g t).trace)
      ≤ ∑ t ∈ Finset.Ico 1 T, M * ((S g (t + 1)).trace - (S g t).trace) := by
    refine Finset.sum_le_sum fun t ht => ?_
    have ht' := Finset.mem_Ico.mp ht
    have := hle (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hm := tr_mono g t
    exact mul_le_mul_of_nonneg_right this (by linarith)
  rw [← Finset.mul_sum, tele g T hT] at h1
  have h2 : ‖xstar - x 1‖ ^ 2 ≤ M := hle 1 (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩)
  have h3 : 0 ≤ (S g 1).trace := (S_psd g 1).trace_nonneg
  nlinarith
