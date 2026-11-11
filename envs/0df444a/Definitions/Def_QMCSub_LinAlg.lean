-- Prove2me | Definitions.Def_QMCSub_LinAlg
-- name    : QMCSub_LinAlg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:01:19.8954+00:00
-- url     : https://prove2.me/theorems/2f33b798-0601-4e0c-8adc-0a074fc3c628
-- title:
--   Trace inequalities for positive semidefinite matrices and the matrix power lemma
-- statement:
--   Facts about real positive semidefinite $n\times n$ matrices, used to analyse a subgradient method for the Max-Cut semidefinite relaxation.
--
--   - For $A,B\succeq0$: $0\le\operatorname{tr}(AB)\le\operatorname{tr}(A)\operatorname{tr}(B)$.
--   - An even power of a symmetric matrix is positive semidefinite, and every power of a positive semidefinite matrix with positive trace has positive trace.
--   - **Power lemma.** If $M,X\succeq0$, $0<\delta<1$ and $n(1-\delta)^{2K}\le\delta$, then
--   $$(1-\delta)\operatorname{tr}(MX)\operatorname{tr}(M^{2K})\le(1+\delta)\operatorname{tr}(M^{2K+1})\operatorname{tr}(X).$$
--   - Entries of a positive semidefinite matrix with unit diagonal lie in $[-1,1]$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib

/-!
Real positive-semidefinite matrix facts used by the subgradient analysis.
-/

namespace QMCSub
open Matrix

variable {n : ℕ}

/-- Spectral decomposition of a real positive semidefinite matrix, in plain matrix form. -/
theorem exists_spectral_psd {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ M = U * diagonal d * Uᴴ ∧ ∀ i, 0 ≤ d i := by
  refine ⟨(hM.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), hM.1.eigenvalues, ?_, ?_, ?_,
    hM.eigenvalues_nonneg⟩
  · simpa [star_eq_conjTranspose] using Unitary.coe_star_mul_self hM.1.eigenvectorUnitary
  · simpa [star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.1.eigenvectorUnitary
  · have h := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [star_eq_conjTranspose] using h

/-- Powers of a unitarily conjugated matrix. -/
theorem conj_pow {U : Matrix (Fin n) (Fin n) ℝ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (m : ℕ) :
    (U * D * Uᴴ) ^ m = U * D ^ m * Uᴴ := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hU']
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc U * D ^ m * Uᴴ * (U * D * Uᴴ) = U * D ^ m * (Uᴴ * U) * D * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (D ^ m * D) * Uᴴ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U]

/-- The trace is invariant under unitary conjugation. -/
theorem trace_conj {U : Matrix (Fin n) (Fin n) ℝ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᴴ * U = 1) : (U * D * Uᴴ).trace = D.trace := by
  rw [trace_mul_cycle, hU, Matrix.one_mul]

/-- The trace of a power, in terms of the eigenvalues. -/
theorem trace_conj_pow {U : Matrix (Fin n) (Fin n) ℝ} (d : Fin n → ℝ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (m : ℕ) :
    ((U * diagonal d * Uᴴ) ^ m).trace = ∑ i, d i ^ m := by
  rw [conj_pow _ hU hU', trace_conj _ hU, diagonal_pow, trace_diagonal]
  rfl

/-- The trace against another matrix, in terms of the eigenvalues. -/
theorem trace_conj_mul {U : Matrix (Fin n) (Fin n) ℝ} (d : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (U * diagonal d * Uᴴ * B).trace = ∑ i, d i * (Uᴴ * B * U) i i := by
  have h : U * diagonal d * Uᴴ * B = (U * diagonal d) * (Uᴴ * B) := by
    simp only [Matrix.mul_assoc]
  rw [h, trace_mul_comm, ← Matrix.mul_assoc, trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, mul_diagonal, mul_comm]

/-- The trace of a conjugate by the inverse unitary. -/
theorem trace_conj' {U : Matrix (Fin n) (Fin n) ℝ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hU' : U * Uᴴ = 1) : B.trace = ∑ i, (Uᴴ * B * U) i i := by
  have h : (Uᴴ * B * U).trace = B.trace := by rw [trace_mul_cycle, hU', Matrix.one_mul]
  rw [← h]
  rfl

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem psd_trace_mul_nonneg {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨U, d, hU, hU', rfl, hd⟩ := exists_spectral_psd hA
  rw [trace_conj_mul]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hd i) (hB.conjTranspose_mul_mul_same U).diag_nonneg

/-- `tr(AB) ≤ tr(A) tr(B)` for positive semidefinite `A`, `B`. -/
theorem psd_trace_mul_le {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A * B).trace ≤ A.trace * B.trace := by
  obtain ⟨U, d, hU, hU', rfl, hd⟩ := exists_spectral_psd hA
  have hc : ∀ i, 0 ≤ (Uᴴ * B * U) i i := fun i =>
    (hB.conjTranspose_mul_mul_same U).diag_nonneg
  rw [trace_conj_mul, trace_conj _ hU, trace_diagonal, trace_conj' B hU', Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun j => (Uᴴ * B * U) j j) (fun j _ => hc j) (Finset.mem_univ i))
    (hd i)

/-- An even power of a symmetric real matrix is positive semidefinite. -/
theorem psd_even_pow {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (K : ℕ) :
    (M ^ (2 * K)).PosSemidef := by
  have h : M ^ (2 * K) = (M ^ K)ᴴ * M ^ K := by
    rw [(hM.pow K).eq, two_mul, pow_add]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

/-- Powers of a positive semidefinite matrix with positive trace have positive trace. -/
theorem psd_pow_trace_pos {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (h : 0 < M.trace) (m : ℕ) : 0 < (M ^ m).trace := by
  obtain ⟨U, d, hU, hU', rfl, hd⟩ := exists_spectral_psd hM
  rw [trace_conj _ hU, trace_diagonal] at h
  rw [trace_conj_pow d hU hU']
  obtain ⟨i, hi⟩ : ∃ i, 0 < d i := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd h (not_lt.mpr (Finset.sum_nonpos fun i _ => hcon i))
  calc (0 : ℝ) < d i ^ m := pow_pos hi m
    _ ≤ ∑ j, d j ^ m :=
      Finset.single_le_sum (f := fun j => d j ^ m) (fun j _ => pow_nonneg (hd j) m)
        (Finset.mem_univ i)

/-- The scalar (eigenvalue) form of the matrix-power lemma. -/
theorem scalar_power_lemma (d c : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (hc : ∀ i, 0 ≤ c i)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (K : ℕ)
    (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ) :
    (1 - δ) * (∑ i, d i * c i) * (∑ i, d i ^ (2 * K)) ≤
      (1 + δ) * (∑ i, d i ^ (2 * K + 1)) * (∑ i, c i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hL0 : 0 ≤ d i0 := hd i0
  have hle : ∀ i, d i ≤ d i0 := fun i => hi0 i (Finset.mem_univ i)
  have hC : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have h1δ : 0 < 1 - δ := by linarith
  have hT : 0 ≤ (1 - δ) * d i0 := mul_nonneg h1δ.le hL0
  -- Step a: `∑ d c ≤ Λ ∑ c`.
  have ha : ∑ i, d i * c i ≤ d i0 * ∑ i, c i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hc i)
  -- Step b: termwise scalar bound.
  have hb1 : ∀ i, (1 - δ) * d i0 * d i ^ (2 * K) ≤
      d i ^ (2 * K + 1) + ((1 - δ) * d i0) ^ (2 * K + 1) := by
    intro i
    have hdi := hd i
    have hpow : 0 ≤ d i ^ (2 * K) := pow_nonneg hdi _
    rcases le_total ((1 - δ) * d i0) (d i) with h | h
    · have h1 : (1 - δ) * d i0 * d i ^ (2 * K) ≤ d i * d i ^ (2 * K) :=
        mul_le_mul_of_nonneg_right h hpow
      have h2 : d i * d i ^ (2 * K) = d i ^ (2 * K + 1) := by ring
      have h3 : 0 ≤ ((1 - δ) * d i0) ^ (2 * K + 1) := pow_nonneg hT _
      linarith
    · have h0 : d i ^ (2 * K) ≤ ((1 - δ) * d i0) ^ (2 * K) := pow_le_pow_left₀ hdi h _
      have h2 : (1 - δ) * d i0 * d i ^ (2 * K) ≤
          (1 - δ) * d i0 * ((1 - δ) * d i0) ^ (2 * K) := mul_le_mul_of_nonneg_left h0 hT
      have h3 : (1 - δ) * d i0 * ((1 - δ) * d i0) ^ (2 * K) =
          ((1 - δ) * d i0) ^ (2 * K + 1) := by ring
      have h4 : 0 ≤ d i ^ (2 * K + 1) := pow_nonneg hdi _
      linarith
  have hS1 : d i0 ^ (2 * K + 1) ≤ ∑ i, d i ^ (2 * K + 1) :=
    Finset.single_le_sum (f := fun i => d i ^ (2 * K + 1))
      (fun i _ => pow_nonneg (hd i) _) (Finset.mem_univ i0)
  have hb2 : (1 - δ) * d i0 * ∑ i, d i ^ (2 * K) ≤
      ∑ i, d i ^ (2 * K + 1) + (n : ℝ) * ((1 - δ) * d i0) ^ (2 * K + 1) := by
    rw [Finset.mul_sum]
    calc ∑ i, (1 - δ) * d i0 * d i ^ (2 * K)
        ≤ ∑ i, (d i ^ (2 * K + 1) + ((1 - δ) * d i0) ^ (2 * K + 1)) :=
          Finset.sum_le_sum fun i _ => hb1 i
      _ = ∑ i, d i ^ (2 * K + 1) + (n : ℝ) * ((1 - δ) * d i0) ^ (2 * K + 1) := by
          rw [Finset.sum_add_distrib]; simp
  have hLp : 0 ≤ d i0 ^ (2 * K + 1) := pow_nonneg hL0 _
  have hb3 : (n : ℝ) * ((1 - δ) * d i0) ^ (2 * K + 1) ≤ δ * d i0 ^ (2 * K + 1) := by
    have e : (n : ℝ) * ((1 - δ) * d i0) ^ (2 * K + 1) =
        ((n : ℝ) * (1 - δ) ^ (2 * K)) * ((1 - δ) * d i0 ^ (2 * K + 1)) := by
      rw [mul_pow, pow_succ (1 - δ)]; ring
    rw [e]
    calc ((n : ℝ) * (1 - δ) ^ (2 * K)) * ((1 - δ) * d i0 ^ (2 * K + 1))
        ≤ δ * ((1 - δ) * d i0 ^ (2 * K + 1)) :=
          mul_le_mul_of_nonneg_right hK (mul_nonneg h1δ.le hLp)
      _ ≤ δ * d i0 ^ (2 * K + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hδ0.le
          have : δ * d i0 ^ (2 * K + 1) ≥ 0 := mul_nonneg hδ0.le hLp
          linarith
  have hb : (1 - δ) * d i0 * ∑ i, d i ^ (2 * K) ≤ (1 + δ) * ∑ i, d i ^ (2 * K + 1) := by
    have h5 := mul_le_mul_of_nonneg_left hS1 hδ0.le
    linarith
  -- Combine.
  have hP : 0 ≤ ∑ i, d i ^ (2 * K) := Finset.sum_nonneg fun i _ => pow_nonneg (hd i) _
  calc (1 - δ) * (∑ i, d i * c i) * (∑ i, d i ^ (2 * K))
      ≤ (1 - δ) * (d i0 * ∑ i, c i) * (∑ i, d i ^ (2 * K)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha h1δ.le) hP
    _ = ((1 - δ) * d i0 * ∑ i, d i ^ (2 * K)) * ∑ i, c i := by ring
    _ ≤ ((1 + δ) * ∑ i, d i ^ (2 * K + 1)) * ∑ i, c i := mul_le_mul_of_nonneg_right hb hC
    _ = (1 + δ) * (∑ i, d i ^ (2 * K + 1)) * (∑ i, c i) := by ring

/-- The matrix-power lemma: the density `M^(2K)/tr(M^(2K))` nearly maximizes `tr(M ·)`. -/
theorem power_lemma {M X : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) (hX : X.PosSemidef)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (K : ℕ)
    (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ) :
    (1 - δ) * (M * X).trace * (M ^ (2 * K)).trace ≤
      (1 + δ) * (M ^ (2 * K + 1)).trace * X.trace := by
  obtain ⟨U, d, hU, hU', rfl, hd⟩ := exists_spectral_psd hM
  have hc : ∀ i, 0 ≤ (Uᴴ * X * U) i i := fun i =>
    (hX.conjTranspose_mul_mul_same U).diag_nonneg
  rw [trace_conj_mul, trace_conj_pow d hU hU', trace_conj_pow d hU hU', trace_conj' X hU']
  exact scalar_power_lemma d _ hd hc hδ0 hδ1 K hK

/-- Entries of a positive semidefinite matrix with unit diagonal lie in `[-1, 1]`. -/
theorem psd_unitDiag_abs_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (h1 : ∀ i, X i i = 1) (i j : Fin n) : |X i j| ≤ 1 := by
  have hsym : X j i = X i j := by
    have h := congrFun (congrFun hX.1 i) j
    simpa using h
  have key : ∀ t : ℝ, 0 ≤ X i i + t * X i j + t * X j i + t * t * X j j := by
    intro t
    have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 + t • Pi.single j 1)
    simp only [star_trivial, mulVec_add, mulVec_smul, mulVec_single_one, add_dotProduct,
      smul_dotProduct, dotProduct_add, dotProduct_smul, single_dotProduct, one_mul,
      smul_eq_mul, col_apply] at h
    linarith
  have hp := key 1
  have hm := key (-1)
  rw [h1 i, h1 j, hsym] at hp hm
  rw [abs_le]
  constructor <;> linarith

end QMCSub


