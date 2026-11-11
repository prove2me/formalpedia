-- Prove2me | Definitions.Def_QMCSub_Core
-- name    : QMCSub_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:04:45.531697+00:00
-- url     : https://prove2.me/theorems/851c0500-ed40-42ac-b4c6-80efd92591db
-- title:
--   Soundness and accuracy of the integer subgradient iteration
-- statement:
--   Let $P$ be the sum of the rounded primal values over $T$ iterations and let $c_\theta$ be a positive integer.
--
--   **Soundness.** If the final iterate passes the check $c_\theta(T-u^{(T)}_i)\le\eta T$ for all $i$, there is a positive semidefinite $X$ with unit diagonal and $\langle L,X\rangle\ge Pc_\theta/(T(c_\theta+1))$.
--
--   **Accuracy.** Under explicit inequalities on the parameters the check passes, and every such $X$ satisfies
--   $$\langle L,X\rangle\le\frac{Pc_\theta}{T(c_\theta+1)}+\frac{4w}{c_\theta}+1+\eta n^2+n^2T+4\delta n(2w+2n\sigma),$$
--   where $\operatorname{tr}L\le2w$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter
import Definitions.Def_QMCSub_Step

/-!
Soundness and accuracy of the integer subgradient iteration.
-/

namespace QMCSub
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- The per-step error budget. -/
noncomputable def errE (n : ℕ) (η σ w : ℤ) (T : ℕ) (δ : ℝ) : ℝ :=
  η * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 * T + 4 * δ * n * (2 * w + 2 * n * σ)

section run
variable {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w)
variable (η σ : ℤ) (K T : ℕ)

include hLap in
theorem shift_nonneg (hη : 0 ≤ η) (hn : 1 ≤ n) (hσ : (T : ℤ) * (η * n) ≤ σ)
    (k : ℕ) (hk : k ≤ T) (i : Fin n) : 0 ≤ σ + useq L η σ K k i := by
  have h := useq_abs_le hLap.symm η σ K hη hn k i
  rw [abs_le] at h
  have h0 : 0 ≤ η * (n : ℤ) := mul_nonneg hη (Int.natCast_nonneg n)
  have hk' : (k : ℤ) * (η * n) ≤ (T : ℤ) * (η * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h0
  linarith [h.1]

include hLap in
theorem sum_abs_le (hη : 0 ≤ η) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ T) :
    ∑ i, |(useq L η σ K k i : ℝ)| ≤ (n : ℝ) ^ 2 * T * η := by
  have h1 : ∀ i, |(useq L η σ K k i : ℝ)| ≤ (T : ℝ) * (η * n) := by
    intro i
    have h := useq_abs_le hLap.symm η σ K hη hn k i
    have h0 : 0 ≤ η * (n : ℤ) := mul_nonneg hη (Int.natCast_nonneg n)
    have hk' : (k : ℤ) * (η * n) ≤ (T : ℤ) * (η * n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h0
    have h2 : |useq L η σ K k i| ≤ (T : ℤ) * (η * n) := h.trans hk'
    have h3 : ((|useq L η σ K k i| : ℤ) : ℝ) ≤ (((T : ℤ) * (η * n) : ℤ) : ℝ) := by
      exact_mod_cast h2
    rw [Int.cast_abs] at h3
    calc |(useq L η σ K k i : ℝ)| ≤ (((T : ℤ) * (η * n) : ℤ) : ℝ) := h3
      _ = (T : ℝ) * (η * n) := by push_cast; ring
  calc ∑ i, |(useq L η σ K k i : ℝ)| ≤ ∑ _i : Fin n, (T : ℝ) * (η * n) :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = (n : ℝ) ^ 2 * T * η := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

include hLap in
theorem Mz_trace_le (hη : 0 ≤ η) (hn : 1 ≤ n) (hσ : (T : ℤ) * (η * n) ≤ σ)
    (k : ℕ) (hk : k ≤ T) :
    ((Mz L σ (useq L η σ K k)).trace : ℝ) ≤ 2 * w + 2 * n * σ := by
  rw [Mz_trace]
  have h1 : ∀ i, σ + useq L η σ K k i ≤ 2 * σ := by
    intro i
    have h := useq_abs_le hLap.symm η σ K hη hn k i
    rw [abs_le] at h
    have h0 : 0 ≤ η * (n : ℤ) := mul_nonneg hη (Int.natCast_nonneg n)
    have hk' : (k : ℤ) * (η * n) ≤ (T : ℤ) * (η * n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h0
    linarith [h.2]
  have h2 : ∑ i, (σ + useq L η σ K k i) ≤ ∑ _i : Fin n, 2 * σ :=
    Finset.sum_le_sum (fun i _ => h1 i)
  have h3 : ∑ _i : Fin n, 2 * σ = (n : ℤ) * (2 * σ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : L.trace + ∑ i, (σ + useq L η σ K k i) ≤ 2 * w + (n : ℤ) * (2 * σ) := by
    linarith [hLap.trace_le]
  have h5 : ((L.trace + ∑ i, (σ + useq L η σ K k i) : ℤ) : ℝ) ≤
      ((2 * w + (n : ℤ) * (2 * σ) : ℤ) : ℝ) := by exact_mod_cast h4
  calc ((L.trace + ∑ i, (σ + useq L η σ K k i) : ℤ) : ℝ)
      ≤ ((2 * w + (n : ℤ) * (2 * σ) : ℤ) : ℝ) := h5
    _ = 2 * w + 2 * n * σ := by push_cast; ring

include hLap in
/-- Summing the step inequality over the first `m ≤ T` iterations. -/
theorem sum_bound (hη : 0 < η) (hn : 1 ≤ n) (hσ : (T : ℤ) * (η * n) ≤ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hX1 : ∀ i, X i i = 1)
    (m : ℕ) (hm : m ≤ T) :
    (m : ℝ) * (∑ i, ∑ j, (L i j : ℝ) * X i j) +
        (∑ i, (useq L η σ K m i : ℝ) ^ 2) / (2 * η) ≤
      ∑ k ∈ Finset.range m, pt L σ K (useq L η σ K k) + m * errE n η σ w T δ := by
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  induction m with
  | zero => simp [useq_zero]
  | succ m ih =>
      have hmT : m ≤ T := Nat.le_of_succ_le hm
      have ih' := ih hmT
      have hstep := step_bound hLap η σ K hη hn (useq L η σ K m)
        (shift_nonneg hLap η σ K T hη.le hn hσ m hmT) hδ0 hδ1 hK X hX hX1
      rw [← useq_succ] at hstep
      have habs := sum_abs_le hLap η σ K T hη.le hn m hmT
      have habs' : (∑ i, |(useq L η σ K m i : ℝ)|) / η ≤ (n : ℝ) ^ 2 * T := by
        rw [div_le_iff₀ hηr]
        linarith
      have htr := Mz_trace_le hLap η σ K T hη.le hn hσ m hmT
      have htr' : 4 * δ * n * ((Mz L σ (useq L η σ K m)).trace : ℝ) ≤
          4 * δ * n * (2 * w + 2 * n * σ) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
      rw [Finset.sum_range_succ]
      have hE : errE n η σ w T δ =
          η * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 * T + 4 * δ * n * (2 * w + 2 * n * σ) := rfl
      have hsub : (∑ i, (useq L η σ K m i : ℝ) ^ 2 - ∑ i, (useq L η σ K (m + 1) i : ℝ) ^ 2) /
          (2 * η) = (∑ i, (useq L η σ K m i : ℝ) ^ 2) / (2 * η) -
            (∑ i, (useq L η σ K (m + 1) i : ℝ) ^ 2) / (2 * η) := sub_div _ _ _
      rw [hsub] at hstep
      push_cast
      nlinarith [hstep, ih', habs', htr', hE]

omit hLap in
theorem one_feasible_value :
    ∑ i, ∑ j, (L i j : ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ) i j = (L.trace : ℝ) := by
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Matrix.trace, Matrix.diag_apply]
  rw [Int.cast_sum]

include hLap in
/-- Bound on the squared norm of the final iterate. -/
theorem normSq_final_le (hη : 0 < η) (hn : 1 ≤ n) (hσ : (T : ℤ) * (η * n) ≤ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ) :
    ∑ i, (useq L η σ K T i : ℝ) ^ 2 ≤ 2 * η * T * (2 * n * w + errE n η σ w T δ) := by
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have h := sum_bound hLap η σ K T hη hn hσ hδ0 hδ1 hK 1 Matrix.PosSemidef.one
    (fun i => by simp) T le_rfl
  rw [one_feasible_value] at h
  have htr : (0 : ℝ) ≤ (L.trace : ℝ) := by exact_mod_cast hLap.trace_pos.le
  have htrle : (L.trace : ℝ) ≤ 2 * w := by exact_mod_cast hLap.trace_le
  have hpt : ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k) ≤ (T : ℝ) * (2 * n * w) := by
    calc ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k)
        ≤ ∑ _k ∈ Finset.range T, (2 * n * w : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          have h1 := pt_le hLap σ K (useq L η σ K k)
          have h2 : (n : ℝ) * (L.trace : ℝ) ≤ n * (2 * w) :=
            mul_le_mul_of_nonneg_left htrle (Nat.cast_nonneg n)
          linarith
      _ = (T : ℝ) * (2 * n * w) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have h2 : (∑ i, (useq L η σ K T i : ℝ) ^ 2) / (2 * η) ≤
      (T : ℝ) * (2 * n * w + errE n η σ w T δ) := by
    nlinarith [mul_nonneg hT0 htr]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * η)] at h2
  linarith

include hLap in
/-- The feasibility check passes under the parameter hypotheses. -/
theorem check_holds (hη : 0 < η) (hn : 1 ≤ n) (hσ : (T : ℤ) * (η * n) ≤ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ)
    (cθ : ℕ) (hηθ : 2 * (cθ : ℤ) ≤ η)
    (hHT : 8 * (cθ : ℝ) ^ 2 * (2 * n * w + errE n η σ w T δ) ≤ η * T) (i : Fin n) :
    (cθ : ℤ) * ((T : ℤ) - useq L η σ K T i) ≤ η * T := by
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hnorm := normSq_final_le hLap η σ K T hη hn hσ hδ0 hδ1 hK
  have hsingle : (useq L η σ K T i : ℝ) ^ 2 ≤ ∑ j, (useq L η σ K T j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => (useq L η σ K T j : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (2 * (cθ : ℝ) * (useq L η σ K T i : ℝ)) ^ 2 ≤ ((η : ℝ) * T) ^ 2 := by
    have h1 : (2 * (cθ : ℝ) * (useq L η σ K T i : ℝ)) ^ 2 =
        4 * (cθ : ℝ) ^ 2 * (useq L η σ K T i : ℝ) ^ 2 := by ring
    rw [h1]
    have h2 : 4 * (cθ : ℝ) ^ 2 * (useq L η σ K T i : ℝ) ^ 2 ≤
        4 * (cθ : ℝ) ^ 2 * (2 * η * T * (2 * n * w + errE n η σ w T δ)) :=
      mul_le_mul_of_nonneg_left (hsingle.trans hnorm) (by positivity)
    have h3 : 4 * (cθ : ℝ) ^ 2 * (2 * η * T * (2 * n * w + errE n η σ w T δ)) =
        (η * T) * (8 * (cθ : ℝ) ^ 2 * (2 * n * w + errE n η σ w T δ)) := by ring
    have h4 : (η * T) * (8 * (cθ : ℝ) ^ 2 * (2 * n * w + errE n η σ w T δ)) ≤
        ((η : ℝ) * T) * (η * T) :=
      mul_le_mul_of_nonneg_left hHT (mul_nonneg hηr.le hT0)
    nlinarith
  have habs := abs_le_of_sq_le_sq hsq (mul_nonneg hηr.le hT0)
  rw [abs_le] at habs
  have hθ : 2 * (cθ : ℝ) ≤ η := by exact_mod_cast hηθ
  have hfin : (cθ : ℝ) * ((T : ℝ) - (useq L η σ K T i : ℝ)) ≤ η * T := by
    nlinarith [habs.1, mul_le_mul_of_nonneg_right hθ hT0]
  exact_mod_cast hfin

end run

section sound
variable {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i)
variable (η σ : ℤ) (K : ℕ)

theorem sum_dz_eq (T : ℕ) (i : Fin n) :
    ∑ k ∈ Finset.range T, dz L η σ K (useq L η σ K k) i = η * T - useq L η σ K T i := by
  induction T with
  | zero => simp [useq_zero]
  | succ T ih =>
      rw [Finset.sum_range_succ, ih, useq_succ]
      have hstep : stepU L η σ K (useq L η σ K T) i =
          useq L η σ K T i + η - dz L η σ K (useq L η σ K T) i := rfl
      rw [hstep]
      push_cast
      ring

include hL in
theorem rho_le (hη : 0 < η) (u : Fin n → ℤ) (i : Fin n) :
    rho L σ K u i ≤ ((dz L η σ K u i : ℝ) + 1) / η := by
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  rw [le_div_iff₀ hηr]
  rcases (tauz_nonneg hL σ K u).eq_or_lt with h0 | hpos
  · have hr : rho L σ K u i = 0 := by
      unfold rho
      rw [← h0]
      simp
    have hd : dz L η σ K u i = 0 := by
      unfold dz
      rw [← h0, Int.ediv_zero]
    rw [hr, hd]
    simp
  · have h := rho_lt η σ K u hpos i
    linarith

/-- The averaged density matrix, scaled to trace `n`. -/
noncomputable def Xbar (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K T : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / (T : ℝ)) • ∑ k ∈ Finset.range T,
    ((n : ℝ) / (tauz L σ K (useq L η σ K k) : ℝ)) • castM (Qz L σ K (useq L η σ K k))

include hL in
theorem Xbar_psd (T : ℕ) : (Xbar L η σ K T).PosSemidef := by
  unfold Xbar
  apply Matrix.PosSemidef.smul _ (by positivity)
  apply Finset.sum_induction _ (fun A : Matrix (Fin n) (Fin n) ℝ => A.PosSemidef)
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro k _
    apply Matrix.PosSemidef.smul (castM_Qz_psd hL σ K _)
    apply div_nonneg (Nat.cast_nonneg n)
    exact_mod_cast tauz_nonneg hL σ K _

theorem Xbar_apply (T : ℕ) (i j : Fin n) :
    Xbar L η σ K T i j = (1 / (T : ℝ)) * ∑ k ∈ Finset.range T,
      ((n : ℝ) / (tauz L σ K (useq L η σ K k) : ℝ)) * (Qz L σ K (useq L η σ K k) i j : ℝ) := by
  unfold Xbar
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1

theorem Xbar_diag (T : ℕ) (i : Fin n) :
    Xbar L η σ K T i i = (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, rho L σ K (useq L η σ K k) i := by
  rw [Xbar_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold rho
  ring

theorem Xbar_value (T : ℕ) :
    ∑ i, ∑ j, (L i j : ℝ) * Xbar L η σ K T i j =
      (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k) := by
  simp only [Xbar_apply]
  have h1 : ∀ i j, (L i j : ℝ) * ((1 / (T : ℝ)) * ∑ k ∈ Finset.range T,
      ((n : ℝ) / (tauz L σ K (useq L η σ K k) : ℝ)) * (Qz L σ K (useq L η σ K k) i j : ℝ)) =
      (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, ((n : ℝ) / (tauz L σ K (useq L η σ K k) : ℝ)) *
        ((L i j : ℝ) * (Qz L σ K (useq L η σ K k) i j : ℝ)) := by
    intro i j
    rw [← mul_assoc, mul_comm (L i j : ℝ), mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [h1]
  simp only [← Finset.mul_sum]
  congr 1
  have hpt : ∀ k, pt L σ K (useq L η σ K k) = ∑ i, ∑ j,
      ((n : ℝ) / (tauz L σ K (useq L η σ K k) : ℝ)) *
        ((L i j : ℝ) * (Qz L σ K (useq L η σ K k) i j : ℝ)) := by
    intro k
    unfold pt
    simp only [← Finset.mul_sum]
    ring
  simp only [hpt]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

include hL in
/-- Soundness: a passed check yields a feasible point whose value dominates the output. -/
theorem sound (hdiag : ∀ i, 0 ≤ L i i) (hη : 0 < η) (T : ℕ) (hT : 0 < T) (cθ : ℕ)
    (hcθ : 0 < cθ) (hcheck : ∀ i, (cθ : ℤ) * ((T : ℤ) - useq L η σ K T i) ≤ η * T) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef ∧ (∀ i, X i i = 1) ∧
      (Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1)) ≤ ∑ i, ∑ j, (L i j : ℝ) * X i j := by
  have hcθr : (0 : ℝ) < cθ := by exact_mod_cast hcθ
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (0 : ℝ) ≤ 1 / (T : ℝ) := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (cθ : ℝ) / (cθ + 1) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact div_pos hcθr (by linarith)
  have hdiagX : ∀ i, c * Xbar L η σ K T i i ≤ 1 := by
    intro i
    rw [Xbar_diag]
    have h1 : ∑ k ∈ Finset.range T, rho L σ K (useq L η σ K k) i ≤
        ∑ k ∈ Finset.range T, ((dz L η σ K (useq L η σ K k) i : ℝ) + 1) / η :=
      Finset.sum_le_sum (fun k _ => rho_le hL η σ K hη _ i)
    have h3 : (∑ k ∈ Finset.range T, (dz L η σ K (useq L η σ K k) i : ℝ)) =
        (η : ℝ) * T - (useq L η σ K T i : ℝ) := by
      have h := sum_dz_eq (L := L) η σ K T i
      exact_mod_cast h
    have h2 : ∑ k ∈ Finset.range T, ((dz L η σ K (useq L η σ K k) i : ℝ) + 1) / η =
        ((η : ℝ) * T - (useq L η σ K T i : ℝ) + T) / η := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, h3]
      simp
    rw [h2] at h1
    have hck : (cθ : ℝ) * ((T : ℝ) - (useq L η σ K T i : ℝ)) ≤ η * T := by
      exact_mod_cast hcheck i
    have hR : c * ((1 / (T : ℝ)) * (((η : ℝ) * T - (useq L η σ K T i : ℝ) + T) / η)) ≤ 1 := by
      have e : c * ((1 / (T : ℝ)) * (((η : ℝ) * T - (useq L η σ K T i : ℝ) + T) / η)) =
          ((cθ : ℝ) * ((η : ℝ) * T - (useq L η σ K T i : ℝ) + T)) / (((cθ : ℝ) + 1) * T * η) := by
        rw [hc]
        field_simp
      rw [e, div_le_one (mul_pos (mul_pos (by linarith) hTr) hηr)]
      nlinarith [hck]
    calc c * (1 / (T : ℝ) * ∑ k ∈ Finset.range T, rho L σ K (useq L η σ K k) i)
        ≤ c * ((1 / (T : ℝ)) * (((η : ℝ) * T - (useq L η σ K T i : ℝ) + T) / η)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hT1) hc0.le
      _ ≤ 1 := hR
  refine ⟨c • Xbar L η σ K T + Matrix.diagonal (fun i => 1 - c * Xbar L η σ K T i i), ?_, ?_, ?_⟩
  · apply Matrix.PosSemidef.add
    · exact (Xbar_psd hL η σ K T).smul hc0.le
    · rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact sub_nonneg.mpr (hdiagX i)
  · intro i
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq]
    ring
  · have hval : ∑ i, ∑ j, (L i j : ℝ) *
        (c • Xbar L η σ K T + Matrix.diagonal (fun i => 1 - c * Xbar L η σ K T i i)) i j =
        c * (∑ i, ∑ j, (L i j : ℝ) * Xbar L η σ K T i j) +
          ∑ i, (L i i : ℝ) * (1 - c * Xbar L η σ K T i i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      have hj : ∀ j, (L i j : ℝ) *
          (c • Xbar L η σ K T + Matrix.diagonal (fun i => 1 - c * Xbar L η σ K T i i)) i j =
          c * ((L i j : ℝ) * Xbar L η σ K T i j) +
            (if i = j then (L i j : ℝ) * (1 - c * Xbar L η σ K T i i) else 0) := by
        intro j
        rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
        split_ifs with h <;> ring
      simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hP : (Pz L η σ K T : ℝ) ≤ ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k) := by
      unfold Pz
      rw [Int.cast_sum]
      exact Finset.sum_le_sum (fun k _ => pz_le_pt hL σ K _)
    have e2 : (Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1)) =
        c * ((1 / (T : ℝ)) * (Pz L η σ K T : ℝ)) := by
      rw [hc]
      field_simp
    rw [e2, hval, Xbar_value]
    have h6 : c * ((1 / (T : ℝ)) * (Pz L η σ K T : ℝ)) ≤
        c * ((1 / (T : ℝ)) * ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hT1) hc0.le
    have h7 : 0 ≤ ∑ i, (L i i : ℝ) * (1 - c * Xbar L η σ K T i i) :=
      Finset.sum_nonneg (fun i _ =>
        mul_nonneg (by exact_mod_cast hdiag i) (sub_nonneg.mpr (hdiagX i)))
    linarith

end sound

/-- Accuracy: under the parameter hypotheses every feasible value is within the error budget
of the output (and, by `check_holds`, the check passes). -/
theorem accurate {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (η σ : ℤ)
    (K T : ℕ) (hη : 0 < η) (hn : 1 ≤ n) (hT : 0 < T) (hσ : (T : ℤ) * (η * n) ≤ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ)
    (cθ : ℕ) (hcθ : 0 < cθ) (hηθ : 2 * (cθ : ℤ) ≤ η)
    (hHT : 8 * (cθ : ℝ) ^ 2 * (2 * n * w + errE n η σ w T δ) ≤ η * T)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hX1 : ∀ i, X i i = 1) :
    ∑ i, ∑ j, (L i j : ℝ) * X i j ≤
      (Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1)) + (4 * w / cθ + 1 + errE n η σ w T δ) := by
  have hcθr : (0 : ℝ) < cθ := by exact_mod_cast hcθ
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcheck := fun i => check_holds hLap η σ K T hη hn hσ hδ0 hδ1 hK cθ hηθ hHT i
  have hdiag : ∀ i, 0 ≤ L i i := by
    intro i
    have h := hLap.psd.diag_nonneg (i := i)
    rw [castM_apply] at h
    exact_mod_cast h
  obtain ⟨X', hX', hX'1, hval⟩ := sound hLap.symm η σ K hdiag hη T hT cθ hcθ hcheck
  have h4w := hLap.feas_le X' hX' hX'1
  have hsum := sum_bound hLap η σ K T hη hn hσ hδ0 hδ1 hK X hX hX1 T le_rfl
  have hpt : ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k) ≤ (Pz L η σ K T : ℝ) + T := by
    unfold Pz
    rw [Int.cast_sum]
    calc ∑ k ∈ Finset.range T, pt L σ K (useq L η σ K k)
        ≤ ∑ k ∈ Finset.range T, ((pz L σ K (useq L η σ K k) : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro k hk
          exact (pt_lt σ K _ (tauz_pos hLap σ K _
            (shift_nonneg hLap η σ K T hη.le hn hσ k (Finset.mem_range.mp hk).le))).le
      _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
  have hnn : 0 ≤ (∑ i, (useq L η σ K T i : ℝ) ^ 2) / (2 * η) :=
    div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by linarith)
  have hA : ∑ i, ∑ j, (L i j : ℝ) * X i j ≤
      (Pz L η σ K T : ℝ) / T + 1 + errE n η σ w T δ := by
    have h1 : (T : ℝ) * (∑ i, ∑ j, (L i j : ℝ) * X i j) ≤
        (T : ℝ) * ((Pz L η σ K T : ℝ) / T + 1 + errE n η σ w T δ) := by
      have e : (T : ℝ) * ((Pz L η σ K T : ℝ) / T + 1 + errE n η σ w T δ) =
          (Pz L η σ K T : ℝ) + T + T * errE n η σ w T δ := by
        field_simp
      rw [e]
      linarith
    exact le_of_mul_le_mul_left h1 hTr
  have hgap : (Pz L η σ K T : ℝ) / T ≤
      (Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1)) + 4 * w / cθ := by
    have hy : (Pz L η σ K T : ℝ) / T = (Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1)) +
        ((Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1))) / cθ := by
      field_simp
    have h2 : ((Pz L η σ K T : ℝ) * cθ / (T * (cθ + 1))) / cθ ≤ 4 * w / cθ := by
      gcongr
      linarith
    linarith
  linarith

end QMCSub


