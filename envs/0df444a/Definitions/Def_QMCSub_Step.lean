-- Prove2me | Definitions.Def_QMCSub_Step
-- name    : QMCSub_Step
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:03:22.267687+00:00
-- url     : https://prove2.me/theorems/a1ea9e8b-ad11-4c8c-853a-cdf198861e5f
-- title:
--   One-step dual bound for the subgradient iteration
-- statement:
--   For a positive semidefinite integer Laplacian $L$ and an iterate $u$ with $\sigma+u_i\ge0$, the density $\rho=Q/\tau$ of the even power $Q=M^{2K}$ gives a dual bound: for every positive semidefinite $X$ with unit diagonal,
--   $$\langle L,X\rangle\le n\langle L,\rho\rangle+\sum_iu_i(n\rho_{ii}-1)+4\delta n\operatorname{tr}M,$$
--   whenever $0<\delta\le\tfrac12$ and $n(1-\delta)^{2K}\le\delta$. Combined with the rounded update this yields the telescoping step inequality in $\lVert u\rVert^2$ and the a priori bound $|u^{(k)}_i|\le k\eta n$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter

/-!
One step of the subgradient analysis: the dual bound from the power lemma and the
telescoping step inequality.
-/

namespace QMCSub
open Matrix
open scoped BigOperators

variable {n : ℕ}

theorem trace_castM (A : Matrix (Fin n) (Fin n) ℤ) : (castM A).trace = (A.trace : ℝ) := by
  simp only [Matrix.trace, Matrix.diag_apply, castM_apply]
  rw [Int.cast_sum]

theorem Mz_trace (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (u : Fin n → ℤ) :
    (Mz L σ u).trace = L.trace + ∑ i, (σ + u i) := by
  unfold Mz
  rw [Matrix.trace_add, Matrix.trace_diagonal]

/-- `tr(M X)` for the shifted matrix and a symmetric `X`. -/
theorem trace_castM_Mz_mul (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (u : Fin n → ℤ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : ∀ i j, X i j = X j i) :
    (castM (Mz L σ u) * X).trace =
      ∑ i, ∑ j, (L i j : ℝ) * X i j + ∑ i, ((σ + u i : ℤ) : ℝ) * X i i := by
  rw [castM_Mz, add_mul, Matrix.trace_add]
  congr 1
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, castM_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hX j i]
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

theorem tauz_pos {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) (hu : ∀ i, 0 ≤ σ + u i) : 0 < tauz L σ K u := by
  have hM := castM_Mz_psd σ u hLap.psd hu
  have htr : 0 < (castM (Mz L σ u)).trace := by
    rw [trace_castM, Mz_trace]
    have h1 : 0 ≤ ∑ i, (σ + u i) := Finset.sum_nonneg (fun i _ => hu i)
    have h2 := hLap.trace_pos
    exact_mod_cast add_pos_of_pos_of_nonneg h2 h1
  have h := psd_pow_trace_pos hM htr (2 * K)
  rw [← castM_Qz, trace_castM] at h
  have h' : (0 : ℝ) < ((tauz L σ K u : ℤ) : ℝ) := h
  exact_mod_cast h'

theorem trace_Mz_Qz {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) :
    (castM (Mz L σ u) * castM (Qz L σ K u)).trace =
      ∑ i, ∑ j, (L i j : ℝ) * (Qz L σ K u i j : ℝ) +
        ∑ i, ((σ + u i : ℤ) : ℝ) * (Qz L σ K u i i : ℝ) := by
  rw [trace_castM_Mz_mul L σ u _ (fun i j => by rw [castM_apply, castM_apply, Qz_symm hL])]
  rfl

theorem nB_eq {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) :
    (n : ℝ) * (castM (Mz L σ u) * castM (Qz L σ K u)).trace / (tauz L σ K u : ℝ) =
      pt L σ K u + ∑ i, ((σ + u i : ℤ) : ℝ) * rho L σ K u i := by
  rw [trace_Mz_Qz hL]
  unfold pt rho
  rw [mul_add, add_div]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `n ⟨L, ρ⟩ ≤ n tr L`. -/
theorem pt_le {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) : pt L σ K u ≤ n * (L.trace : ℝ) := by
  unfold pt
  have hτ0 : (0 : ℝ) ≤ (tauz L σ K u : ℝ) := by exact_mod_cast tauz_nonneg hLap.symm σ K u
  have htrL : (0 : ℝ) ≤ (L.trace : ℝ) := by exact_mod_cast hLap.trace_pos.le
  rcases hτ0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact mul_nonneg (Nat.cast_nonneg n) htrL
  · rw [div_le_iff₀ hpos]
    have hQ := castM_Qz_psd hLap.symm σ K u
    have h := psd_trace_mul_le hLap.psd hQ
    rw [trace_castM, trace_castM] at h
    have hsum : (castM L * castM (Qz L σ K u)).trace =
        ∑ i, ∑ j, (L i j : ℝ) * (Qz L σ K u i j : ℝ) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, castM_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Qz_symm hLap.symm σ K u j i]
    rw [hsum] at h
    have h' : (∑ i, ∑ j, (L i j : ℝ) * (Qz L σ K u i j : ℝ)) ≤
        (L.trace : ℝ) * (tauz L σ K u : ℝ) := h
    calc (n : ℝ) * ∑ i, ∑ j, (L i j : ℝ) * (Qz L σ K u i j : ℝ)
        ≤ (n : ℝ) * ((L.trace : ℝ) * (tauz L σ K u : ℝ)) :=
          mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg n)
      _ = n * (L.trace : ℝ) * (tauz L σ K u : ℝ) := by ring

/-- The dual bound at one iterate. -/
theorem dual_bound {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) (hu : ∀ i, 0 ≤ σ + u i) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hX1 : ∀ i, X i i = 1) :
    ∑ i, ∑ j, (L i j : ℝ) * X i j ≤
      pt L σ K u + ∑ i, (u i : ℝ) * (rho L σ K u i - 1) +
        4 * δ * n * ((Mz L σ u).trace : ℝ) := by
  have hM : (castM (Mz L σ u)).PosSemidef := castM_Mz_psd σ u hLap.psd hu
  have hQ : (castM (Qz L σ K u)).PosSemidef := castM_Qz_psd hLap.symm σ K u
  have hτ := tauz_pos hLap σ K u hu
  have hτr : (0 : ℝ) < (tauz L σ K u : ℝ) := by exact_mod_cast hτ
  have hXsymm : ∀ i j, X i j = X j i := fun i j => by
    have h := hX.1.apply j i
    simpa using h
  have hpl := power_lemma hM hX hδ0 (by linarith) K hK
  have hXtr : X.trace = n := by
    simp [Matrix.trace, hX1]
  have hQtr : (castM (Mz L σ u) ^ (2 * K)).trace = (tauz L σ K u : ℝ) := by
    rw [← castM_Qz, trace_castM]
    rfl
  have hpow : castM (Mz L σ u) ^ (2 * K + 1) = castM (Mz L σ u) * castM (Qz L σ K u) := by
    rw [castM_Qz, pow_succ']
  have hMX : (castM (Mz L σ u) * X).trace =
      ∑ i, ∑ j, (L i j : ℝ) * X i j + ∑ i, ((σ + u i : ℤ) : ℝ) := by
    rw [trace_castM_Mz_mul L σ u X hXsymm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hX1 i, mul_one]
  rw [hXtr, hQtr, hpow, hMX] at hpl
  have hB := nB_eq hLap.symm σ K u
  have hBtr0 := psd_trace_mul_nonneg hM hQ
  have hBtrle := psd_trace_mul_le hM hQ
  rw [trace_castM, trace_castM] at hBtrle
  have hBtrle' : (castM (Mz L σ u) * castM (Qz L σ K u)).trace ≤
      ((Mz L σ u).trace : ℝ) * (tauz L σ K u : ℝ) := hBtrle
  set Btr := (castM (Mz L σ u) * castM (Qz L σ K u)).trace with hBtr
  set A := ∑ i, ∑ j, (L i j : ℝ) * X i j with hA
  set C := ∑ i, ((σ + u i : ℤ) : ℝ) with hC
  set B := (n : ℝ) * Btr / (tauz L σ K u : ℝ) with hBdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg hn0 hBtr0) hτr.le
  have hBle : B ≤ n * ((Mz L σ u).trace : ℝ) := by
    rw [hBdef, div_le_iff₀ hτr]
    calc (n : ℝ) * Btr ≤ n * (((Mz L σ u).trace : ℝ) * (tauz L σ K u : ℝ)) :=
          mul_le_mul_of_nonneg_left hBtrle' hn0
      _ = n * ((Mz L σ u).trace : ℝ) * (tauz L σ K u : ℝ) := by ring
  have hBτ : B * (tauz L σ K u : ℝ) = n * Btr := by
    rw [hBdef]
    field_simp
  have h1 : (1 - δ) * (A + C) ≤ (1 + δ) * B := by
    have h2 : (1 - δ) * (A + C) * (tauz L σ K u : ℝ) ≤ (1 + δ) * B * (tauz L σ K u : ℝ) := by
      calc (1 - δ) * (A + C) * (tauz L σ K u : ℝ) ≤ (1 + δ) * Btr * n := hpl
        _ = (1 + δ) * B * (tauz L σ K u : ℝ) := by rw [mul_assoc (1 + δ) B, hBτ]; ring
    exact le_of_mul_le_mul_right h2 hτr
  have h3 : A + C ≤ (1 + 4 * δ) * B := by
    have h4 : (1 - δ) * (A + C) ≤ (1 - δ) * ((1 + 4 * δ) * B) := by
      have h5 : 0 ≤ δ * (1 - 2 * δ) * B :=
        mul_nonneg (mul_nonneg hδ0.le (by linarith)) hB0
      nlinarith
    exact le_of_mul_le_mul_left h4 (by linarith)
  have hsum : ∑ i, ((σ + u i : ℤ) : ℝ) * rho L σ K u i - C =
      ∑ i, (u i : ℝ) * (rho L σ K u i - 1) := by
    have hρ := sum_rho σ K u hτ
    rw [hC, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, ((σ + u i : ℤ) : ℝ) * rho L σ K u i - ((σ + u i : ℤ) : ℝ) =
        (σ : ℝ) * (rho L σ K u i - 1) + (u i : ℝ) * (rho L σ K u i - 1) := fun i => by
      push_cast; ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hρ]
    simp
  have h6 : 4 * δ * B ≤ 4 * δ * n * ((Mz L σ u).trace : ℝ) := by
    have := mul_le_mul_of_nonneg_left hBle (by linarith : (0 : ℝ) ≤ 4 * δ)
    linarith
  rw [hB] at h3 h6
  linarith

theorem sum_sq_step_le {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i)
    (η σ : ℤ) (K : ℕ) (u : Fin n → ℤ) (hη : 0 ≤ η) (hn : 1 ≤ n) :
    ∑ i, (η - dz L η σ K u i) ^ 2 ≤ 2 * η ^ 2 * (n : ℤ) ^ 2 := by
  have h1 : ∀ i, (η - dz L η σ K u i) ^ 2 ≤ η ^ 2 + dz L η σ K u i * (η * n) := by
    intro i
    have hd0 := dz_nonneg hL η σ K u hη i
    have hd1 := dz_le hL η σ K u hη i
    nlinarith [mul_nonneg hη hd0, mul_le_mul_of_nonneg_left hd1 hd0]
  have h0 : 0 ≤ η * (n : ℤ) := mul_nonneg hη (Int.natCast_nonneg n)
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  calc ∑ i, (η - dz L η σ K u i) ^ 2
      ≤ ∑ i, (η ^ 2 + dz L η σ K u i * (η * n)) := Finset.sum_le_sum (fun i _ => h1 i)
    _ = n * η ^ 2 + (∑ i, dz L η σ K u i) * (η * n) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp
    _ ≤ n * η ^ 2 + (η * n) * (η * n) := by
        have := mul_le_mul_of_nonneg_right (sum_dz_le hL η σ K u hη) h0
        linarith
    _ ≤ 2 * η ^ 2 * (n : ℤ) ^ 2 := by
        have h2 : (0 : ℤ) ≤ η ^ 2 * ((n : ℤ) ^ 2 - n) :=
          mul_nonneg (sq_nonneg η) (by nlinarith)
        nlinarith

/-- The telescoping step inequality. -/
theorem step_bound {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (η σ : ℤ) (K : ℕ)
    (hη : 0 < η) (hn : 1 ≤ n)
    (u : Fin n → ℤ) (hu : ∀ i, 0 ≤ σ + u i) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hK : (n : ℝ) * (1 - δ) ^ (2 * K) ≤ δ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hX1 : ∀ i, X i i = 1) :
    ∑ i, ∑ j, (L i j : ℝ) * X i j ≤
      pt L σ K u + (∑ i, (u i : ℝ) ^ 2 - ∑ i, (stepU L η σ K u i : ℝ) ^ 2) / (2 * η)
        + η * (n : ℝ) ^ 2 + (∑ i, |(u i : ℝ)|) / η
        + 4 * δ * n * ((Mz L σ u).trace : ℝ) := by
  have hdb := dual_bound hLap σ K u hu hδ0 hδ1 hK X hX hX1
  have hτ := tauz_pos hLap σ K u hu
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have h2η : (0 : ℝ) < 2 * η := by linarith
  have hi : ∀ i, (u i : ℝ) * (rho L σ K u i - 1) ≤
      ((u i : ℝ) ^ 2 - (stepU L η σ K u i : ℝ) ^ 2) / (2 * η) +
        ((η - dz L η σ K u i : ℤ) : ℝ) ^ 2 / (2 * η) + |(u i : ℝ)| / η := by
    intro i
    have h1 := dz_le_rho hLap.symm η σ K u i
    have h2 := rho_lt η σ K u hτ i
    have hstep : (stepU L η σ K u i : ℝ) = (u i : ℝ) + η - (dz L η σ K u i : ℝ) := by
      unfold stepU
      push_cast
      rfl
    have hcast : ((η - dz L η σ K u i : ℤ) : ℝ) = (η : ℝ) - (dz L η σ K u i : ℝ) := by
      push_cast
      rfl
    rw [hstep, hcast]
    generalize (dz L η σ K u i : ℝ) = d at h1 h2 ⊢
    generalize rho L σ K u i = r at h1 h2 ⊢
    generalize (u i : ℝ) = x
    have hgap0 : 0 ≤ r - d / η := by
      rw [sub_nonneg, div_le_iff₀ hηr]
      linarith
    have hgap1 : r - d / η ≤ 1 / η := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hηr]
      linarith
    have habs : x * (r - d / η) ≤ |x| / η := by
      calc x * (r - d / η) ≤ |x| * (r - d / η) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hgap0
        _ ≤ |x| * (1 / η) := mul_le_mul_of_nonneg_left hgap1 (abs_nonneg _)
        _ = |x| / η := by ring
    have halg : x * (d / η - 1) =
        (x ^ 2 - (x + η - d) ^ 2) / (2 * η) + ((η : ℝ) - d) ^ 2 / (2 * η) := by
      field_simp
      ring
    calc x * (r - 1) = x * (d / η - 1) + x * (r - d / η) := by ring
      _ ≤ _ := by rw [halg]; linarith
  have hsq := sum_sq_step_le hLap.symm η σ K u hη.le hn
  have hsq' : (∑ i, ((η - dz L η σ K u i : ℤ) : ℝ) ^ 2) ≤ 2 * (η : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    exact_mod_cast hsq
  have hsq'' : (∑ i, ((η - dz L η σ K u i : ℤ) : ℝ) ^ 2) / (2 * η) ≤ η * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ h2η]
    nlinarith
  have key : ∑ i, (u i : ℝ) * (rho L σ K u i - 1) ≤
      (∑ i, (u i : ℝ) ^ 2 - ∑ i, (stepU L η σ K u i : ℝ) ^ 2) / (2 * η)
        + (∑ i, ((η - dz L η σ K u i : ℤ) : ℝ) ^ 2) / (2 * η) + (∑ i, |(u i : ℝ)|) / η := by
    calc ∑ i, (u i : ℝ) * (rho L σ K u i - 1)
        ≤ ∑ i, (((u i : ℝ) ^ 2 - (stepU L η σ K u i : ℝ) ^ 2) / (2 * η) +
            ((η - dz L η σ K u i : ℤ) : ℝ) ^ 2 / (2 * η) + |(u i : ℝ)| / η) :=
          Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
            ← Finset.sum_div, ← Finset.sum_div, Finset.sum_sub_distrib]
  linarith

/-- A priori bound on the iterates. -/
theorem useq_abs_le {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i)
    (η σ : ℤ) (K : ℕ) (hη : 0 ≤ η) (hn : 1 ≤ n) (k : ℕ) (i : Fin n) :
    |useq L η σ K k i| ≤ k * (η * n) := by
  induction k with
  | zero => simp [useq_zero]
  | succ k ih =>
      rw [useq_succ]
      have hd0 := dz_nonneg hL η σ K (useq L η σ K k) hη i
      have hd1 := dz_le hL η σ K (useq L η σ K k) hη i
      have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
      have hηn : η ≤ η * n := by nlinarith
      have hstep : stepU L η σ K (useq L η σ K k) i =
          useq L η σ K k i + η - dz L η σ K (useq L η σ K k) i := rfl
      rw [hstep]
      rw [abs_le] at ih ⊢
      push_cast
      constructor <;> nlinarith [ih.1, ih.2]

end QMCSub


