-- Prove2me | Definitions.Def_QMCSub_Iter
-- name    : QMCSub_Iter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:02:25.669275+00:00
-- url     : https://prove2.me/theorems/5c900111-770f-4cb3-bb00-34a37ff8cd6a
-- title:
--   Integer subgradient iteration for the Max-Cut semidefinite relaxation
-- statement:
--   Definitions for a dual subgradient method run entirely in integers. Given an integer matrix $L$ (a graph Laplacian), a shift $\sigma$, a step $\eta$ and an exponent $K$, an iterate $u\in\mathbb Z^n$ determines $M=L+\operatorname{diag}(\sigma+u)$, $Q=M^{2K}$ and $\tau=\operatorname{tr}Q$. The update is $u_i\leftarrow u_i+\eta-\lfloor\eta nQ_{ii}/\tau\rfloor$, and each step records $\lfloor n\langle L,Q\rangle/\tau\rfloor$.
--
--   The file also proves the elementary properties of these quantities: symmetry and positive semidefiniteness of $Q$, the rounding bounds, and $\sum_i nQ_{ii}/\tau=n$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QMCSub_LinAlg

/-!
The integer subgradient iteration for the Max-Cut SDP and its elementary properties.
-/

namespace QMCSub
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- Entrywise cast of an integer matrix to the reals. -/
noncomputable abbrev castM : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℝ :=
  (Int.castRingHom ℝ).mapMatrix

theorem castM_apply (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    castM A i j = (A i j : ℝ) := rfl

/-- The shifted matrix `L + diag(σ + u)`. -/
def Mz (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (u : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  L + Matrix.diagonal (fun i => σ + u i)

/-- The even power `M^(2K)`. -/
def Qz (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (K : ℕ) (u : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ := (Mz L σ u) ^ (2 * K)

def tauz (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (K : ℕ) (u : Fin n → ℤ) : ℤ :=
  (Qz L σ K u).trace

/-- Rounded-down scaled diagonal of the density matrix. -/
def dz (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K : ℕ) (u : Fin n → ℤ) (i : Fin n) : ℤ :=
  (η * n * (Qz L σ K u) i i) / tauz L σ K u

/-- Rounded-down primal value `n ⟨L, ρ⟩`. -/
def pz (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (K : ℕ) (u : Fin n → ℤ) : ℤ :=
  (n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j) / tauz L σ K u

def stepU (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K : ℕ) (u : Fin n → ℤ) : Fin n → ℤ :=
  fun i => u i + η - dz L η σ K u i

def useq (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K : ℕ) (k : ℕ) : Fin n → ℤ :=
  (stepU L η σ K)^[k] 0

def Pz (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K T : ℕ) : ℤ :=
  ∑ k ∈ Finset.range T, pz L σ K (useq L η σ K k)

theorem useq_zero (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K : ℕ) : useq L η σ K 0 = 0 := rfl

theorem useq_succ (L : Matrix (Fin n) (Fin n) ℤ) (η σ : ℤ) (K : ℕ) (k : ℕ) :
    useq L η σ K (k + 1) = stepU L η σ K (useq L η σ K k) := by
  unfold useq
  rw [Function.iterate_succ_apply']

/-- What the analysis needs from the (integer) Laplacian. -/
structure LapHyp (L : Matrix (Fin n) (Fin n) ℤ) (w : ℤ) : Prop where
  symm : ∀ i j, L i j = L j i
  psd : (castM L).PosSemidef
  trace_pos : 0 < L.trace
  trace_le : L.trace ≤ 2 * w
  feas_le : ∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef → (∀ i, X i i = 1) →
    ∑ i, ∑ j, (L i j : ℝ) * X i j ≤ 4 * w

section basic
variable {L : Matrix (Fin n) (Fin n) ℤ} (hL : ∀ i j, L i j = L j i)
variable (η σ : ℤ) (K : ℕ) (u : Fin n → ℤ)

include hL in
theorem Mz_symm (i j : Fin n) : Mz L σ u i j = Mz L σ u j i := by
  unfold Mz
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  rw [hL i j]
  by_cases h : i = j
  · subst h; rfl
  · have h' : ¬ j = i := fun e => h e.symm
    simp only [h, h', if_false]

include hL in
theorem Mz_transpose : (Mz L σ u)ᵀ = Mz L σ u := by
  ext i j
  exact Mz_symm hL σ u j i

include hL in
theorem Qz_symm (i j : Fin n) : Qz L σ K u i j = Qz L σ K u j i := by
  have h : (Qz L σ K u)ᵀ = Qz L σ K u := by
    unfold Qz
    rw [Matrix.transpose_pow, Mz_transpose hL]
  have h2 := congrFun (congrFun h j) i
  simpa only [Matrix.transpose_apply] using h2

include hL in
theorem castM_Mz_isHermitian : (castM (Mz L σ u)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [castM_apply, castM_apply, star_trivial, Mz_symm hL σ u j i]

theorem castM_Qz : castM (Qz L σ K u) = (castM (Mz L σ u)) ^ (2 * K) := by
  unfold Qz
  exact map_pow castM _ _

include hL in
theorem castM_Qz_psd : (castM (Qz L σ K u)).PosSemidef := by
  rw [castM_Qz]
  exact psd_even_pow (castM_Mz_isHermitian hL σ u) K

theorem castM_Mz : castM (Mz L σ u) =
    castM L + Matrix.diagonal (fun i => ((σ + u i : ℤ) : ℝ)) := by
  ext i j
  rw [castM_apply]
  unfold Mz
  simp only [Matrix.add_apply, Matrix.diagonal_apply, castM_apply]
  by_cases h : i = j
  · simp only [h, if_true, Int.cast_add]
  · simp only [h, if_false, Int.cast_add, Int.cast_zero]

theorem castM_Mz_psd (hpsd : (castM L).PosSemidef) (hu : ∀ i, 0 ≤ σ + u i) :
    (castM (Mz L σ u)).PosSemidef := by
  rw [castM_Mz]
  apply Matrix.PosSemidef.add hpsd
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast hu i

include hL in
theorem Qz_diag_nonneg (i : Fin n) : 0 ≤ Qz L σ K u i i := by
  have h := (castM_Qz_psd hL σ K u).diag_nonneg (i := i)
  rw [castM_apply] at h
  exact_mod_cast h

theorem tauz_eq : tauz L σ K u = ∑ i, Qz L σ K u i i := rfl

include hL in
theorem tauz_nonneg : 0 ≤ tauz L σ K u := by
  rw [tauz_eq]
  exact Finset.sum_nonneg (fun i _ => Qz_diag_nonneg hL σ K u i)

include hL in
theorem Qz_diag_le_tauz (i : Fin n) : Qz L σ K u i i ≤ tauz L σ K u := by
  rw [tauz_eq]
  exact Finset.single_le_sum (f := fun i => Qz L σ K u i i)
    (fun j _ => Qz_diag_nonneg hL σ K u j) (Finset.mem_univ i)

include hL in
theorem dz_nonneg (hη : 0 ≤ η) (i : Fin n) : 0 ≤ dz L η σ K u i := by
  unfold dz
  apply Int.ediv_nonneg
  · exact mul_nonneg (mul_nonneg hη (Int.natCast_nonneg n)) (Qz_diag_nonneg hL σ K u i)
  · exact tauz_nonneg hL σ K u

include hL in
theorem dz_le (hη : 0 ≤ η) (i : Fin n) : dz L η σ K u i ≤ η * n := by
  unfold dz
  by_cases hτ : tauz L σ K u = 0
  · rw [hτ, Int.ediv_zero]
    exact mul_nonneg hη (Int.natCast_nonneg n)
  · have hτpos : 0 < tauz L σ K u := lt_of_le_of_ne (tauz_nonneg hL σ K u) (Ne.symm hτ)
    apply Int.ediv_le_of_le_mul hτpos
    exact mul_le_mul_of_nonneg_left (Qz_diag_le_tauz hL σ K u i)
      (mul_nonneg hη (Int.natCast_nonneg n))

include hL in
theorem sum_dz_le (hη : 0 ≤ η) : ∑ i, dz L η σ K u i ≤ η * n := by
  by_cases hτ : tauz L σ K u = 0
  · have h0 : ∀ i, dz L η σ K u i = 0 := fun i => by unfold dz; rw [hτ, Int.ediv_zero]
    simp only [h0, Finset.sum_const_zero]
    exact mul_nonneg hη (Int.natCast_nonneg n)
  · have hτpos : 0 < tauz L σ K u := lt_of_le_of_ne (tauz_nonneg hL σ K u) (Ne.symm hτ)
    have h1 : (∑ i, dz L η σ K u i) * tauz L σ K u ≤ (η * n) * tauz L σ K u := by
      rw [Finset.sum_mul, tauz_eq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact Int.ediv_mul_le _ hτ
    exact le_of_mul_le_mul_right h1 hτpos

/-- `n ρ_ii` as a real number. -/
noncomputable def rho (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (K : ℕ) (u : Fin n → ℤ)
    (i : Fin n) : ℝ := (n * (Qz L σ K u i i : ℝ)) / (tauz L σ K u : ℝ)

/-- `n ⟨L, ρ⟩` as a real number. -/
noncomputable def pt (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (K : ℕ) (u : Fin n → ℤ) : ℝ :=
  (n * ∑ i, ∑ j, (L i j : ℝ) * (Qz L σ K u i j : ℝ)) / (tauz L σ K u : ℝ)

include hL in
theorem rho_nonneg (i : Fin n) : 0 ≤ rho L σ K u i := by
  unfold rho
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg n) (by exact_mod_cast Qz_diag_nonneg hL σ K u i)
  · exact_mod_cast tauz_nonneg hL σ K u

theorem sum_rho (hτ : 0 < tauz L σ K u) : ∑ i, rho L σ K u i = n := by
  unfold rho
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have h : (∑ i, (Qz L σ K u i i : ℝ)) = (tauz L σ K u : ℝ) := by
    rw [tauz_eq]; push_cast; rfl
  rw [h]
  have hτ' : (tauz L σ K u : ℝ) ≠ 0 := by exact_mod_cast hτ.ne'
  field_simp

include hL in
theorem dz_le_rho (i : Fin n) : (dz L η σ K u i : ℝ) ≤ η * rho L σ K u i := by
  unfold rho dz
  by_cases hτ : tauz L σ K u = 0
  · rw [hτ, Int.ediv_zero]
    simp
  · have hτpos : 0 < tauz L σ K u := lt_of_le_of_ne (tauz_nonneg hL σ K u) (Ne.symm hτ)
    have hτr : (0 : ℝ) < (tauz L σ K u : ℝ) := by exact_mod_cast hτpos
    rw [← mul_div_assoc, le_div_iff₀ hτr]
    have h := Int.ediv_mul_le (η * n * Qz L σ K u i i) hτ
    have h' : ((η * n * Qz L σ K u i i / tauz L σ K u : ℤ) : ℝ) * (tauz L σ K u : ℝ) ≤
        ((η * n * Qz L σ K u i i : ℤ) : ℝ) := by exact_mod_cast h
    calc _ ≤ ((η * n * Qz L σ K u i i : ℤ) : ℝ) := h'
      _ = (η : ℝ) * (n * (Qz L σ K u i i : ℝ)) := by push_cast; ring

theorem rho_lt (hτ : 0 < tauz L σ K u) (i : Fin n) :
    η * rho L σ K u i < (dz L η σ K u i : ℝ) + 1 := by
  unfold rho dz
  have hτr : (0 : ℝ) < (tauz L σ K u : ℝ) := by exact_mod_cast hτ
  rw [← mul_div_assoc, div_lt_iff₀ hτr]
  have h := Int.lt_ediv_add_one_mul_self (η * n * Qz L σ K u i i) hτ
  have h' : ((η * n * Qz L σ K u i i : ℤ) : ℝ) <
      (((η * n * Qz L σ K u i i / tauz L σ K u : ℤ) : ℝ) + 1) * (tauz L σ K u : ℝ) := by
    exact_mod_cast h
  calc (η : ℝ) * (n * (Qz L σ K u i i : ℝ)) = ((η * n * Qz L σ K u i i : ℤ) : ℝ) := by
        push_cast; ring
    _ < _ := h'

include hL in
theorem pz_le_pt : (pz L σ K u : ℝ) ≤ pt L σ K u := by
  unfold pt pz
  by_cases hτ : tauz L σ K u = 0
  · rw [hτ, Int.ediv_zero]
    simp
  · have hτpos : 0 < tauz L σ K u := lt_of_le_of_ne (tauz_nonneg hL σ K u) (Ne.symm hτ)
    have hτr : (0 : ℝ) < (tauz L σ K u : ℝ) := by exact_mod_cast hτpos
    rw [le_div_iff₀ hτr]
    have h := Int.ediv_mul_le (n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j) hτ
    have h' : (((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j) / tauz L σ K u : ℤ) : ℝ) *
        (tauz L σ K u : ℝ) ≤ ((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j : ℤ) : ℝ) := by
      exact_mod_cast h
    calc _ ≤ ((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j : ℤ) : ℝ) := h'
      _ = _ := by push_cast; rfl

theorem pt_lt (hτ : 0 < tauz L σ K u) : pt L σ K u < (pz L σ K u : ℝ) + 1 := by
  unfold pt pz
  have hτr : (0 : ℝ) < (tauz L σ K u : ℝ) := by exact_mod_cast hτ
  rw [div_lt_iff₀ hτr]
  have h := Int.lt_ediv_add_one_mul_self (n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j) hτ
  have h' : ((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j : ℤ) : ℝ) <
      ((((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j) / tauz L σ K u : ℤ) : ℝ) + 1) *
        (tauz L σ K u : ℝ) := by exact_mod_cast h
  calc _ = ((n * ∑ i, ∑ j, L i j * (Qz L σ K u) i j : ℤ) : ℝ) := by push_cast; rfl
    _ < _ := h'

end basic

end QMCSub


