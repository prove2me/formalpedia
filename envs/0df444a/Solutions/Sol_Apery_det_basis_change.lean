-- Prove2me | solution 1 for Apery.det_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:50:10.920058+00:00
-- url     : https://prove2.me/submissions/66057220-4927-4c18-b753-8236e8d6d5ae

/-
# Change of basis in the Hankel determinant (`Apery/Arith/BasisChange.lean`)

`Apery.det_basis_change`: for polynomials `E a` of degree `< 37 n`, the Hankel matrix of
`mu_X (D (3n)^6 * E a * E b)` equals `C ((coeffMat E).det^2) * Δ n`. Together with
`Apery/PartialFractions.lean` this is the algebraic core of the small-prime bound and the
`T`-key bound for `integral_mN`.

Faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Degree.lean` + `Apery/PartialFractions.lean` + `Apery/Arith/BasisChange.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Polynomial Matrix Finset

namespace Apery

lemma coeff_det_of_natDegree_le_one {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (M.det).coeff n = (Matrix.of fun i j => (M i j).coeff 1).det ∧ M.det.natDegree ≤ n := by
  constructor
  · rw [det_apply', det_apply', finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hc := coeff_prod_of_natDegree_le (s := Finset.univ) (f := fun i => M (σ i) i) (n := 1)
      (fun i _ => hM _ _)
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hc
    rw [← C_eq_intCast, coeff_C_mul, hc]
    simp
  · rw [det_apply']
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_intCast, zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i : Fin n, (M (σ i) i).natDegree ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp


noncomputable def res (K : ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)

lemma poleValue_eq (j : ℕ) : poleValue j =
    C ((j : ℚ) ^ 4) * X + C (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ))) := by
  simp only [poleValue, C_add, C_sub, C_mul, C_neg, C_pow]
  ring

lemma μX_eq (K : ℕ) (P : ℚ[X]) : μX K P =
    C (∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4) * X +
    C (μpoly (P /ₘ D K) +
      ∑ j ∈ Icc 1 K, res K P j * (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ)))) := by
  simp only [μX, res, poleValue_eq, mul_add, ← mul_assoc, ← C_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum, C_add]
  ring

lemma natDegree_μX_le (K : ℕ) (P : ℚ[X]) : (μX K P).natDegree ≤ 1 := by
  rw [μX_eq]
  compute_degree!

lemma coeff_μX_one (K : ℕ) (P : ℚ[X]) :
    (μX K P).coeff 1 = ∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4 := by
  rw [μX_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, mul_one, one_ne_zero, ite_false, add_zero]

lemma eval_D (m : ℕ) (x : ℚ) : (D m).eval x = ∏ j ∈ Icc 1 m, (x + (j : ℚ) ^ 2) := by
  simp [D, eval_prod]

lemma eval_D_eq_zero {m j : ℕ} (hj : j ∈ Icc 1 m) : (D m).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hj (by ring)

lemma eval_D_ne_zero {m j : ℕ} (hj : m < j) : (D m).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_D]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : (i : ℚ) < j := by exact_mod_cast (by omega : i < j)
  have h2 : (0 : ℚ) ≤ i := by positivity
  nlinarith

lemma eval_derivative_D {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) = ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  rw [D, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single j]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_mul, eval_one, mul_one,
      eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro b _ hb
    rw [eval_mul, eval_prod]
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb.symm, hj⟩) (by simp)) _
  · intro h; exact absurd hj h

lemma eval_derivative_D_ne_zero {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_derivative_D hj]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : (i : ℚ) ≠ j := by exact_mod_cast hij
  have h0i : (0 : ℚ) ≤ i := by positivity
  have h0j : (0 : ℚ) ≤ j := by positivity
  intro h
  have hfac : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact this (by linarith)
  · have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith

/-- Reindexing: a sum over `Icc 1 K` whose terms vanish on `Icc 1 N` is a sum over
`k : Fin (K - N)` of the terms at `N + 1 + k`. -/
lemma sum_Icc_eq_sum_fin (N K : ℕ) (hNK : N ≤ K) (f : ℕ → ℚ) (hf : ∀ j ∈ Icc 1 N, f j = 0) :
    ∑ j ∈ Icc 1 K, f j = ∑ k : Fin (K - N), f (N + 1 + k) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (N + 1 + k)) (K - N)]
  have h1 := Finset.sum_Ico_eq_sum_range f (N + 1) (K + 1)
  rw [show K + 1 - (N + 1) = K - N by omega] at h1
  rw [← h1]
  have h2 : Icc 1 K = Ico 1 (K + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, ← Finset.sum_Ico_consecutive f (show 1 ≤ N + 1 by omega) (show N + 1 ≤ K + 1 by omega)]
  rw [Finset.sum_eq_zero (fun j hj => hf j ?_), zero_add]
  rw [Finset.mem_Ico] at hj
  rw [Finset.mem_Icc]; omega

/-- The nodes `x_k = -(N + 1 + k)²`, `k < h`. -/
noncomputable def node (n : ℕ) (k : Fin (37 * n)) : ℚ := -((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 2

/-- The weights `w_k = D_N(x_k)^6 (N + 1 + k)^4 / D_K'(x_k)`. -/
noncomputable def weight (n : ℕ) (k : Fin (37 * n)) : ℚ :=
  (D (3 * n)).eval (node n k) ^ 6 * ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 4 /
    (derivative (D (40 * n))).eval (node n k)

lemma natDegree_G_le (n : ℕ) (i j : Fin (37 * n)) : (G n i j).natDegree ≤ 1 :=
  natDegree_μX_le _ _

/-- The matrix of `X`-coefficients of `G_K(X)` is `Vᵀ diag(w) V` with `V` the Vandermonde
matrix of the nodes. -/
lemma coeff_G_one (n : ℕ) : (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1) =
    (vandermonde (node n))ᵀ * diagonal (weight n) * vandermonde (node n) := by
  ext i j
  simp only [Matrix.of_apply, G, coeff_μX_one, res]
  rw [sum_Icc_eq_sum_fin (3 * n) (40 * n) (by omega)
    (fun j' => eval (-(j' : ℚ) ^ 2) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) /
      eval (-(j' : ℚ) ^ 2) (derivative (D (40 * n))) * (j' : ℚ) ^ 4)
    (fun j' hj' => by rw [eval_mul, eval_pow, eval_D_eq_zero hj']; simp)]
  rw [show 40 * n - 3 * n = 37 * n by omega]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, vandermonde_apply, weight, node,
    eval_mul, eval_pow, eval_X]
  rw [pow_add]
  ring

lemma node_injective (n : ℕ) : Function.Injective (node n) := by
  intro k₁ k₂ h
  simp only [node, neg_inj] at h
  have h' : (3 * n + 1 + (k₁ : ℕ)) ^ 2 = (3 * n + 1 + (k₂ : ℕ)) ^ 2 := by exact_mod_cast h
  have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h'
  exact Fin.ext (by omega)

lemma weight_ne_zero (n : ℕ) (k : Fin (37 * n)) : weight n k ≠ 0 := by
  have hk := k.isLt
  have h1 : (D (3 * n)).eval (node n k) ≠ 0 := eval_D_ne_zero (by omega)
  have h2 : (derivative (D (40 * n))).eval (node n k) ≠ 0 :=
    eval_derivative_D_ne_zero (by rw [Finset.mem_Icc]; omega)
  have h3 : ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ≠ 0 := by positivity
  unfold weight
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h3)) h2

lemma det_coeff_G_one_ne_zero (n : ℕ) :
    (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1).det ≠ 0 := by
  rw [coeff_G_one, det_mul, det_mul, det_transpose, det_diagonal]
  have hV : (vandermonde (node n)).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr (node_injective n)
  exact mul_ne_zero (mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr fun k _ => weight_ne_zero n k)) hV

/-- **(2.9)**: `Δ_K` has degree exactly `h = 37 n`. -/
theorem natDegree_Δ (n : ℕ) : (Δ n).natDegree = 37 * n := by
  obtain ⟨hc, hd⟩ := coeff_det_of_natDegree_le_one (G n) (natDegree_G_le n)
  exact natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ det_coeff_G_one_ne_zero n)

lemma S_pos (n : ℕ) : 0 < S n := by
  unfold S
  positivity

/-- **(2.9)**: `F_K` has degree exactly `h = 37 n`. -/
theorem natDegree_F (n : ℕ) : (F n).natDegree = 37 * n := by
  rw [F, natDegree_C_mul (S_pos n).ne', natDegree_Δ]

lemma D_monic (K : ℕ) : (D K).Monic := by
  unfold D; exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma natDegree_D (K : ℕ) : (D K).natDegree = K := by
  unfold D; rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

/-- The polynomial identity behind the partial fractions: the remainder `P %ₘ D_K` equals
`∑_j res_j ∏_{i ≠ j} (X + i²)`. -/
lemma modByMonic_eq_sum_res (K : ℕ) (P : ℚ[X]) :
    P %ₘ D K = ∑ j ∈ Icc 1 K, C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2)) := by
  have hnodes : Set.InjOn (fun j : ℕ => -(j : ℚ) ^ 2) (Icc 1 K : Set ℕ) := by
    intro a _ b _ hab
    have h1 : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := by simpa using hab
    have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective two_ne_zero h2
  set s : Finset ℚ := (Icc 1 K).image (fun j : ℕ => -(j : ℚ) ^ 2) with hs
  have hcard : s.card = K := by
    rw [hs, Finset.card_image_of_injOn hnodes]; simp
  -- degree of each summand
  have hterm : ∀ j ∈ Icc 1 K,
      (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree < K := by
    intro j hj
    have hK : 1 ≤ K := (Finset.mem_Icc.mp hj).2.trans' (Finset.mem_Icc.mp hj).1
    have hprod : (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).natDegree = K - 1 := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
      simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hj, Nat.card_Icc]
      omega
    calc (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree
        ≤ (C (res K P j)).degree + (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree :=
          degree_mul_le _ _
      _ ≤ 0 + ((K - 1 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact degree_C_le
          · rw [← hprod]; exact degree_le_natDegree
      _ < K := by
          rw [zero_add]; exact_mod_cast (by omega : K - 1 < K)
  refine eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · rw [hcard]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rcases eq_or_ne (P %ₘ D K) 0 with h | h
      · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
      · have := degree_modByMonic_lt P (D_monic K)
        rwa [degree_eq_natDegree (D_monic K).ne_zero, natDegree_D] at this
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hterm
  · intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨j₀, hj₀, rfl⟩ := hx
    -- LHS: `(P %ₘ D_K)(-j₀²) = P(-j₀²)`
    have hL : (P %ₘ D K).eval (-(j₀ : ℚ) ^ 2) = P.eval (-(j₀ : ℚ) ^ 2) := by
      conv_rhs => rw [← modByMonic_add_div P (D K)]
      rw [eval_add, eval_mul, eval_D_eq_zero hj₀, zero_mul, add_zero]
    rw [hL, eval_finsetSum, Finset.sum_eq_single j₀]
    · rw [eval_mul, eval_C, eval_prod, res, eval_derivative_D hj₀]
      have hne := eval_derivative_D_ne_zero hj₀
      rw [eval_derivative_D hj₀] at hne
      have : ∏ i ∈ (Icc 1 K).erase j₀, eval (-(j₀ : ℚ) ^ 2) (X + C ((i : ℚ) ^ 2)) =
          ∏ i ∈ (Icc 1 K).erase j₀, ((i : ℚ) ^ 2 - (j₀ : ℚ) ^ 2) :=
        Finset.prod_congr rfl fun i _ => by simp; ring
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjne
      rw [eval_mul, eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := j₀) ?_ ?_)
      · exact Finset.mem_erase.mpr ⟨fun h => hjne h.symm, hj₀⟩
      · simp
    · intro h; exact absurd hj₀ h

lemma aeval_D_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < aeval t (D m) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.prod_pos fun j hj => ?_
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  positivity

/-- **Partial fractions** as real functions, for `t ≥ 0`. -/
theorem partial_fractions (K : ℕ) (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    aeval t P / aeval t (D K) =
      aeval t (P /ₘ D K) + ∑ j ∈ Icc 1 K, (res K P j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hD : 0 < aeval t (D K) := aeval_D_pos K ht
  have hsplit : aeval t P = aeval t (P %ₘ D K) + aeval t (D K) * aeval t (P /ₘ D K) := by
    conv_lhs => rw [← modByMonic_add_div P (D K)]
    rw [map_add, map_mul]
  rw [hsplit, add_div, mul_div_cancel_left₀ _ hD.ne', add_comm]
  congr 1
  rw [modByMonic_eq_sum_res, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, aeval_C, map_prod]
  simp only [map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  have hj2 : 0 < t + (j : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    positivity
  have hDt : aeval t (D K) = (t + (j : ℝ) ^ 2) * ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) := by
    simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
    rw [← Finset.mul_prod_erase _ _ hj]
  rw [hDt]
  have hprod : 0 < ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) :=
    Finset.prod_pos fun i hi => by
      have : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      positivity
  field_simp

lemma divByMonic_add' {q : ℚ[X]} (hq : q.Monic) (P Q : ℚ[X]) :
    (P + Q) /ₘ q = P /ₘ q + Q /ₘ q := by
  refine ((div_modByMonic_unique (P /ₘ q + Q /ₘ q) (P %ₘ q + Q %ₘ q) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    have h2 := modByMonic_add_div Q q
    rw [mul_add]; linear_combination h1 + h2
  · exact (degree_add_le _ _).trans_lt (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul' {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (P : ℚ[X]) :
    (C c * P) /ₘ q = C c * (P /ₘ q) := by
  refine ((div_modByMonic_unique (C c * (P /ₘ q)) (C c * (P %ₘ q)) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    linear_combination C c * h1
  · rw [← smul_eq_C_mul]; exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma μpoly_add (P Q : ℚ[X]) : μpoly (P + Q) = μpoly P + μpoly Q := by
  unfold μpoly
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma μpoly_C_mul (c : ℚ) (P : ℚ[X]) : μpoly (C c * P) = c * μpoly P := by
  unfold μpoly
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum,
    Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma μX_add (K : ℕ) (P Q : ℚ[X]) : μX K (P + Q) = μX K P + μX K Q := by
  unfold μX
  rw [divByMonic_add' (D_monic K), μpoly_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma μX_C_mul (K : ℕ) (c : ℚ) (P : ℚ[X]) : μX K (C c * P) = C c * μX K P := by
  unfold μX
  rw [divByMonic_C_mul' (D_monic K), μpoly_C_mul, map_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]; ring

lemma μX_sum {ι : Type*} (K : ℕ) (s : Finset ι) (f : ι → ℚ[X]) :
    μX K (∑ i ∈ s, f i) = ∑ i ∈ s, μX K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := μX_C_mul K 0 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, μX_add, ih]

/-- The coefficient matrix of a family of polynomials. -/
noncomputable def coeffMat {h : ℕ} (E : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a k => (E a).coeff k

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X]) (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) := by
  conv_lhs => rw [as_sum_range' (E a) h (hE a)]
  rw [Finset.sum_range (fun k => monomial k ((E a).coeff k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeffMat, Matrix.of_apply, C_mul_X_pow_eq_monomial]

/-- **Change of basis**. -/
theorem det_basis_change (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((Matrix.of (fun a k => (E a).coeff k : Fin (37 * n) → Fin (37 * n) → ℚ)).det ^ 2) * Δ n := by
  change (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
    C ((coeffMat E).det ^ 2) * Δ n
  set Cm := (coeffMat E).map (C : ℚ →+* ℚ[X]) with hCm
  have hM : (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) =
      Cm * G n * Cm.transpose := by
    refine Matrix.ext fun a b => ?_
    have hexp : D (3 * n) ^ 6 * E a * E b = ∑ k : Fin (37 * n), ∑ l : Fin (37 * n),
        C (coeffMat E a k * coeffMat E b l) * (D (3 * n) ^ 6 * X ^ ((k : ℕ) + (l : ℕ))) := by
      rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [Matrix.of_apply, hexp, μX_sum]
    simp only [μX_sum, μX_C_mul, Matrix.mul_apply, Matrix.transpose_apply, hCm, Matrix.map_apply, G,
      Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCm, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, Δ, map_pow]; ring

end Apery

end Port0

open Polynomial Matrix Finset in
/-- The platform target `Apery.det_basis_change`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => Apery.μX (40 * n) (Apery.D (3 * n) ^ 6 * E a * E b)).det =
      Polynomial.C ((Matrix.of (fun a k => (E a).coeff k : Fin (37 * n) → Fin (37 * n) → ℚ)).det ^ 2) * Apery.Δ n :=
  Apery.det_basis_change n E hE
