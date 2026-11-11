-- Prove2me | Definitions.Def_QMCSub_Lap
-- name    : QMCSub_Lap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:17:05.37362+00:00
-- url     : https://prove2.me/theorems/f29681eb-b8a1-4d60-b520-1cbb91a432e8
-- title:
--   Integer Laplacian of scaled rounded weights and the Max-Cut relaxation objective
-- statement:
--   For an input graph with symmetric weight matrix $A$ and total weight $W>0$, let $N_{ij}=\lfloor\Omega A_{ij}/W\rfloor$ and let $L$ be the Laplacian of $N$. Then $L$ is symmetric and positive semidefinite, $0<\operatorname{tr}L\le2\Omega$ when $\Omega\ge n^2$, and $\langle L,X\rangle\le4\Omega$ for every positive semidefinite $X$ with unit diagonal. For such $X$ the relaxation objective $f_A(X)=\tfrac14\sum_{i,j}A_{ij}(1-X_{ij})$ satisfies
--   $$\frac{W}{\Omega}\cdot\frac{\langle L,X\rangle}{4}\le f_A(X)\le\frac{W}{\Omega}\cdot\frac{\langle L,X\rangle+2n^2}{4},$$
--   and $0\le f_A(X)\le W$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter

/-!
The integer Laplacian of the scaled, rounded-down weights of an input graph, and how its
quadratic form compares with the Max-Cut relaxation objective.
-/

namespace QMCSub
open QuantumMaxCutEnergy Matrix
open scoped BigOperators

/-- The symmetric rational weight matrix of an input graph. -/
def Aq (G : Input) (i j : Fin G.n) : ℚ :=
  if h : i < j then (G.weights ⟨(i, j), h⟩ : ℚ)
  else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℚ) else 0

/-- Total weight. -/
def Wq (G : Input) : ℚ := ∑ e, (G.weights e : ℚ)

/-- Scaled and rounded-down weights. -/
def Nz (Om : ℕ) (G : Input) (i j : Fin G.n) : ℤ := ⌊(Om : ℚ) * Aq G i j / Wq G⌋

/-- Integer Laplacian of the scaled weights. -/
def Lz (Om : ℕ) (G : Input) : Matrix (Fin G.n) (Fin G.n) ℤ :=
  Matrix.of fun i j => if i = j then ∑ k, Nz Om G i k else -Nz Om G i j

/-- The real weight matrix exactly as it appears in the target statement. -/
noncomputable def Ar (G : Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

theorem Aq_cast (G : Input) (i j : Fin G.n) : ((Aq G i j : ℚ) : ℝ) = Ar G i j := by
  unfold Aq Ar
  rw [Matrix.of_apply]
  split_ifs
  · exact Rat.cast_nnratCast _
  · exact Rat.cast_nnratCast _
  · exact Rat.cast_zero

theorem Aq_symm (G : Input) (i j : Fin G.n) : Aq G i j = Aq G j i := by
  unfold Aq
  rcases lt_trichotomy i j with h | h | h
  · simp only [dif_pos h, dif_neg (not_lt.mpr h.le)]
  · subst h; rfl
  · simp only [dif_pos h, dif_neg (not_lt.mpr h.le)]

theorem Aq_nonneg (G : Input) (i j : Fin G.n) : 0 ≤ Aq G i j := by
  unfold Aq
  split_ifs
  · exact NNRat.coe_nonneg _
  · exact NNRat.coe_nonneg _
  · exact le_rfl

theorem Aq_self (G : Input) (i : Fin G.n) : Aq G i i = 0 := by
  unfold Aq
  simp only [dif_neg (lt_irrefl i)]

/-- A sum over edges, as a double sum over ordered pairs. -/
theorem lap_sum_edge_eq {n : ℕ} (g : Edge n → ℚ) :
    ∑ e, g e = ∑ i : Fin n, ∑ j : Fin n, if h : i < j then g ⟨(i, j), h⟩ else 0 := by
  classical
  let f : Fin n × Fin n → ℚ := fun p => if h : p.1 < p.2 then g ⟨p, h⟩ else 0
  have hf : (∑ p, f p) = ∑ e, g e := by
    apply Finset.sum_congr_set {p : Fin n × Fin n | p.1 < p.2} f g
    · intro p hp
      change p.1 < p.2 at hp
      simp only [f, dif_pos hp]
    · intro p hp
      change ¬p.1 < p.2 at hp
      simp only [f, dif_neg hp]
  rw [← hf, Fintype.sum_prod_type]

theorem Aq_split (G : Input) (i j : Fin G.n) :
    Aq G i j = (if h : i < j then (G.weights ⟨(i, j), h⟩ : ℚ) else 0) +
      (if h : j < i then (G.weights ⟨(j, i), h⟩ : ℚ) else 0) := by
  unfold Aq
  rcases lt_trichotomy i j with h | h | h
  · simp only [dif_pos h, dif_neg (not_lt.mpr h.le), add_zero]
  · subst h
    simp only [dif_neg (lt_irrefl i), add_zero]
  · simp only [dif_pos h, dif_neg (not_lt.mpr h.le), zero_add]

theorem sum_Aq (G : Input) : ∑ i, ∑ j, Aq G i j = 2 * Wq G := by
  have h1 : Wq G = ∑ i : Fin G.n, ∑ j : Fin G.n,
      (if h : i < j then (G.weights ⟨(i, j), h⟩ : ℚ) else 0) :=
    lap_sum_edge_eq (fun e : Edge G.n => (G.weights e : ℚ))
  have h2 : ∑ i : Fin G.n, ∑ j : Fin G.n,
      (if h : j < i then (G.weights ⟨(j, i), h⟩ : ℚ) else 0) = Wq G := by
    rw [Finset.sum_comm]
    exact h1.symm
  simp only [Aq_split, Finset.sum_add_distrib]
  rw [h2, ← h1]
  ring

theorem Wq_nonneg (G : Input) : 0 ≤ Wq G := by
  unfold Wq
  exact Finset.sum_nonneg fun e _ => NNRat.coe_nonneg _

theorem Nz_nonneg (Om : ℕ) (G : Input) (i j : Fin G.n) : 0 ≤ Nz Om G i j := by
  unfold Nz
  rw [Int.floor_nonneg]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Aq_nonneg G i j)) (Wq_nonneg G)

theorem Nz_self (Om : ℕ) (G : Input) (i : Fin G.n) : Nz Om G i i = 0 := by
  unfold Nz
  rw [Aq_self, mul_zero, zero_div, Int.floor_zero]

theorem Nz_symm (Om : ℕ) (G : Input) (i j : Fin G.n) : Nz Om G i j = Nz Om G j i := by
  unfold Nz
  rw [Aq_symm G i j]

theorem Nz_le (Om : ℕ) (G : Input) (i j : Fin G.n) :
    (Nz Om G i j : ℚ) ≤ (Om : ℚ) * Aq G i j / Wq G := by
  unfold Nz
  exact Int.floor_le _

theorem lt_Nz_add_one (Om : ℕ) (G : Input) (i j : Fin G.n) :
    (Om : ℚ) * Aq G i j / Wq G < (Nz Om G i j : ℚ) + 1 := by
  unfold Nz
  exact Int.lt_floor_add_one _

theorem Lz_apply (Om : ℕ) (G : Input) (i j : Fin G.n) :
    Lz Om G i j = if i = j then ∑ k, Nz Om G i k else -Nz Om G i j := rfl

theorem Lz_symm (Om : ℕ) (G : Input) (i j : Fin G.n) : Lz Om G i j = Lz Om G j i := by
  rw [Lz_apply, Lz_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (fun e => h e.symm), Nz_symm Om G i j]

theorem Lz_trace (Om : ℕ) (G : Input) : (Lz Om G).trace = ∑ i, ∑ k, Nz Om G i k := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Lz_apply, if_pos rfl]

/-- The Laplacian form against any matrix, in terms of the scaled weights. -/
theorem Lz_sum (Om : ℕ) (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ) :
    ∑ i, ∑ j, (Lz Om G i j : ℝ) * X i j =
      ∑ i, ∑ j, (Nz Om G i j : ℝ) * (X i i - X i j) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, (Lz Om G i j : ℝ) * X i j =
      (if i = j then (∑ k, (Nz Om G i k : ℝ)) * X i j else 0) -
        (Nz Om G i j : ℝ) * X i j := by
    intro j
    rw [Lz_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, Nz_self]
      push_cast
      ring
    · rw [if_neg hij, if_neg hij]
      push_cast
      ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Lz_sum_unit (Om : ℕ) (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (h1 : ∀ i, X i i = 1) :
    ∑ i, ∑ j, (Lz Om G i j : ℝ) * X i j =
      ∑ i, ∑ j, (Nz Om G i j : ℝ) * (1 - X i j) := by
  rw [Lz_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h1 i]

theorem Lz_psd (Om : ℕ) (G : Input) : (castM (Lz Om G)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    rw [castM_apply, castM_apply, star_trivial, Lz_symm Om G j i]
  · intro x
    have h1 : star x ⬝ᵥ (castM (Lz Om G) *ᵥ x) =
        ∑ i, ∑ j, (Lz Om G i j : ℝ) * (x i * x j) := by
      rw [star_trivial]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, castM_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 : ∑ i, ∑ j, (Lz Om G i j : ℝ) * (x i * x j) =
        ∑ i, ∑ j, (Nz Om G i j : ℝ) * (x i * x i - x i * x j) :=
      Lz_sum Om G (fun i j => x i * x j)
    have h3 : ∑ i, ∑ j, (Nz Om G i j : ℝ) * (x i * x i - x i * x j) =
        ∑ i, ∑ j, (Nz Om G i j : ℝ) * (x j * x j - x i * x j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Nz_symm Om G j i]
      ring
    have h4 : 0 ≤ ∑ i, ∑ j, (Nz Om G i j : ℝ) * (x i * x i - x i * x j) +
        ∑ i, ∑ j, (Nz Om G i j : ℝ) * (x j * x j - x i * x j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_nonneg fun j _ => ?_
      have hN : (0 : ℝ) ≤ (Nz Om G i j : ℝ) := by exact_mod_cast Nz_nonneg Om G i j
      have e : (Nz Om G i j : ℝ) * (x i * x i - x i * x j) +
          (Nz Om G i j : ℝ) * (x j * x j - x i * x j) =
            (Nz Om G i j : ℝ) * (x i - x j) ^ 2 := by ring
      rw [e]
      exact mul_nonneg hN (sq_nonneg _)
    rw [h1, h2]
    linarith

theorem sum_Nz_le (Om : ℕ) (G : Input) (hW : 0 < Wq G) :
    ∑ i, ∑ j, Nz Om G i j ≤ 2 * (Om : ℤ) := by
  have h : ((∑ i, ∑ j, Nz Om G i j : ℤ) : ℚ) ≤ ((2 * (Om : ℤ) : ℤ) : ℚ) := by
    push_cast
    calc ∑ i, ∑ j, (Nz Om G i j : ℚ)
        ≤ ∑ i, ∑ j, (Om : ℚ) * Aq G i j / Wq G :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Nz_le Om G i j
      _ = (Om : ℚ) * (∑ i, ∑ j, Aq G i j) / Wq G := by
          simp only [Finset.mul_sum, Finset.sum_div]
      _ = 2 * (Om : ℚ) := by
          rw [sum_Aq]
          field_simp
  exact_mod_cast h

theorem Nz_row_le (Om : ℕ) (G : Input) (i : Fin G.n) :
    ∑ k, Nz Om G i k ≤ ∑ i, ∑ k, Nz Om G i k :=
  Finset.single_le_sum (f := fun i => ∑ k, Nz Om G i k)
    (fun i _ => Finset.sum_nonneg fun k _ => Nz_nonneg Om G i k) (Finset.mem_univ i)

theorem Nz_le_row (Om : ℕ) (G : Input) (i j : Fin G.n) :
    Nz Om G i j ≤ ∑ k, Nz Om G i k :=
  Finset.single_le_sum (f := fun k => Nz Om G i k)
    (fun k _ => Nz_nonneg Om G i k) (Finset.mem_univ j)

/-- With scale at least `n^2`, some scaled weight is at least one. -/
theorem exists_Nz_pos (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : G.n ^ 2 ≤ Om) :
    ∃ i j, 1 ≤ Nz Om G i j := by
  by_contra hex
  have hcon : ∀ i j, Nz Om G i j < 1 := fun i j => by
    by_contra hge
    exact hex ⟨i, j, not_lt.mp hge⟩
  have hn : 0 < G.n := by
    rcases Nat.eq_zero_or_pos G.n with h0 | h
    · exfalso
      have hs := sum_Aq G
      have : IsEmpty (Fin G.n) := by rw [h0]; infer_instance
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
      linarith
    · exact h
  have hOmpos : (0 : ℚ) < (Om : ℚ) := by
    have : 0 < Om := lt_of_lt_of_le (pow_pos hn 2) hOm
    exact_mod_cast this
  have hOmq : (G.n : ℚ) ^ 2 ≤ (Om : ℚ) := by exact_mod_cast hOm
  have hterm : ∀ i j, (Om : ℚ) * Aq G i j ≤ Wq G := by
    intro i j
    have h1 := lt_Nz_add_one Om G i j
    have h2 : (Nz Om G i j : ℚ) + 1 ≤ 1 := by
      have h2' : Nz Om G i j + 1 ≤ 1 := by
        have := hcon i j
        omega
      exact_mod_cast h2'
    have h3 : (Om : ℚ) * Aq G i j / Wq G < 1 := lt_of_lt_of_le h1 h2
    rw [div_lt_one hW] at h3
    exact h3.le
  have hsum : ∑ i, ∑ j, (Om : ℚ) * Aq G i j ≤ ∑ _i : Fin G.n, ∑ _j : Fin G.n, Wq G :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hL : ∑ i, ∑ j, (Om : ℚ) * Aq G i j = (Om : ℚ) * (2 * Wq G) := by
    rw [← sum_Aq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hR : ∑ _i : Fin G.n, ∑ _j : Fin G.n, Wq G = (G.n : ℚ) ^ 2 * Wq G := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hL, hR] at hsum
  have h5 : (G.n : ℚ) ^ 2 * Wq G ≤ (Om : ℚ) * Wq G := mul_le_mul_of_nonneg_right hOmq hW.le
  have h6 : 0 < (Om : ℚ) * Wq G := mul_pos hOmpos hW
  linarith

theorem Lz_feas_le (Om : ℕ) (G : Input) (hW : 0 < Wq G) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : X.PosSemidef) (h1 : ∀ i, X i i = 1) :
    ∑ i, ∑ j, (Lz Om G i j : ℝ) * X i j ≤ 4 * ((Om : ℤ) : ℝ) := by
  rw [Lz_sum_unit Om G X h1]
  have hs : ((∑ i, ∑ j, Nz Om G i j : ℤ) : ℝ) ≤ ((2 * (Om : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast sum_Nz_le Om G hW
  push_cast at hs
  calc ∑ i, ∑ j, (Nz Om G i j : ℝ) * (1 - X i j)
      ≤ ∑ i, ∑ j, (Nz Om G i j : ℝ) * 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hN : (0 : ℝ) ≤ (Nz Om G i j : ℝ) := by exact_mod_cast Nz_nonneg Om G i j
        have hx := (abs_le.mp (psd_unitDiag_abs_le_one hX h1 i j)).1
        exact mul_le_mul_of_nonneg_left (by linarith) hN
    _ = 2 * ∑ i, ∑ j, (Nz Om G i j : ℝ) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 4 * ((Om : ℤ) : ℝ) := by
        push_cast
        linarith

/-- With positive total weight and scale at least `n^2`, the integer Laplacian satisfies the
hypotheses of the iteration analysis with `w = Om`. -/
theorem lapHyp (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : G.n ^ 2 ≤ Om) :
    LapHyp (Lz Om G) (Om : ℤ) := by
  refine ⟨Lz_symm Om G, Lz_psd Om G, ?_, ?_, fun X hX h1 => Lz_feas_le Om G hW X hX h1⟩
  · rw [Lz_trace]
    obtain ⟨i, j, hij⟩ := exists_Nz_pos Om G hW hOm
    have h1 := Nz_le_row Om G i j
    have h2 := Nz_row_le Om G i
    linarith
  · rw [Lz_trace]
    exact sum_Nz_le Om G hW

theorem Lz_abs_le (Om : ℕ) (G : Input) (hW : 0 < Wq G) (i j : Fin G.n) :
    |Lz Om G i j| ≤ 2 * (Om : ℤ) := by
  have hrow := Nz_row_le Om G i
  have htot := sum_Nz_le Om G hW
  rw [Lz_apply]
  by_cases h : i = j
  · rw [if_pos h, abs_of_nonneg (Finset.sum_nonneg fun k _ => Nz_nonneg Om G i k)]
    linarith
  · rw [if_neg h, abs_neg, abs_of_nonneg (Nz_nonneg Om G i j)]
    have h1 := Nz_le_row Om G i j
    linarith

theorem Nz_scaled_le (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : 0 < Om) (i j : Fin G.n) :
    ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (Nz Om G i j : ℝ) ≤ Ar G i j := by
  have hOmq : (0 : ℚ) < (Om : ℚ) := by exact_mod_cast hOm
  have h := Nz_le Om G i j
  rw [le_div_iff₀ hW] at h
  have h2 : Wq G / (Om : ℚ) * (Nz Om G i j : ℚ) ≤ Aq G i j := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hOmq]
    linarith
  have h3 : ((Wq G / (Om : ℚ) * (Nz Om G i j : ℚ) : ℚ) : ℝ) ≤ ((Aq G i j : ℚ) : ℝ) := by
    exact_mod_cast h2
  rw [Aq_cast] at h3
  push_cast at h3
  exact h3

theorem Ar_le_scaled (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : 0 < Om) (i j : Fin G.n) :
    Ar G i j ≤ ((Wq G : ℚ) : ℝ) / (Om : ℝ) * ((Nz Om G i j : ℝ) + 1) := by
  have hOmq : (0 : ℚ) < (Om : ℚ) := by exact_mod_cast hOm
  have h := (lt_Nz_add_one Om G i j).le
  rw [div_le_iff₀ hW] at h
  have h2 : Aq G i j ≤ Wq G / (Om : ℚ) * ((Nz Om G i j : ℚ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hOmq]
    linarith
  have h3 : ((Aq G i j : ℚ) : ℝ) ≤
      ((Wq G / (Om : ℚ) * ((Nz Om G i j : ℚ) + 1) : ℚ) : ℝ) := by
    exact_mod_cast h2
  rw [Aq_cast] at h3
  push_cast at h3
  exact h3

theorem Ar_nonneg (G : Input) (i j : Fin G.n) : 0 ≤ Ar G i j := by
  rw [← Aq_cast]
  exact_mod_cast Aq_nonneg G i j

theorem sum_Ar (G : Input) : ∑ i, ∑ j, Ar G i j = 2 * ((Wq G : ℚ) : ℝ) := by
  have h : ((∑ i, ∑ j, Aq G i j : ℚ) : ℝ) = ((2 * Wq G : ℚ) : ℝ) := by rw [sum_Aq]
  push_cast at h
  simpa only [Aq_cast] using h

theorem lap_sum_affine {n : ℕ} (c : ℝ) (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (c * f i j + c * 2) = c * (∑ i, ∑ j, f i j) + c * (2 * (n : ℝ) ^ 2) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  ring

/-- The scaled Laplacian form is a lower bound for the relaxation objective. -/
theorem obj_lower (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : 0 < Om)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (∑ i, ∑ j, (Lz Om G i j : ℝ) * X i j) / 4 ≤
      ModernConvex.Relaxations.maxcutRelaxationObjective (Ar G) X := by
  obtain ⟨hpsd, h1⟩ := hX
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  rw [Lz_sum_unit Om G X h1]
  have key : ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (∑ i, ∑ j, (Nz Om G i j : ℝ) * (1 - X i j)) ≤
      ∑ i, ∑ j, Ar G i j * (1 - X i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hx := (abs_le.mp (psd_unitDiag_abs_le_one hpsd h1 i j)).2
    have hs := Nz_scaled_le Om G hW hOm i j
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hs (by linarith)
  linarith

/-- The scaled Laplacian form is an upper bound up to the rounding loss. -/
theorem obj_upper (Om : ℕ) (G : Input) (hW : 0 < Wq G) (hOm : 0 < Om)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (Ar G) X ≤
      ((Wq G : ℚ) : ℝ) / (Om : ℝ) *
        (∑ i, ∑ j, (Lz Om G i j : ℝ) * X i j + 2 * (G.n : ℝ) ^ 2) / 4 := by
  obtain ⟨hpsd, h1⟩ := hX
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  rw [Lz_sum_unit Om G X h1]
  have hc : (0 : ℝ) ≤ ((Wq G : ℚ) : ℝ) / (Om : ℝ) := by
    apply div_nonneg
    · exact_mod_cast hW.le
    · exact Nat.cast_nonneg _
  have hterm : ∀ i j, Ar G i j * (1 - X i j) ≤
      ((Wq G : ℚ) : ℝ) / (Om : ℝ) * ((Nz Om G i j : ℝ) * (1 - X i j)) +
        ((Wq G : ℚ) : ℝ) / (Om : ℝ) * 2 := by
    intro i j
    have hx := abs_le.mp (psd_unitDiag_abs_le_one hpsd h1 i j)
    have hs := Ar_le_scaled Om G hW hOm i j
    have h0 : 0 ≤ 1 - X i j := by linarith [hx.2]
    have h2 : 1 - X i j ≤ 2 := by linarith [hx.1]
    calc Ar G i j * (1 - X i j)
        ≤ (((Wq G : ℚ) : ℝ) / (Om : ℝ) * ((Nz Om G i j : ℝ) + 1)) * (1 - X i j) :=
          mul_le_mul_of_nonneg_right hs h0
      _ = ((Wq G : ℚ) : ℝ) / (Om : ℝ) * ((Nz Om G i j : ℝ) * (1 - X i j)) +
          ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (1 - X i j) := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h2 hc
          linarith
  have key : ∑ i, ∑ j, Ar G i j * (1 - X i j) ≤
      ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (∑ i, ∑ j, (Nz Om G i j : ℝ) * (1 - X i j)) +
        ((Wq G : ℚ) : ℝ) / (Om : ℝ) * (2 * (G.n : ℝ) ^ 2) := by
    calc ∑ i, ∑ j, Ar G i j * (1 - X i j)
        ≤ ∑ i : Fin G.n, ∑ j : Fin G.n,
            (((Wq G : ℚ) : ℝ) / (Om : ℝ) * ((Nz Om G i j : ℝ) * (1 - X i j)) +
              ((Wq G : ℚ) : ℝ) / (Om : ℝ) * 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := lap_sum_affine _ (fun i j => (Nz Om G i j : ℝ) * (1 - X i j))
  linarith

/-- With zero total weight the objective vanishes. -/
theorem obj_zero (G : Input) (hW : Wq G = 0) (X : Matrix (Fin G.n) (Fin G.n) ℝ) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (Ar G) X = 0 := by
  have hs : ∑ i, ∑ j, Aq G i j = 0 := by rw [sum_Aq, hW, mul_zero]
  have hrow : ∀ i, ∑ j, Aq G i j = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Aq_nonneg G i j)).mp hs i (Finset.mem_univ i)
  have hA : ∀ i j, Aq G i j = 0 := fun i j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Aq_nonneg G i j)).mp (hrow i) j
      (Finset.mem_univ j)
  have hAr : ∀ i j, Ar G i j = 0 := fun i j => by rw [← Aq_cast, hA, Rat.cast_zero]
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  simp only [hAr, zero_mul, Finset.sum_const_zero, mul_zero]

theorem one_feasible (G : Input) :
    ModernConvex.Relaxations.IsUnitDiagPSD (1 : Matrix (Fin G.n) (Fin G.n) ℝ) := by
  exact ⟨Matrix.PosSemidef.one, fun i => Matrix.one_apply_eq i⟩

theorem obj_one_nonneg (G : Input) :
    0 ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (Ar G)
      (1 : Matrix (Fin G.n) (Fin G.n) ℝ) := by
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  apply mul_nonneg (by norm_num)
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  apply mul_nonneg (Ar_nonneg G i j)
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-- The objective is bounded above on the feasible set (by the total weight). -/
theorem obj_le_total (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (Ar G) X ≤ ((Wq G : ℚ) : ℝ) := by
  obtain ⟨hpsd, h1⟩ := hX
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  have key : ∑ i, ∑ j, Ar G i j * (1 - X i j) ≤ ∑ i, ∑ j, Ar G i j * 2 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hx := (abs_le.mp (psd_unitDiag_abs_le_one hpsd h1 i j)).1
    exact mul_le_mul_of_nonneg_left (by linarith) (Ar_nonneg G i j)
  have e : ∑ i, ∑ j, Ar G i j * 2 = 4 * ((Wq G : ℚ) : ℝ) := by
    simp only [← Finset.sum_mul]
    rw [sum_Ar]
    ring
  linarith

end QMCSub


