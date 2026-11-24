-- Prove2me | Definitions.Def_CSL_Circuit_Labels_Framework_RankMetric
-- name    : CSL_Circuit_Labels_Framework_RankMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:54.101698+00:00
-- url     : https://prove2.me/theorems/c038c178-58cb-4779-8135-c383f5c4c6f6
-- title:
--   Coded sorting library: Circuit / Labels / Framework / RankMetric
-- statement:
--   Module `CodedSorting.Circuit.Labels.Framework.RankMetric` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Matrix rank lengths and the routing budget
--
--   These results use Mathlib's actual matrix rank. They do not assume the paper's
--   existence of a labelled graph or its total-rank formula. The finite-dimensional
--   projection theorem states its compatibility hypotheses explicitly.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Labels.Framework.RankMetric

import Definitions.Def_CSL_Compat
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-!
# Matrix rank lengths and the routing budget

These results use Mathlib's actual matrix rank. They do not assume the paper's
existence of a labelled graph or its total-rank formula. The finite-dimensional
projection theorem states its compatibility hypotheses explicitly.
-/

namespace CSL.RankMetric

open scoped BigOperators Matrix
open Module

section IndicatorPairing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal 0/1 indicator vector of a finite subset. -/
def indicator (T : Finset n) : n → ℚ := fun i => if i ∈ T then 1 else 0

def allOnes : Matrix n n ℚ := fun _ _ => 1

/-- The matrix I - J/9 used in Section 4.2. -/
def gramMatrix : Matrix n n ℚ :=
  (1 : Matrix n n ℚ) - (1 / 9 : ℚ) • (allOnes : Matrix n n ℚ)

/-- The actual coordinate formula xᵀ C₀ y, not an abstract pairing oracle. -/
def pairing (x y : n → ℚ) : ℚ := dotProduct x (gramMatrix *ᵥ y)

theorem sum_indicator (T : Finset n) :
    ∑ i, indicator T i = (T.card : ℚ) := by
  simp [indicator]

theorem dot_indicator (S T : Finset n) :
    dotProduct (indicator S) (indicator T) = ((S ∩ T).card : ℚ) := by
  have h : (fun i => indicator S i * indicator T i) = indicator (S ∩ T) := by
    funext i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [indicator, hs, ht]
  unfold dotProduct
  rw [h, sum_indicator]

theorem pairing_expansion (x y : n → ℚ) :
    pairing x y = dotProduct x y - (1 / 9 : ℚ) * (∑ i, x i) * (∑ i, y i) := by
  have hj : (allOnes : Matrix n n ℚ) *ᵥ y = fun _ : n => ∑ i, y i := by
    funext i
    simp [allOnes, Matrix.mulVec, dotProduct]
  unfold pairing gramMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, hj]
  simp only [smul_eq_mul, dotProduct]
  rw [← Finset.sum_mul]
  ring

theorem gram_apply (x : n → ℚ) (i : n) :
    (gramMatrix *ᵥ x) i = x i - (1 / 9 : ℚ) * ∑ j, x j := by
  unfold gramMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp [allOnes, Matrix.mulVec, dotProduct]

/-- C₀ has trivial kernel whenever the ambient dimension is not nine. -/
theorem gram_kernel_trivial (hne : (Fintype.card n : ℚ) ≠ 9)
    (x : n → ℚ) (hx : gramMatrix *ᵥ x = 0) : x = 0 := by
  have hcoord (i : n) : x i = (1 / 9 : ℚ) * ∑ j, x j := by
    have h := congrFun hx i
    rw [gram_apply] at h
    simpa only [Pi.zero_apply, sub_eq_zero] using h
  have hsum : (∑ i, x i) = (Fintype.card n : ℚ) * ((1 / 9 : ℚ) * ∑ i, x i) := by
    calc
      (∑ i, x i) = ∑ _i : n, (1 / 9 : ℚ) * ∑ j, x j :=
        Finset.sum_congr rfl (fun i _ => hcoord i)
      _ = _ := by simp
  have hprod : ((Fintype.card n : ℚ) - 9) * (∑ i, x i) = 0 := by
    nlinarith [hsum]
  have hz : (∑ i, x i) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  funext i
  rw [hcoord i, hz]
  simp

theorem gram_full_rank (hne : (Fintype.card n : ℚ) ≠ 9) :
    (gramMatrix : Matrix n n ℚ).rank = Fintype.card n := by
  have hk : LinearMap.ker (gramMatrix : Matrix n n ℚ).mulVecLin = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact gram_kernel_trivial hne x hx
  have h := LinearMap.finrank_range_add_finrank_ker
    (gramMatrix : Matrix n n ℚ).mulVecLin
  rw [hk, finrank_bot, add_zero, finrank_pi] at h
  exact h

/-- The paper's dimension restriction implies the required full-rank condition. -/
theorem gram_full_rank_of_dimension_ge39 (h : 39 ≤ Fintype.card n) :
    (gramMatrix : Matrix n n ℚ).rank = Fintype.card n := by
  apply gram_full_rank
  have hn : Fintype.card n ≠ 9 := by omega
  exact_mod_cast hn

/-- The intersection-to-orthogonality identity in the paper. -/
theorem triple_indicator_pairing (S T : Finset n)
    (hS : S.card = 3) (hT : T.card = 3) :
    pairing (indicator S) (indicator T) = ((S ∩ T).card : ℚ) - 1 := by
  rw [pairing_expansion, dot_indicator, sum_indicator, sum_indicator, hS, hT]
  norm_num

theorem triple_self_pairing (T : Finset n) (hT : T.card = 3) :
    pairing (indicator T) (indicator T) = 2 := by
  rw [triple_indicator_pairing T T hT hT, Finset.inter_self, hT]
  norm_num

theorem intersect_one_orthogonal (S T : Finset n)
    (hS : S.card = 3) (hT : T.card = 3) (hST : (S ∩ T).card = 1) :
    pairing (indicator S) (indicator T) = 0 := by
  rw [triple_indicator_pairing S T hS hT, hST]
  norm_num

theorem pairing_smul_left (x y : n → ℚ) (a : ℚ) :
    pairing (a • x) y = a * pairing x y := by
  unfold pairing
  simpa only [smul_eq_mul] using smul_dotProduct a x (gramMatrix *ᵥ y)

theorem pairing_comm (x y : n → ℚ) : pairing x y = pairing y x := by
  rw [pairing_expansion, pairing_expansion, dotProduct_comm x y]
  ring

/-- Nondegeneracy of the actual matrix pairing, not only a determinant claim. -/
theorem gram_nondegenerate (hne : (Fintype.card n : ℚ) ≠ 9) :
    Matrix.Nondegenerate (gramMatrix : Matrix n n ℚ) := by
  have key : ∀ x : n → ℚ, (∀ y, x ⬝ᵥ gramMatrix *ᵥ y = 0) → x = 0 := by
    intro x hx
    apply gram_kernel_trivial hne x
    funext i
    have hi : pairing (Pi.single i 1) x = 0 := by
      rw [pairing_comm]
      exact hx (Pi.single i 1)
    simpa [pairing] using hi
  rw [Matrix.nondegenerate_def]
  refine ⟨key, fun y hy => key y (fun x => ?_)⟩
  have h := hy x
  change pairing y x = 0
  rw [pairing_comm]
  exact h

theorem pairing_smul_right (x y : n → ℚ) (a : ℚ) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_comm x (a • y), pairing_smul_left, pairing_comm y x]

def indicatorLine (T : Finset n) : Submodule ℚ (n → ℚ) :=
  Submodule.span ℚ {indicator T}

theorem triple_indicator_ne_zero (T : Finset n) (hT : T.card = 3) :
    indicator T ≠ 0 := by
  intro hz
  have h := sum_indicator T
  rw [hz, hT] at h
  norm_num at h

theorem indicator_line_finrank (T : Finset n) (hT : T.card = 3) :
    finrank ℚ (indicatorLine T) = 1 := by
  exact finrank_span_singleton (triple_indicator_ne_zero T hT)

/-- On each line generated by a triple indicator, orthogonality to the generator
forces the scalar to be zero. This is the claimed one-dimensional nondegeneracy. -/
theorem triple_line_nondegenerate (T : Finset n) (hT : T.card = 3)
    (a : ℚ) (ha : pairing (a • indicator T) (indicator T) = 0) : a = 0 := by
  rw [pairing_smul_left, triple_self_pairing T hT] at ha
  linarith

/-- The same nondegeneracy statement on the actual span submodule. -/
theorem indicator_line_nondegenerate (T : Finset n) (hT : T.card = 3)
    (x : n → ℚ) (hx : x ∈ indicatorLine T)
    (horth : ∀ y ∈ indicatorLine T, pairing x y = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have ha := triple_line_nondegenerate T hT a
    (horth (indicator T) (Submodule.mem_span_singleton_self _))
  simp [ha]

/-- The side-wire incidence condition makes the entire two lines orthogonal. -/
theorem indicator_lines_orthogonal (S T : Finset n)
    (hS : S.card = 3) (hT : T.card = 3) (hST : (S ∩ T).card = 1)
    (x y : n → ℚ) (hx : x ∈ indicatorLine S) (hy : y ∈ indicatorLine T) :
    pairing x y = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [pairing_smul_left, pairing_smul_right, intersect_one_orthogonal S T hS hT hST]
  simp

end IndicatorPairing

section MatrixLengths

variable {n : Type*} [Fintype n]

/-- Subadditivity for the rank of rational square matrices. -/
theorem matrix_rank_add_le (A B : Matrix n n ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  apply le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))
  rintro x ⟨v, rfl⟩
  exact Submodule.mem_sup.mpr
    ⟨A.mulVecLin v, ⟨v, rfl⟩, B.mulVecLin v, ⟨v, rfl⟩, rfl⟩

/-- Reversing an undirected edge does not change its rank length. -/
theorem matrix_rank_neg (A : Matrix n n ℚ) : (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.neg_mulVec x A
  unfold Matrix.rank
  rw [h, LinearMap.range_neg]

theorem matrix_rank_sub_symm (A B : Matrix n n ℚ) :
    (A - B).rank = (B - A).rank := by
  rw [← matrix_rank_neg (B - A), neg_sub]

/-- Any sequence of labels satisfies the rank-metric triangle inequality.
No graph simplicity, orientation, or absence of repeated vertices is needed. -/
theorem matrix_path_bound (A : ℕ → Matrix n n ℚ) (k : ℕ) :
    (A k - A 0).rank ≤ ∑ i ∈ Finset.range k, (A (i + 1) - A i).rank := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : A (k + 1) - A 0 = (A (k + 1) - A k) + (A k - A 0) := by
        abel
      rw [heq, Finset.sum_range_succ]
      have h := matrix_rank_add_le (A (k + 1) - A k) (A k - A 0)
      omega

/-- The endpoint condition in Section 4 implies path length at least m. -/
theorem endpoint_identity_path_bound [DecidableEq n] (A : ℕ → Matrix n n ℚ) (k : ℕ)
    (hend : A k - A 0 = 1) :
    Fintype.card n ≤ ∑ i ∈ Finset.range k, (A (i + 1) - A i).rank := by
  have h := matrix_path_bound A k
  simpa only [hend, Matrix.rank_one] using h

/-- Scaling over Q by a nonzero scalar preserves the actual matrix rank. -/
theorem matrix_rank_smul (A : Matrix n n ℚ) (c : ℚ) (hc : c ≠ 0) :
    (c • A).rank = A.rank := by
  have h : (c • A).mulVecLin = c • A.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.smul_mulVec c A x
  unfold Matrix.rank
  rw [h, LinearMap.range_smul _ c hc]

/-- The negative source label contributes rank P, not rank zero.
In particular, a rank-one P gives an edge of length one. -/
theorem negative_source_edge_rank (P : Matrix n n ℚ) :
    (P - (-P)).rank = P.rank := by
  have h : P - (-P) = (2 : ℚ) • P := by
    ext i j
    simp
    ring
  rw [h]
  exact matrix_rank_smul P 2 (by norm_num)

omit [Fintype n] in
/-- The crossed X-source/Y-sink endpoint labels differ by the identity. -/
theorem crossed_endpoint_difference [DecidableEq n] (P : Matrix n n ℚ) :
    (1 - P) - (-P) = 1 := by abel

end MatrixLengths

section CompatibleProjections

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
/-- Compatible nested projections split the larger image into two disjoint images.
For orthogonal projections onto nondegenerate U ⊆ V, the paper must establish
the four displayed composition identities; they are not automatic for arbitrary
projections onto nested subspaces. -/
theorem compatible_projection_ranges
    (p q : V →ₗ[ℚ] V)
    (hpp : p.comp p = p) (hqq : q.comp q = q)
    (hpq : p.comp q = p) (hqp : q.comp p = p) :
    LinearMap.range p ⊔ LinearMap.range (q - p) = LinearMap.range q ∧
      Disjoint (LinearMap.range p) (LinearMap.range (q - p)) := by
  have pp (x : V) : p (p x) = p x := LinearMap.congr_fun hpp x
  have qq (x : V) : q (q x) = q x := LinearMap.congr_fun hqq x
  have pq (x : V) : p (q x) = p x := LinearMap.congr_fun hpq x
  have qp (x : V) : q (p x) = p x := LinearMap.congr_fun hqp x
  constructor
  · apply le_antisymm
    · apply sup_le
      · rintro x ⟨y, rfl⟩
        exact ⟨p y, qp y⟩
      · rintro x ⟨y, rfl⟩
        refine ⟨(q - p) y, ?_⟩
        simp only [LinearMap.sub_apply, map_sub, qq, qp]
    · rintro x ⟨y, rfl⟩
      apply Submodule.mem_sup.mpr
      refine ⟨p y, ⟨y, rfl⟩, (q - p) y, ⟨y, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply]
      abel
  · rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hpx : p x = x := by rw [← ha, pp]
    have hpzero : p x = 0 := by
      rw [← hb]
      simp only [LinearMap.sub_apply, map_sub, pq, pp, sub_self]
    exact hpx.symm.trans hpzero

/-- Dimension form of rank(P_V - P_U) = dim(V) - dim(U), for compatible
projections. The actual subspaces and their nondegeneracy are not assumed proved. -/
theorem compatible_projection_rank_difference
    (p q : V →ₗ[ℚ] V)
    (hpp : p.comp p = p) (hqq : q.comp q = q)
    (hpq : p.comp q = p) (hqp : q.comp p = p) :
    finrank ℚ (LinearMap.range (q - p)) =
      finrank ℚ (LinearMap.range q) - finrank ℚ (LinearMap.range p) := by
  obtain ⟨hsup, hdis⟩ := compatible_projection_ranges p q hpp hqq hpq hqp
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range p) (LinearMap.range (q - p))
  rw [hsup, hdis.eq_bot, finrank_bot, add_zero] at h
  omega

end CompatibleProjections

section MatrixProjectionRank

variable {n : Type*} [Fintype n]

/-- Matrix form of the compatible-projection theorem, using actual Matrix.rank. -/
theorem matrix_compatible_projection_rank_difference (P Q : Matrix n n ℚ)
    (hpp : P * P = P) (hqq : Q * Q = Q)
    (hpq : P * Q = P) (hqp : Q * P = P) :
    (Q - P).rank = Q.rank - P.rank := by
  have hsub : (Q - P).mulVecLin = Q.mulVecLin - P.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.sub_mulVec Q P x
  have hpp' : P.mulVecLin.comp P.mulVecLin = P.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hpp]
  have hqq' : Q.mulVecLin.comp Q.mulVecLin = Q.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hqq]
  have hpq' : P.mulVecLin.comp Q.mulVecLin = P.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hpq]
  have hqp' : Q.mulVecLin.comp P.mulVecLin = P.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hqp]
  unfold Matrix.rank
  rw [hsub]
  exact compatible_projection_rank_difference P.mulVecLin Q.mulVecLin
    hpp' hqq' hpq' hqp'

end MatrixProjectionRank

section Routing

variable {Path Edge : Type*} [Fintype Path] [Fintype Edge]

/-- Summing the per-session rate constraints supplies the total-flow hypothesis
used below. Every enumerated path has exactly one owning session. -/
theorem session_total_flow {Session : Type*} [Fintype Session] [DecidableEq Session]
    (owner : Path → Session) (flow : Path → ℝ) (r : ℝ)
    (hrate : ∀ i, r ≤ ∑ p, if owner p = i then flow p else 0) :
    (Fintype.card Session : ℝ) * r ≤ ∑ p, flow p := by
  calc
    (Fintype.card Session : ℝ) * r = ∑ _i : Session, r := by simp
    _ ≤ ∑ i : Session, ∑ p, if owner p = i then flow p else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hrate i
    _ = ∑ p, flow p := by
      rw [Finset.sum_comm]
      simp

/-- Weighted capacity accounting for any finite collection of paths.
`uses p e` counts edge traversals, allowing repeated traversals rather than
silently treating walks as simple paths. -/
theorem weighted_routing_budget
    (flow : Path → ℝ) (length capacity : Edge → ℝ)
    (uses : Path → Edge → ℕ) (m : ℝ)
    (hflow : ∀ p, 0 ≤ flow p) (hlength : ∀ e, 0 ≤ length e)
    (hpath : ∀ p, m ≤ ∑ e, length e * (uses p e : ℝ))
    (hcapacity : ∀ e, ∑ p, flow p * (uses p e : ℝ) ≤ capacity e) :
    m * ∑ p, flow p ≤ ∑ e, length e * capacity e := by
  calc
    m * ∑ p, flow p = ∑ p, flow p * m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p, flow p * ∑ e, length e * (uses p e : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hpath p) (hflow p)
    _ = ∑ e, length e * ∑ p, flow p * (uses p e : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ e, length e * capacity e := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left (hcapacity e) (hlength e)

/-- Once W sessions supply at least W*r total path flow, the weighted budget
implies the common-rate bound. The total-flow hypothesis is explicit. -/
theorem common_rate_bound
    (flow : Path → ℝ) (length capacity : Edge → ℝ)
    (uses : Path → Edge → ℕ) (m W r : ℝ)
    (hm : 0 < m) (hW : 0 < W)
    (hflow : ∀ p, 0 ≤ flow p) (hlength : ∀ e, 0 ≤ length e)
    (hpath : ∀ p, m ≤ ∑ e, length e * (uses p e : ℝ))
    (hcapacity : ∀ e, ∑ p, flow p * (uses p e : ℝ) ≤ capacity e)
    (hrate : W * r ≤ ∑ p, flow p) :
    r ≤ (∑ e, length e * capacity e) / (W * m) := by
  have hb := weighted_routing_budget flow length capacity uses m
    hflow hlength hpath hcapacity
  have ht := mul_le_mul_of_nonneg_left hrate (le_of_lt hm)
  apply (le_div_iff₀ (mul_pos hW hm)).mpr
  nlinarith

/-- In unit-capacity networks, total weighted capacity is just total edge length. -/
theorem unit_capacity_budget (length : Edge → ℝ) :
    (∑ e, length e * (1 : ℝ)) = ∑ e, length e := by simp

end Routing

end CSL.RankMetric


