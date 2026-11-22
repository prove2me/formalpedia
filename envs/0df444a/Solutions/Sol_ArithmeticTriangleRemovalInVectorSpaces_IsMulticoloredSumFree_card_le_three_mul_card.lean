-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_three_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:51.962274+00:00
-- url     : https://prove2.me/submissions/a9f7bd44-efa8-4f31-93a3-f1f8f7f3c273

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_le_card_add_card_add_card

section
public section
open Finset MvPolynomial
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime]
private lemma exists_ite_add_add_eq_zero_eq_sum :
    ∃ S : Finset (Fin 3 →₀ ℕ), ∃ κ : (Fin 3 →₀ ℕ) → ZMod p, (∀ e ∈ S, e 0 + e 1 + e 2 ≤ p - 1) ∧
      ∀ u v w : ZMod p,
        (if u + v + w = 0 then 1 else 0) = ∑ e ∈ S, κ e * (u ^ e 0 * v ^ e 1 * w ^ e 2) := by
  let P : MvPolynomial (Fin 3) (ZMod p) := 1 - (X 0 + X 1 + X 2) ^ (p - 1)
  refine ⟨P.support, fun e ↦ P.coeff e, ?_, ?_⟩
  · intro e he
    have hdeg := le_totalDegree he
    have hP : P.totalDegree ≤ p - 1 := by
      grw [totalDegree_sub, totalDegree_one, totalDegree_pow, totalDegree_add, totalDegree_add,
        totalDegree_X, totalDegree_X, totalDegree_X]
      simp
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_three] at hdeg
    grind
  · intro u v w
    have hP := eval_eq' ![u, v, w] P
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hP
    rw [← hP]
    simp only [P, map_sub, map_one, map_pow, map_add, eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases h : u + v + w = 0
    · simp [h, zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)]
    · simp [h, ZMod.pow_card_sub_one_eq_one h]
private lemma ite_eq_sum_prod {S : Finset (Fin 3 →₀ ℕ)} {κ : (Fin 3 →₀ ℕ) → ZMod p}
    (hf : ∀ u v w : ZMod p,
      (if u + v + w = 0 then 1 else 0) = ∑ e ∈ S, κ e * (u ^ e 0 * v ^ e 1 * w ^ e 2))
    {d : ℕ} (x y z : Fin d → ZMod p) :
    (if x + y + z = 0 then 1 else 0) = ∑ σ ∈ Fintype.piFinset fun _ ↦ S,
      ∏ t, κ (σ t) * (x t ^ σ t 0 * y t ^ σ t 1 * z t ^ σ t 2) := by
  rw [← prod_univ_sum (fun _ ↦ S) fun t e ↦ κ e * (x t ^ e 0 * y t ^ e 1 * z t ^ e 2)]
  simp_rw [← hf]
  rw [prod_boole]
  simp [funext_iff]
omit [Fact p.Prime] in
/-- If every `σ t` is the exponent vector of a monomial of degree at most `p - 1`, then the
degrees of the monomial `∏ t, x t ^ σ t 0 * y t ^ σ t 1 * z t ^ σ t 2` in `x`, `y` and `z` add up
to at most `(p - 1) * d`. -/
private lemma sum_add_sum_add_sum_le {S : Finset (Fin 3 →₀ ℕ)}
    (hS : ∀ e ∈ S, e 0 + e 1 + e 2 ≤ p - 1)
    {d : ℕ} {σ : Fin d → Fin 3 →₀ ℕ} (hσ : σ ∈ Fintype.piFinset fun _ ↦ S) :
    ∑ t, σ t 0 + ∑ t, σ t 1 + ∑ t, σ t 2 ≤ (p - 1) * d := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  trans ∑ _t : Fin d, (p - 1)
  · apply sum_le_sum
    intro t _
    exact hS _ (Fintype.mem_piFinset.1 hσ t)
  · simp [mul_comm]
private lemma mem_lowDegreeExponents_of_three_mul_sum_le {S : Finset (Fin 3 →₀ ℕ)}
    (hS : ∀ e ∈ S, e 0 + e 1 + e 2 ≤ p - 1) {d : ℕ} {σ : Fin d → Fin 3 →₀ ℕ}
    (hσ : σ ∈ Fintype.piFinset fun _ ↦ S) {s : Fin 3} (hs : 3 * ∑ t, σ t s ≤ (p - 1) * d) :
    (fun t ↦ σ t s) ∈ lowDegreeExponents p d := by
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 ?_, hs⟩
  intro t
  have := hS _ (Fintype.mem_piFinset.1 hσ t)
  fin_cases s <;> grind [(Fact.out : p.Prime).one_lt]
omit [Fact p.Prime] in
/-- Grouping a sum according to a map into a finite set. -/
private lemma sum_mul_eq_sum_mul_sum {κ α R : Type*} [CommSemiring R] [DecidableEq α] {s : Finset κ}
    {A : Finset α} (a : κ → α) (ha : ∀ σ ∈ s, a σ ∈ A) (u : α → R) (v : κ → R) :
    ∑ σ ∈ s, u (a σ) * v σ = ∑ α ∈ A, u α * ∑ σ ∈ s with a σ = α, v σ := by
  rw [← sum_fiberwise_of_maps_to ha]
  congr with α
  rw [mul_sum, sum_filter, sum_filter]
  congr with σ
  grind
variable (p) in
/-- The indicator function of `x + y + z = 0` on `(Fin d → ZMod p) ^ 3` is a sum of
`3 * #(lowDegreeExponents p d)` slices: products of a monomial `x ^ α`, `y ^ β` or `z ^ γ` of low
degree and a function of the other two variables. -/
private lemma exists_ite_eq_sum_slices (d : ℕ) :
    ∃ F G H : (Fin d → ℕ) → (Fin d → ZMod p) → (Fin d → ZMod p) → ZMod p,
      ∀ x y z : Fin d → ZMod p, (if x + y + z = 0 then 1 else 0) =
        ∑ α ∈ lowDegreeExponents p d, (∏ t, x t ^ α t) * F α y z +
        ∑ β ∈ lowDegreeExponents p d, (∏ t, y t ^ β t) * G β x z +
        ∑ γ ∈ lowDegreeExponents p d, (∏ t, z t ^ γ t) * H γ x y := by
  classical
  obtain ⟨S, κ, hS, hf⟩ := exists_ite_add_add_eq_zero_eq_sum (p := p)
  let P := Fintype.piFinset fun _ : Fin d ↦ S
  let a (σ : Fin d → Fin 3 →₀ ℕ) (s : Fin 3) : Fin d → ℕ := fun t ↦ σ t s
  let low (σ : Fin d → Fin 3 →₀ ℕ) (s : Fin 3) : Prop := 3 * ∑ t, a σ s t ≤ (p - 1) * d
  refine ⟨fun α y z ↦ ∑ σ ∈ (P.filter (low · 0)).filter (a · 0 = α),
      ∏ t, κ (σ t) * (y t ^ σ t 1 * z t ^ σ t 2),
    fun β x z ↦ ∑ σ ∈ ((P.filter (¬low · 0)).filter (low · 1)).filter (a · 1 = β),
      ∏ t, κ (σ t) * (x t ^ σ t 0 * z t ^ σ t 2),
    fun γ x y ↦ ∑ σ ∈ ((P.filter (¬low · 0)).filter (¬low · 1)).filter (a · 2 = γ),
      ∏ t, κ (σ t) * (x t ^ σ t 0 * y t ^ σ t 1), ?_⟩
  intro x y z
  rw [ite_eq_sum_prod hf, ← sum_filter_add_sum_filter_not P (low · 0),
    ← sum_filter_add_sum_filter_not (P.filter (¬low · 0)) (low · 1), add_assoc,
    ← sum_mul_eq_sum_mul_sum (s := P.filter (low · 0)) (a · 0) ?_,
    ← sum_mul_eq_sum_mul_sum (s := (P.filter (¬low · 0)).filter (low · 1)) (a · 1) ?_,
    ← sum_mul_eq_sum_mul_sum (s := (P.filter (¬low · 0)).filter (¬low · 1)) (a · 2) ?_]
  · simp [a, ← prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm]
  · intro σ hσ
    simp only [mem_filter, low, a] at hσ
    obtain ⟨⟨hσP, hσ₀⟩, hσ₁⟩ := hσ
    exact mem_lowDegreeExponents_of_three_mul_sum_le hS hσP
      (by grind [sum_add_sum_add_sum_le hS hσP])
  · intro σ hσ
    simp only [mem_filter] at hσ
    obtain ⟨⟨hσP, -⟩, hσ₁⟩ := hσ
    exact mem_lowDegreeExponents_of_three_mul_sum_le hS hσP hσ₁
  · intro σ hσ
    obtain ⟨hσP, hσ₀⟩ := mem_filter.1 hσ
    exact mem_lowDegreeExponents_of_three_mul_sum_le hS hσP hσ₀
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime]
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution {ι : Type*} [Fintype ι] {d : ℕ}
    {x y z : ι → Fin d → ZMod p} (h : IsMulticoloredSumFree x y z) :
    Fintype.card ι ≤ 3 * #(lowDegreeExponents p d) := by
  classical
  obtain ⟨F, G, H, hT⟩ := exists_ite_eq_sum_slices p d
  grw [card_le_card_add_card_add_card (A := lowDegreeExponents p d) (B := lowDegreeExponents p d)
    (C := lowDegreeExponents p d) (fun α i ↦ ∏ t, x i t ^ α t) (fun α j k ↦ F α (y j) (z k))
    (fun β j ↦ ∏ t, y j t ^ β t) (fun β i k ↦ G β (x i) (z k)) (fun γ k ↦ ∏ t, z k t ^ γ t)
    (fun γ i j ↦ H γ (x i) (y j)) ?_]
  · grind
  · intro i j k
    rw [← hT]
    simp [h i j k]
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
