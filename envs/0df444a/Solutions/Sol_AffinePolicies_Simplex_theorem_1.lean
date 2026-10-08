-- Prove2me | solution 1 for AffinePolicies.Simplex.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:56:39.496843+00:00
-- url     : https://prove2.me/submissions/b87863a4-220f-4ade-b698-cef07d266590

/-
Bertsimas–Goyal, Theorem 1: for the simplex uncertainty set an affine second-stage policy is
optimal in the two-stage adaptive problem.

Proof. The adaptive problem on `conv(b¹,…,b^{m+1})` is equivalent to the linear program in the
vertex data `(x, Y₁,…,Y_{m+1}, τ)`: `x, Yⱼ ≥ 0`, `A x + B Yⱼ ≥ bʲ`, `c·x + d·Yⱼ ≤ τ`. This LP is
feasible (take an adaptive solution at the vertices) and bounded below by `0`, so an optimum exists
(`Polyhedral.lp_min_attained_basic`). The affine interpolant of the optimal vertex values
(`interpolant_eq_sum`: `ỹ(Σ αⱼ bʲ) = Σ αⱼ Yⱼ`) is feasible on the whole simplex and has the same
worst-case cost bound, and every adaptive solution gives a feasible LP point, so the interpolated
solution is optimal. The interpolant is `b ↦ P b + q` with `P = Y Q⁻¹`.

Imports of platform theorems (both Proved): `Polyhedral.lp_min_attained_basic`,
`AffinePolicies.Simplex.interpolant_eq_sum`.
-/
import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting
import Theorems.Thm_Polyhedral_lp_min_attained_basic
import Theorems.Thm_AffinePolicies_Simplex_interpolant_eq_sum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AffProof

open Matrix

/-- Attainment of a bounded linear program in equality form, for arbitrary finite index types. -/
theorem lp_eq_general {κ ι : Type} [Fintype κ] [Fintype ι] (W : ι → κ → ℝ) (q : κ → ℝ)
    (d : ι → ℝ)
    (hfeas : ∃ y : κ → ℝ, (∀ k, 0 ≤ y k) ∧ ∀ r, ∑ k, W r k * y k = d r)
    (hbdd : ∃ β : ℝ, ∀ y : κ → ℝ, (∀ k, 0 ≤ y k) → (∀ r, ∑ k, W r k * y k = d r) →
      β ≤ ∑ k, q k * y k) :
    ∃ y0 : κ → ℝ, (∀ k, 0 ≤ y0 k) ∧ (∀ r, ∑ k, W r k * y0 k = d r) ∧
      ∀ y : κ → ℝ, (∀ k, 0 ≤ y k) → (∀ r, ∑ k, W r k * y k = d r) →
        ∑ k, q k * y0 k ≤ ∑ k, q k * y k := by
  classical
  let eκ := Fintype.equivFin κ
  let eι := Fintype.equivFin ι
  let W' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card κ)) ℝ :=
    Matrix.of fun a b => W (eι.symm a) (eκ.symm b)
  let q' : Fin (Fintype.card κ) → ℝ := fun b => q (eκ.symm b)
  let d' : Fin (Fintype.card ι) → ℝ := fun a => d (eι.symm a)
  have hmul : ∀ (y' : Fin (Fintype.card κ) → ℝ) (a : Fin (Fintype.card ι)),
      (W'.mulVec y') a = ∑ k, W (eι.symm a) k * y' (eκ k) := by
    intro y' a
    simp only [Matrix.mulVec, dotProduct, W', Matrix.of_apply]
    exact (Equiv.sum_comp eκ (fun b => W (eι.symm a) (eκ.symm b) * y' b)).symm ▸ by simp
  have hdot : ∀ (y' : Fin (Fintype.card κ) → ℝ), q' ⬝ᵥ y' = ∑ k, q k * y' (eκ k) := by
    intro y'
    simp only [dotProduct, q']
    exact (Equiv.sum_comp eκ (fun b => q (eκ.symm b) * y' b)).symm ▸ by simp
  have hfeas' : ∃ y' : Fin (Fintype.card κ) → ℝ, (∀ j, 0 ≤ y' j) ∧ W'.mulVec y' = d' := by
    obtain ⟨y, hy0, hy⟩ := hfeas
    refine ⟨fun b => y (eκ.symm b), fun b => hy0 _, ?_⟩
    funext a
    rw [hmul]
    simpa [d'] using hy (eι.symm a)
  have hbdd' : ∃ β : ℝ, ∀ y' : Fin (Fintype.card κ) → ℝ, (∀ j, 0 ≤ y' j) → W'.mulVec y' = d' →
      β ≤ q' ⬝ᵥ y' := by
    obtain ⟨β, hβ⟩ := hbdd
    refine ⟨β, fun y' hy0 hy => ?_⟩
    rw [hdot]
    refine hβ (fun k => y' (eκ k)) (fun k => hy0 _) (fun r => ?_)
    have := congrFun hy (eι r)
    rw [hmul] at this
    simpa [d'] using this
  obtain ⟨y0', hy0', hy0, hopt, -⟩ := Polyhedral.lp_min_attained_basic W' q' d' hfeas' hbdd'
  refine ⟨fun k => y0' (eκ k), fun k => hy0' _, fun r => ?_, fun y hy0'' hy => ?_⟩
  · have := congrFun hy0 (eι r)
    rw [hmul] at this
    simpa [d'] using this
  · have h := hopt (fun b => y (eκ.symm b)) (fun b => hy0'' _) (by
      funext a
      rw [hmul]
      simpa [d'] using hy (eι.symm a))
    rw [hdot, hdot] at h
    simpa using h

/-- Attainment of a bounded linear program in inequality form `d ≤ R z`, `z ≥ 0`. -/
theorem lp_ineq {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] (R : ι → κ → ℝ)
    (d : ι → ℝ) (q : κ → ℝ)
    (hfeas : ∃ z : κ → ℝ, (∀ k, 0 ≤ z k) ∧ ∀ r, d r ≤ ∑ k, R r k * z k)
    (hbdd : ∃ β : ℝ, ∀ z : κ → ℝ, (∀ k, 0 ≤ z k) → (∀ r, d r ≤ ∑ k, R r k * z k) →
      β ≤ ∑ k, q k * z k) :
    ∃ z0 : κ → ℝ, (∀ k, 0 ≤ z0 k) ∧ (∀ r, d r ≤ ∑ k, R r k * z0 k) ∧
      ∀ z : κ → ℝ, (∀ k, 0 ≤ z k) → (∀ r, d r ≤ ∑ k, R r k * z k) →
        ∑ k, q k * z0 k ≤ ∑ k, q k * z k := by
  classical
  let Wf : ι → κ ⊕ ι → ℝ := fun r k' => Sum.elim (R r) (fun r' => if r = r' then -1 else 0) k'
  let qf : κ ⊕ ι → ℝ := Sum.elim q (fun _ => 0)
  have hrow : ∀ (y : κ ⊕ ι → ℝ) (r : ι),
      ∑ k', Wf r k' * y k' = (∑ k, R r k * y (Sum.inl k)) - y (Sum.inr r) := by
    intro y r
    simp only [Wf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ite_mul, neg_mul, one_mul,
      zero_mul]
    rw [Finset.sum_ite_eq]
    simp [sub_eq_add_neg]
  have hobj : ∀ y : κ ⊕ ι → ℝ, ∑ k', qf k' * y k' = ∑ k, q k * y (Sum.inl k) := by
    intro y
    simp [qf, Fintype.sum_sum_type]
  obtain ⟨y0, hy0, hy0eq, hopt⟩ := lp_eq_general Wf qf d
    (by
      obtain ⟨z, hz0, hz⟩ := hfeas
      refine ⟨Sum.elim z (fun r => (∑ k, R r k * z k) - d r), ?_, ?_⟩
      · rintro (k | r)
        · exact hz0 k
        · simpa using hz r
      · intro r
        rw [hrow]
        simp)
    (by
      obtain ⟨β, hβ⟩ := hbdd
      refine ⟨β, fun y hy0 hy => ?_⟩
      rw [hobj]
      refine hβ (fun k => y (Sum.inl k)) (fun k => hy0 _) (fun r => ?_)
      have := hy r
      rw [hrow] at this
      have := hy0 (Sum.inr r)
      linarith [hy r, hrow y r])
  refine ⟨fun k => y0 (Sum.inl k), fun k => hy0 _, fun r => ?_, fun z hz0 hz => ?_⟩
  · have h1 := hy0eq r
    rw [hrow] at h1
    have := hy0 (Sum.inr r)
    linarith
  · have h := hopt (Sum.elim z (fun r => (∑ k, R r k * z k) - d r)) (by
        rintro (k | r)
        · exact hz0 k
        · simpa using hz r) (by
        intro r
        rw [hrow]
        simp)
    rw [hobj, hobj] at h
    simpa using h


section Main

open AffinePolicies.Simplex

variable {m n₁ n₂ : ℕ}

/-- Variables of the vertex LP: `x`, the second-stage vectors `Y_j`, and the bound `τ`. -/
abbrev KT (m n₁ n₂ : ℕ) := Fin n₁ ⊕ (Fin (m + 1) × Fin n₂) ⊕ Unit

/-- Constraints of the vertex LP: feasibility at each vertex and `τ ≥ cost at each vertex`. -/
abbrev IT (m : ℕ) := (Fin (m + 1) × Fin m) ⊕ Fin (m + 1)

def Rco (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ)
    (d : Fin n₂ → ℝ) : IT m → KT m n₁ n₂ → ℝ
  | Sum.inl (_, i), Sum.inl a => A i a
  | Sum.inl (j, i), Sum.inr (Sum.inl (j', l)) => if j' = j then B i l else 0
  | Sum.inl _, Sum.inr (Sum.inr _) => 0
  | Sum.inr _, Sum.inl a => - c a
  | Sum.inr j, Sum.inr (Sum.inl (j', l)) => if j' = j then - d l else 0
  | Sum.inr _, Sum.inr (Sum.inr _) => 1

def rhs (v : Fin (m + 1) → Fin m → ℝ) : IT m → ℝ
  | Sum.inl (j, i) => v j i
  | Sum.inr _ => 0

def qco : KT m n₁ n₂ → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => 1

theorem rowA (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ)
    (d : Fin n₂ → ℝ) (z : KT m n₁ n₂ → ℝ) (j : Fin (m + 1)) (i : Fin m) :
    ∑ k, Rco A B c d (Sum.inl (j, i)) k * z k =
      (A *ᵥ (fun a => z (Sum.inl a))) i + (B *ᵥ (fun l => z (Sum.inr (Sum.inl (j, l))))) i := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Rco, Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_const, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

theorem rowC (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ)
    (d : Fin n₂ → ℝ) (z : KT m n₁ n₂ → ℝ) (j : Fin (m + 1)) :
    ∑ k, Rco A B c d (Sum.inr j) k * z k =
      z (Sum.inr (Sum.inr ())) - (c ⬝ᵥ (fun a => z (Sum.inl a)) +
        d ⬝ᵥ (fun l => z (Sum.inr (Sum.inl (j, l))))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Rco, dotProduct, Finset.univ_unique, Finset.sum_const]
  have h1 : ∑ x : Fin (m + 1), ∑ y : Fin n₂, (if x = j then -d y else 0) * z (Sum.inr (Sum.inl (x, y)))
      = -∑ l, d l * z (Sum.inr (Sum.inl (j, l))) := by
    rw [Finset.sum_eq_single j]
    · simp [Finset.sum_neg_distrib]
    · intro j' _ hj'
      simp [hj']
    · simp
  rw [h1]
  simp [Finset.sum_neg_distrib, neg_mul]
  ring

theorem objsum (z : KT m n₁ n₂ → ℝ) : ∑ k, (qco : KT m n₁ n₂ → ℝ) k * z k = z (Sum.inr (Sum.inr ())) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [qco]

/-- Weighted-sum description of the simplex. -/
theorem hullrep {v : Fin (m + 1) → Fin m → ℝ} {b : Fin m → ℝ}
    (hb : b ∈ convexHull ℝ (Set.range v)) :
    ∃ α : Fin (m + 1) → ℝ, (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1 ∧ ∑ j, α j • v j = b := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hb
  obtain ⟨s, w, hw0, hw1, hbs⟩ := hb
  refine ⟨fun j => if j ∈ s then w j else 0, fun j => ?_, ?_, ?_⟩
  · by_cases h : j ∈ s
    · simpa [h] using hw0 j h
    · simp [h]
  · simpa [Finset.sum_ite_mem] using hw1
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hbs
    rw [← hbs]
    simp [ite_smul, Finset.sum_ite_mem]

end Main


section Final

open AffinePolicies.Simplex

variable {m n₁ n₂ : ℕ}

def packz (x : Fin n₁ → ℝ) (Y : Fin (m + 1) → Fin n₂ → ℝ) (τ : ℝ) : KT m n₁ n₂ → ℝ :=
  Sum.elim x (Sum.elim (fun p => Y p.1 p.2) (fun _ => τ))

/-- A vertex solution `(x, Y, τ)` gives a feasible point of the vertex LP. -/
theorem pack_feasible (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (v : Fin (m + 1) → Fin m → ℝ)
    (x : Fin n₁ → ℝ) (hx : 0 ≤ x) (Y : Fin (m + 1) → Fin n₂ → ℝ) (hY : ∀ j, 0 ≤ Y j)
    (hrow : ∀ j, v j ≤ A *ᵥ x + B *ᵥ Y j) (τ : ℝ) (hτ : 0 ≤ τ)
    (hcost : ∀ j, c ⬝ᵥ x + d ⬝ᵥ Y j ≤ τ) :
    (∀ k, 0 ≤ packz x Y τ k) ∧ ∀ r, rhs v r ≤ ∑ k, Rco A B c d r k * packz x Y τ k := by
  refine ⟨?_, ?_⟩
  · rintro (a | ⟨j, l⟩ | ⟨⟩)
    · exact hx a
    · exact hY j l
    · exact hτ
  · rintro (⟨j, i⟩ | j)
    · rw [rowA]
      have := hrow j i
      simpa [rhs, packz] using this
    · rw [rowC]
      have := hcost j
      simp only [rhs, packz, Sum.elim_inl, Sum.elim_inr]
      linarith

end Final

section Final2

open AffinePolicies.Simplex

variable {m n₁ n₂ : ℕ}

theorem exists_optimal_adapt (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      Feasible A B (simplexSet v) x y) :
    ∃ (x : Fin n₁ → ℝ) (g : (Fin m → ℝ) → Fin n₂ → ℝ),
      IsOptimalAdapt A B c d (simplexSet v) x (interpolant v g) := by
  classical
  have hvU : ∀ j, v j ∈ simplexSet v := fun j => subset_convexHull ℝ _ (Set.mem_range_self j)
  -- the vertex LP has a feasible point
  obtain ⟨x₁, y₁, hf1⟩ := hfeas
  have hcostnn : ∀ (x : Fin n₁ → ℝ) (Y : Fin n₂ → ℝ), 0 ≤ x → 0 ≤ Y → 0 ≤ c ⬝ᵥ x + d ⬝ᵥ Y :=
    fun x Y hx hY => add_nonneg (dotProduct_nonneg_of_nonneg hc hx) (dotProduct_nonneg_of_nonneg hd hY)
  have hLPfeas : ∃ z : KT m n₁ n₂ → ℝ, (∀ k, 0 ≤ z k) ∧
      ∀ r, rhs v r ≤ ∑ k, Rco A B c d r k * z k := by
    refine ⟨packz x₁ (fun j => y₁ (v j))
      (∑ j, (c ⬝ᵥ x₁ + d ⬝ᵥ y₁ (v j))), ?_⟩
    refine pack_feasible A B c d v x₁ hf1.1 _ (fun j => (hf1.2 _ (hvU j)).1)
      (fun j => (hf1.2 _ (hvU j)).2) _ ?_ (fun j => ?_)
    · exact Finset.sum_nonneg (fun j _ => hcostnn _ _ hf1.1 (hf1.2 _ (hvU j)).1)
    · exact Finset.single_le_sum (f := fun j => c ⬝ᵥ x₁ + d ⬝ᵥ y₁ (v j))
        (fun j _ => hcostnn _ _ hf1.1 (hf1.2 _ (hvU j)).1) (Finset.mem_univ j)
  have hLPbdd : ∃ β : ℝ, ∀ z : KT m n₁ n₂ → ℝ, (∀ k, 0 ≤ z k) →
      (∀ r, rhs v r ≤ ∑ k, Rco A B c d r k * z k) → β ≤ ∑ k, (qco : KT m n₁ n₂ → ℝ) k * z k := by
    refine ⟨0, fun z hz0 _ => ?_⟩
    rw [objsum]
    exact hz0 _
  obtain ⟨z0, hz0, hz0r, hz0opt⟩ := lp_ineq (Rco A B c d) (rhs v) qco hLPfeas hLPbdd
  -- unpack the optimal vertex solution
  set xs : Fin n₁ → ℝ := fun a => z0 (Sum.inl a) with hxs
  set Ys : Fin (m + 1) → Fin n₂ → ℝ := fun j l => z0 (Sum.inr (Sum.inl (j, l))) with hYs
  set τs : ℝ := z0 (Sum.inr (Sum.inr ())) with hτs
  have hxs0 : 0 ≤ xs := fun a => hz0 _
  have hYs0 : ∀ j, 0 ≤ Ys j := fun j l => hz0 _
  have hrowA : ∀ j, v j ≤ A *ᵥ xs + B *ᵥ Ys j := by
    intro j i
    have := hz0r (Sum.inl (j, i))
    rw [rowA] at this
    simpa [rhs] using this
  have hrowC : ∀ j, c ⬝ᵥ xs + d ⬝ᵥ Ys j ≤ τs := by
    intro j
    have := hz0r (Sum.inr j)
    rw [rowC] at this
    simp only [rhs] at this
    linarith
  -- affine interpolation of the vertex solutions
  let g : (Fin m → ℝ) → Fin n₂ → ℝ := fun b =>
    if h : ∃ j, v j = b then Ys (Classical.choose h) else 0
  have hg : ∀ j, g (v j) = Ys j := by
    intro j
    have h : ∃ j', v j' = v j := ⟨j, rfl⟩
    simp only [g, dif_pos h]
    rw [hv.injective (Classical.choose_spec h)]
  have hinterp : ∀ b ∈ simplexSet v, ∃ α : Fin (m + 1) → ℝ, (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1 ∧
      interpolant v g b = ∑ j, α j • Ys j ∧ b = ∑ j, α j • v j := by
    intro b hb
    obtain ⟨α, hα0, hα1, hαb⟩ := hullrep hb
    refine ⟨α, hα0, hα1, ?_, hαb.symm⟩
    rw [← hαb, interpolant_eq_sum v hv g α hα1]
    simp [hg]
  have hcombA : ∀ (α : Fin (m + 1) → ℝ), (∀ j, 0 ≤ α j) → ∑ j, α j = 1 →
      (∑ j, α j • v j) ≤ A *ᵥ xs + B *ᵥ (∑ j, α j • Ys j) := by
    intro α hα0 hα1 i
    have h1 : (B *ᵥ (∑ j, α j • Ys j)) i = ∑ j, α j * (B *ᵥ Ys j) i := by
      rw [Matrix.mulVec_sum]
      simp [Matrix.mulVec_smul, Finset.sum_apply]
    have h2 : (A *ᵥ xs) i = ∑ j, α j * (A *ᵥ xs) i := by
      rw [← Finset.sum_mul, hα1, one_mul]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1]
    nth_rewrite 1 [h2]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hrowA j i) (hα0 j))
  have hcombC : ∀ (α : Fin (m + 1) → ℝ), (∀ j, 0 ≤ α j) → ∑ j, α j = 1 →
      c ⬝ᵥ xs + d ⬝ᵥ (∑ j, α j • Ys j) ≤ τs := by
    intro α hα0 hα1
    have h1 : d ⬝ᵥ (∑ j, α j • Ys j) = ∑ j, α j * (d ⬝ᵥ Ys j) := by
      simp [dotProduct, Finset.mul_sum, Finset.sum_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
    have h2 : c ⬝ᵥ xs = ∑ j, α j * (c ⬝ᵥ xs) := by
      rw [← Finset.sum_mul, hα1, one_mul]
    rw [h1]
    nth_rewrite 1 [h2]
    rw [← Finset.sum_add_distrib]
    calc ∑ j, (α j * (c ⬝ᵥ xs) + α j * (d ⬝ᵥ Ys j)) ≤ ∑ j, α j * τs := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hrowC j) (hα0 j)
      _ = τs := by rw [← Finset.sum_mul, hα1, one_mul]
  have hfeasS : Feasible A B (simplexSet v) xs (interpolant v g) := by
    refine ⟨hxs0, fun b hb => ?_⟩
    obtain ⟨α, hα0, hα1, hyb, hbα⟩ := hinterp b hb
    rw [hyb]
    refine ⟨fun l => ?_, ?_⟩
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hα0 j) (hYs0 j l))
    · rw [hbα]
      exact hcombA α hα0 hα1
  refine ⟨xs, g, hfeasS, fun x' y' t hf' hct => ?_⟩
  have ht0 : 0 ≤ t := by
    have h0 := hct (v 0) (hvU 0)
    exact le_trans (hcostnn _ _ hf'.1 (hf'.2 _ (hvU 0)).1) h0
  have hz' := pack_feasible A B c d v x' hf'.1 (fun j => y' (v j)) (fun j => (hf'.2 _ (hvU j)).1)
    (fun j => (hf'.2 _ (hvU j)).2) t ht0 (fun j => hct _ (hvU j))
  have hle := hz0opt _ hz'.1 hz'.2
  rw [objsum, objsum] at hle
  intro b hb
  obtain ⟨α, hα0, hα1, hyb, hbα⟩ := hinterp b hb
  rw [hyb]
  have := hcombC α hα0 hα1
  have hτt : τs ≤ t := by simpa [packz] using hle
  linarith

end Final2

end AffProof

open AffinePolicies.Simplex Matrix in
theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v) (hvnn : ∀ j, 0 ≤ v j)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      Feasible A B (simplexSet v) x y) :
    ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
      IsOptimalAdapt A B c d (simplexSet v) x (affinePolicy P q) := by
  obtain ⟨x, g, hopt⟩ := AffProof.exists_optimal_adapt A B c d hc hd v hv hfeas
  refine ⟨x, Ymat v g * (Qmat v)⁻¹,
    g (v (Fin.last m)) - (Ymat v g * (Qmat v)⁻¹) *ᵥ v (Fin.last m), ?_⟩
  have h : affinePolicy (Ymat v g * (Qmat v)⁻¹)
      (g (v (Fin.last m)) - (Ymat v g * (Qmat v)⁻¹) *ᵥ v (Fin.last m)) = interpolant v g := by
    funext b
    simp only [affinePolicy, interpolant, Matrix.mulVec_sub]
    abel
  rw [h]
  exact hopt
