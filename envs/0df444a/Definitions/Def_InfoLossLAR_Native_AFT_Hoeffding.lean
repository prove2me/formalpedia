-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
-- name    : InfoLossLAR_Native_AFT_Hoeffding
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:50.919773+00:00
-- url     : https://prove2.me/theorems/a4a1bc2d-dece-45ad-a8a6-e61c0a8ad8b6
-- title:
--   Finite product laws and coordinatewise orthogonality
-- statement:
--   For a finite family of probability laws $(p_i)$, the independent product has mass $p(x)=\prod_i p_i(x_i)$. For a real function $f$, define $$\mathbb E_p f=\sum_xp(x)f(x),\qquad\|f\|_{L^2(p)}^2=\mathbb E_p(f^2).$$ Coordinate dependence and coordinate centering specify canonical finite product components. Their finite-sum orthogonality and expectation identities support the sampler estimates.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/Hoeffding.lean; migrated source SHA256 3842e732da87d1af12267e87c9f7ce898d2f54b564f0bfdc4da28486ea9e09b6; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_Histogram
import Mathlib


/-!
# Exact finite product orthogonality and histogram isometry

The sums in this file are over the actual finite product space. No limiting
Poisson experiment or infinite-population normalization is used.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

namespace FiniteDist

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- The product of a finite, possibly nonidentical family of laws. -/
noncomputable def independent [DecidableEq ι] (p : ι → FiniteDist α) : FiniteDist (ι → α) where
  weight x := ∏ i, (p i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (p i).nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [sum_one, Finset.prod_const_one]

/-- Real expectation, including signed functions. -/
noncomputable def expectation (p : FiniteDist α) (f : α → ℝ) : ℝ :=
  ∑ x, p.weight x * f x

/-- Squared `L²` norm with respect to the specified law. -/
noncomputable def l2Sq (p : FiniteDist α) (f : α → ℝ) : ℝ :=
  p.expectation fun x => f x ^ 2

theorem l2Sq_nonneg (p : FiniteDist α) (f : α → ℝ) : 0 ≤ p.l2Sq f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg _)

theorem expectation_map (p : FiniteDist α) (g : α → β) (f : β → ℝ) :
    (p.map g).expectation f = p.expectation (f ∘ g) := by
  classical
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]



theorem expectation_independent_split (p : ι → FiniteDist α)
    (i : ι) (f : (ι → α) → ℝ) :
    (independent p).expectation f =
      ∑ y : {j : ι // j ≠ i} → α,
        (∏ j : {j : ι // j ≠ i}, (p j).weight (y j)) *
          ∑ a, (p i).weight a * f ((Equiv.funSplitAt i α).symm (a, y)) := by
  classical
  unfold expectation independent
  rw [← (Equiv.funSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (∏ j, (p j).weight ((Equiv.funSplitAt i α).symm (a, y) j)) =
      (p i).weight a * ∏ j : {j : ι // j ≠ i}, (p j).weight (y j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    apply congrArg₂ (· * ·)
    · simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro j _
      simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]
  change (∏ j, (p j).weight ((Equiv.funSplitAt i α).symm (a, y) j)) * _ = _
  rw [hp]
  ring

end FiniteDist

namespace Hoeffding

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A function uses only coordinates in `S`. -/
def DependsOn (S : Finset ι) (f : (ι → α) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- Conditional mean zero in one coordinate, with all others fixed. -/
def CenteredAt (p : ι → FiniteDist α) (i : ι) (f : (ι → α) → ℝ) : Prop :=
  ∀ x, ∑ a, (p i).weight a * f (Function.update x i a) = 0

/-- The actual canonicality condition for a finite-product kernel. -/
def Canonical (p : ι → FiniteDist α) (S : Finset ι) (f : (ι → α) → ℝ) : Prop :=
  DependsOn S f ∧ ∀ i ∈ S, CenteredAt p i f

/-- Integrating a coordinate appearing in just one factor annihilates the
inner product. This is the exact finite-population orthogonality argument. -/
theorem orthogonal_of_centered (p : ι → FiniteDist α) (S : Finset ι)
    (i : ι) (hi : i ∉ S) (f g : (ι → α) → ℝ)
    (hf : CenteredAt p i f) (hg : DependsOn S g) :
    (FiniteDist.independent p).expectation (fun x => f x * g x) = 0 := by
  classical
  rw [FiniteDist.expectation_independent_split p i]
  apply Finset.sum_eq_zero
  intro y _
  haveI : Nonempty α := by
    by_contra hn
    haveI : IsEmpty α := not_nonempty_iff.mp hn
    have h := (p i).sum_one
    simp at h
  let x : ι → α := (Equiv.funSplitAt i α).symm (Classical.choice inferInstance, y)
  have hupdate (a : α) :
      (Equiv.funSplitAt i α).symm (a, y) = Function.update x i a := by
    funext j
    by_cases hji : j = i
    · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, Function.update, hji, x]
  have hgx (a : α) : g (Function.update x i a) = g x := by
    apply hg
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    exact Function.update_of_ne hji a x
  simp_rw [hupdate, hgx, ← mul_assoc]
  rw [← Finset.sum_mul, hf x, zero_mul, mul_zero]

theorem canonical_orthogonal (p : ι → FiniteDist α) (S T : Finset ι)
    (hne : S ≠ T) (f g : (ι → α) → ℝ)
    (hf : Canonical p S f) (hg : Canonical p T g) :
    (FiniteDist.independent p).expectation (fun x => f x * g x) = 0 := by
  classical
  by_cases hST : S ⊆ T
  · have hTS : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
    simpa [mul_comm] using orthogonal_of_centered p S i hiS g f (hg.2 i hiT) hf.1
  · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    exact orthogonal_of_centered p T i hiT f g (hf.2 i hiS) hg.1

/-- Exact Pythagoras for an arbitrary finite collection of canonical kernels
on distinct coordinate sets. The index collection may contain every subset. -/
theorem canonical_sum_l2Sq (p : ι → FiniteDist α) (sets : Finset (Finset ι))
    (kernels : Finset ι → (ι → α) → ℝ)
    (h : ∀ S ∈ sets, Canonical p S (kernels S)) :
    (FiniteDist.independent p).l2Sq (fun x => ∑ S ∈ sets, kernels S x) =
      ∑ S ∈ sets, (FiniteDist.independent p).l2Sq (kernels S) := by
  classical
  unfold FiniteDist.l2Sq FiniteDist.expectation
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single S]
  · intro T hT hTS
    have hzero := canonical_orthogonal p S T (Ne.symm hTS)
      (kernels S) (kernels T) (h S hS) (h T hT)
    simpa only [FiniteDist.expectation, mul_assoc] using hzero
  · exact fun hn => False.elim (hn hS)



/-- Centered density of a point mass relative to the reference color law. -/
noncomputable def centeredAtom (p : FiniteDist α) (source value : α) : ℝ :=
  (if source = value then (p.weight value)⁻¹ else 0) - 1

theorem centeredAtom_mean (p : FiniteDist α) (hp : ∀ a, 0 < p.weight a)
    (source : α) : ∑ a, p.weight a * centeredAtom p source a = 0 := by
  classical
  simp only [centeredAtom, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_one]
  have hm (a : α) : p.weight a * (if source = a then (p.weight a)⁻¹ else 0) =
      if source = a then (1 : ℝ) else 0 := by
    split_ifs <;> simp [ne_of_gt (hp a)]
  simp_rw [hm]
  simp

/-- The canonical coefficient on a specified subset, computed directly from
an arbitrary signed measure on the labeled product space. -/
noncomputable def densityComponent (p : ι → FiniteDist α)
    (mass : (ι → α) → ℝ) (S : Finset ι) (y : ι → α) : ℝ :=
  ∑ x, mass x * ∏ i ∈ S, centeredAtom (p i) (x i) (y i)



theorem centeredAtom_subset_sum (p : ι → FiniteDist α) (x y : ι → α) :
    (∑ S : Finset ι, ∏ i ∈ S, centeredAtom (p i) (x i) (y i)) =
      if x = y then (∏ i, (p i).weight (y i))⁻¹ else 0 := by
  classical
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  simp only [centeredAtom, add_comm (1 : ℝ), sub_add_cancel]
  rw [Fintype.prod_ite_zero]
  simp only [← funext_iff, Finset.prod_inv_distrib]

/-- Exact full Hoeffding expansion of any signed density. The sum includes
all subsets, including degrees near the entire population size. -/
theorem densityComponent_sum (p : ι → FiniteDist α)
    (mass : (ι → α) → ℝ) (y : ι → α) :
    (∑ S : Finset ι, densityComponent p mass S y) =
      mass y / (FiniteDist.independent p).weight y := by
  classical
  unfold densityComponent
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, centeredAtom_subset_sum]
  simp [mul_ite, div_eq_mul_inv, FiniteDist.independent]



end Hoeffding

section HistogramIsometry

variable {dimension : ℕ} {Color : Type*} [Fintype Color]





end HistogramIsometry

end AFT


