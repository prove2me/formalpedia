-- Prove2me | Definitions.Def_DiscreteLipschitzFree
-- name    : DiscreteLipschitzFree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.152911+00:00
-- url     : https://prove2.me/theorems/3f71eb8b-1af4-4459-a038-0fda75f48046
-- statement:
--   For a metric space M with basepoint o, Lip0(o) is the real vector space of Lipschitz functions f:M→ℝ with f(o)=0. Its norm is induced by the bounded slope function (x,y)↦(f(x)−f(y))/dist(x,y), taking the quotient as zero on the diagonal; thus it is the supremum of the absolute slopes. Evaluation at x is a continuous linear functional with |f(x)|≤dist(x,o)‖f‖. The Lipschitz-free space FreeSpace(o) is the closed real linear span of all these evaluation functionals in the continuous dual of Lip0(o), with its inherited norm, and δ(o,x) denotes evaluation at x viewed in this space. For a real normed space X, HasAP means that for every compact C⊆X and ε>0 there is a continuous finite-rank linear operator T:X→X and a real η<ε such that ‖Tu−u‖≤η for every u∈C. HasBAP(X,Λ) additionally requires ‖T‖≤Λ. The defined proposition BlockStatement says that for every integer p≥1 there exist a countable pointed metric space (M,o), with distinct points at distance at least 1 and all distances at most 300p²+150p+5, and a finite set A containing o, such that every continuous finite-rank operator T on FreeSpace(o) with ‖T‖≤p has some a∈A satisfying ‖Tδ(o,a)−δ(o,a)‖≥1/2. The defined proposition MainStatement asserts the existence of a countable pointed metric space whose distinct points are at distance at least 1, which is unbounded and not proper, and whose Lipschitz-free space has HasAP but fails HasBAP(X,Λ) for every real Λ≥1. Neither proposition is asserted here as a proved theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DiscreteLipschitzFree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DiscreteLipschitzFree.lean; bytes 16..5762
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Real Lipschitz-free spaces and approximation properties
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def lipSubmodule (o : M) : Submodule ℝ (M → ℝ) where
  carrier := {f | f o = 0 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y, |f x - f y| ≤ C * dist x y}
  zero_mem' := by
    refine ⟨rfl, 0, le_rfl, ?_⟩
    intro x y
    simp
  add_mem' := by
    rintro f g ⟨hfo, C, hC, hf⟩ ⟨hgo, D, hD, hg⟩
    refine ⟨by simpa using congrArg₂ (· + ·) hfo hgo,
      C + D, add_nonneg hC hD, ?_⟩
    intro x y
    change |f x + g x - (f y + g y)| ≤ (C + D) * dist x y
    calc
      _ = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ C * dist x y + D * dist x y := add_le_add (hf x y) (hg x y)
      _ = _ := by ring
  smul_mem' := by
    rintro c f ⟨hfo, C, hC, hf⟩
    refine ⟨by simp [hfo], |c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
    intro x y
    change |c * f x - c * f y| ≤ (|c| * C) * dist x y
    calc
      _ = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
      _ ≤ |c| * (C * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)
      _ = _ := by ring

def Lip0 (o : M) := ↥(lipSubmodule o)

namespace Lip0

variable {o : M}

instance : AddCommGroup (Lip0 o) := inferInstanceAs (AddCommGroup ↥(lipSubmodule o))
instance : Module ℝ (Lip0 o) := inferInstanceAs (Module ℝ ↥(lipSubmodule o))

instance : CoeFun (Lip0 o) (fun _ => M → ℝ) := ⟨fun f => f.val⟩

def slope (o : M) : Lip0 o →ₗ[ℝ] lp (fun _ : M × M => ℝ) ∞ where
  toFun f := ⟨fun z : M × M => (f z.1 - f z.2) / dist z.1 z.2, by
    obtain ⟨C, hC, hf⟩ := f.property.2
    apply memℓp_infty
    refine ⟨C, ?_⟩
    rintro r ⟨⟨x, y⟩, rfl⟩
    change ‖(f x - f y) / dist x y‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg]
    by_cases hxy : x = y
    · simp [hxy, hC]
    · exact (div_le_iff₀ (dist_pos.mpr hxy)).2 (hf x y)⟩
  map_add' f g := by
    apply lp.ext
    funext z
    change ((f z.1 + g z.1) - (f z.2 + g z.2)) / dist z.1 z.2 =
      (f z.1 - f z.2) / dist z.1 z.2 + (g z.1 - g z.2) / dist z.1 z.2
    ring
  map_smul' c f := by
    apply lp.ext
    funext z
    change (c * f z.1 - c * f z.2) / dist z.1 z.2 =
      c * ((f z.1 - f z.2) / dist z.1 z.2)
    ring

instance (o : M) : NormedAddCommGroup (Lip0 o) :=
  NormedAddCommGroup.induced _ _ (slope o).toAddMonoidHom (by
    intro f g h
    apply Subtype.ext
    funext x
    have hx := congrArg (fun q : lp (fun _ : M × M => ℝ) ∞ => q (x, o)) h
    change (f x - f o) / dist x o = (g x - g o) / dist x o at hx
    rw [f.property.1, g.property.1, sub_zero, sub_zero] at hx
    by_cases hxo : x = o
    · rw [hxo, f.property.1, g.property.1]
    · exact (div_left_inj' (ne_of_gt (dist_pos.mpr hxo))).mp hx)

instance (o : M) : NormedSpace ℝ (Lip0 o) :=
  NormedSpace.induced ℝ _ _ (slope o)

end Lip0

def evaluation (o x : M) : (Lip0 o →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    ({ toFun := fun f : Lip0 o => f x
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : Lip0 o →ₗ[ℝ] ℝ)
    (dist x o) (fun f => by
      change ‖f x‖ ≤ dist x o * ‖f‖
      rw [mul_comm]
      have hx := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0)
        (Lip0.slope o f) (x, o)
      change ‖(f x - f o) / dist x o‖ ≤ ‖f‖ at hx
      rw [f.property.1, sub_zero, norm_div, Real.norm_of_nonneg dist_nonneg] at hx
      by_cases hxo : x = o
      · rw [hxo, f.property.1, norm_zero, dist_self, mul_zero]
      · exact (div_le_iff₀ (dist_pos.mpr hxo)).mp hx)

def freeSubmodule (o : M) : Submodule ℝ ((Lip0 o →L[ℝ] ℝ)) :=
  (Submodule.span ℝ (Set.range (evaluation o))).topologicalClosure

def FreeSpace (o : M) := ↥(freeSubmodule o)

instance (o : M) : NormedAddCommGroup (FreeSpace o) :=
  inferInstanceAs (NormedAddCommGroup ↥(freeSubmodule o))

instance (o : M) : NormedSpace ℝ (FreeSpace o) :=
  inferInstanceAs (NormedSpace ℝ ↥(freeSubmodule o))

def delta (o x : M) : FreeSpace o :=
  ⟨evaluation o x, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, rfl⟩)⟩

def HasAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def HasBAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ‖T‖ ≤ Λ ∧ ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def blockBound (p : ℕ) : ℝ := 300 * (p : ℝ)^2 + 150 * (p : ℝ) + 5

def BlockStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∃ (M : Type) (d : MetricSpace M) (o : M),
    letI := d
    Countable M ∧ (∀ x y : M, x ≠ y → 1 ≤ dist x y) ∧
      (∀ x y : M, dist x y ≤ blockBound p) ∧
      ∃ A : Finset M, o ∈ A ∧ ∀ T : FreeSpace o →L[ℝ] FreeSpace o,
        Module.Finite ℝ (LinearMap.range T.toLinearMap) → ‖T‖ ≤ (p : ℝ) →
          ∃ a ∈ A, (1 / 2 : ℝ) ≤ ‖T (delta o a) - delta o a‖

def MainStatement : Prop :=
  ∃ (M : Type) (d : MetricSpace M) (o : M),
    letI := d
    Countable M ∧ (∀ x y : M, x ≠ y → 1 ≤ dist x y) ∧
      (¬ Bornology.IsBounded (Set.univ : Set M)) ∧
      (¬ ProperSpace M) ∧ HasAP (FreeSpace o) ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ¬ HasBAP (FreeSpace o) Λ



end DiscreteFree
end
end OAI


