-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.det_inequality_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:41.600793+00:00
-- url     : https://prove2.me/submissions/e0a1c795-96a8-4ad6-a6b3-13f560762c9a

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
import Theorems.Thm_AaronsonAmbainis_DetBij_extWing_of_mem
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_antipode_agSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (ℓ : ι → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (A : Cube ι → Finset ι) (d : Cube ι → ℝ)
    (hd : ∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j)
    (σ : Equiv.Perm (Ones g))
    (hσ : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (extWing g A (σ x).1))
    (hcard : ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j) :
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by
  -- Step 1: the sum over the zone as a sum over the ones of `g`
  have hz : zone g ⊆ univ.filter (fun x : Cube ι => g x = true) := by
    intro u hu
    simp only [zone, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1
  have e0 : ∑ u ∈ univ.filter (fun x : Cube ι => g x = true), (if u ∈ zone g then d u else 0)
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) :=
    Finset.sum_subtype _ (fun x => by simp) (fun u => if u ∈ zone g then d u else 0)
  have h1 : ∑ u ∈ zone g, d u = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := by
    rw [← e0, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hz]
  -- Step 2: the bound at each point (the hypothesis on `d` at `G = ag(y, σ⁻¹ y)`)
  have h2 : ∀ y : Ones g,
      (if y.1 ∈ zone g then d y.1 else 0) ≤ ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j := by
    intro y
    split_ifs with hy
    · refine hd y.1 hy _ ?_ ?_
      · have h := hσ (σ.symm y)
        rw [Equiv.apply_symm_apply, extWing_of_mem g A hy] at h
        exact h
      · rw [flipSet_antipode_agSet]
        exact (σ.symm y).2
    · exact Finset.sum_nonneg fun j _ => (hℓ j).le
  -- Step 3: reindex by `σ`
  have h3 : ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j
      = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := by
    refine (Equiv.sum_comp σ
      (fun y : Ones g => ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.symm_apply_apply]
  -- Step 4: exchange the two sums
  have h4 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
      = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := by
    have e1 : ∀ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 := by
      intro x
      unfold agSet
      rw [Finset.sum_filter]
    have e2 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ x : Ones g, ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 :=
      Finset.sum_congr rfl fun x _ => e1 x
    rw [e2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 5: the bound on the multiplicities
  have h5 : ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ)
      ≤ ∑ j, ℓ j * (bdry g j : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcard j)) (hℓ j).le
  calc ∑ u ∈ zone g, d u
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := h1
    _ ≤ ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j :=
        Finset.sum_le_sum fun y _ => h2 y
    _ = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := h3
    _ = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := h4
    _ ≤ ∑ j, ℓ j * (bdry g j : ℝ) := h5
end AaronsonAmbainis.DetBij
