-- Prove2me | solution 1 for AaronsonAmbainis.card_sensitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:13.220493+00:00
-- url     : https://prove2.me/submissions/971e0e34-8de3-4c7c-a32b-07390ebeee45

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Theorems.Thm_AaronsonAmbainis_flipSet_flipSet_self


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card = 2 * bdry g j := by
  have hsplit : (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x)
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
        ∪ (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hx : g x <;> cases hy : g (flipSet x {j}) <;> simp
  have hdisj : Disjoint (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
      (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1.1] at h2
    exact Bool.noConfusion h2.1
  have hB : (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true).card
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card := by
    apply Finset.card_bij (fun x _ => flipSet x {j})
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [flipSet_flipSet_self]
      exact ⟨hx.2, hx.1⟩
    · intro x _ y _ h
      have h' := congrArg (fun z => flipSet z {j}) h
      simpa [flipSet_flipSet_self] using h'
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨flipSet y {j}, ?_, flipSet_flipSet_self y {j}⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [flipSet_flipSet_self]
      exact ⟨hy.2, hy.1⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hB]
  unfold bdry
  ring
end AaronsonAmbainis
