-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.exists_bijection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:42.796955+00:00
-- url     : https://prove2.me/submissions/5fe638d0-398b-450b-9c5c-8df81c726597

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Bijection
import Theorems.Thm_AaronsonAmbainis_DetBij_exists_perm
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_agSet
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_diffSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ τ : Equiv.Perm (Ones g), (∀ x : Ones g, A x.1 ⊆ diffSet x.1 (τ x).1) ∧
      ∀ j, (univ.filter fun x : Ones g => (τ x).1 j = x.1 j).card ≤ bdry g j := by
  obtain ⟨σ, hσ, hcard⟩ := exists_perm hU hB g A hA
  refine ⟨σ.symm, fun x => ?_, fun j => ?_⟩
  · have h := hσ (σ.symm x)
    rw [Equiv.apply_symm_apply] at h
    intro i hi
    rw [mem_diffSet]
    exact fun hxi => Finset.disjoint_right.mp h hi (mem_agSet.mpr hxi)
  · have hc : (univ.filter fun y : Ones g => (σ.symm y).1 j = y.1 j).card
        = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by
      refine Finset.card_bij (fun (y : Ones g) _ => σ.symm y) ?_ ?_ ?_
      · intro y hy
        have hy' : (σ.symm y).1 j = y.1 j := (Finset.mem_filter.mp hy).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        show (σ (σ.symm y)).1 j = (σ.symm y).1 j
        rw [Equiv.apply_symm_apply]
        exact hy'.symm
      · intro y₁ _ y₂ _ h
        exact σ.symm.injective h
      · intro x hx
        have hx' : (σ x).1 j = x.1 j := (Finset.mem_filter.mp hx).2
        refine ⟨σ x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Equiv.symm_apply_apply σ x⟩
        show (σ.symm (σ x)).1 j = (σ x).1 j
        rw [Equiv.symm_apply_apply]
        exact hx'.symm
    rw [hc]
    exact hcard j
end AaronsonAmbainis.DetBij
