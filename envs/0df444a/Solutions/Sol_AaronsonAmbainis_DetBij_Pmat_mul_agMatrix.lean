-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.Pmat_mul_agMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:04.420132+00:00
-- url     : https://prove2.me/submissions/d3c79ef1-c9ec-4f4e-a21d-c4fd677c618c

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_Pmat_apply
import Theorems.Thm_AaronsonAmbainis_DetBij_Qmat_apply
import Theorems.Thm_AaronsonAmbainis_DetBij_agMatrix_apply
import Theorems.Thm_AaronsonAmbainis_DetBij_wing_sum
import Theorems.Thm_AaronsonAmbainis_DetBij_diffSet_flipSet
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_diffSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    Pmat g A * agMatrix g = Umat g A * Qmat g A := by
  refine Matrix.ext fun x z => ?_
  have hR : (Umat g A * Qmat g A) x z
      = (∏ i ∈ A x.1, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0) := by
    unfold Umat
    rw [Matrix.diagonal_mul, Qmat_apply]
  have hL : (Pmat g A * agMatrix g) x z
      = ∑ w ∈ univ.filter (fun w : Ones g => diffSet x.1 w.1 ⊆ A x.1),
          (∏ i ∈ diffSet x.1 w.1, -(X i : MvPolynomial ι ℤ)) * agMon w.1 z.1 := by
    rw [Matrix.mul_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pmat_apply, agMatrix_apply, ite_mul, zero_mul]
  rw [hL, hR, ← wing_sum]
  refine Finset.sum_bij (fun (w : Ones g) _ => diffSet x.1 w.1) ?_ ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hw).2
  · intro w₁ _ w₂ _ h
    have h' : diffSet x.1 w₁.1 = diffSet x.1 w₂.1 := h
    apply Subtype.ext
    calc w₁.1 = flipSet x.1 (diffSet x.1 w₁.1) := (flipSet_diffSet x.1 w₁.1).symm
      _ = flipSet x.1 (diffSet x.1 w₂.1) := by rw [h']
      _ = w₂.1 := flipSet_diffSet x.1 w₂.1
  · intro S hS
    have hS' : S ⊆ A x.1 := Finset.mem_powerset.mp hS
    refine ⟨⟨flipSet x.1 S, hA x S hS'⟩, ?_, diffSet_flipSet x.1 S⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [diffSet_flipSet]
    exact hS'
  · intro w _
    simp only [flipSet_diffSet]
end AaronsonAmbainis.DetBij
