-- Prove2me | solution 1 for AaronsonAmbainis.sum_allPairsTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:44.761772+00:00
-- url     : https://prove2.me/submissions/5b1f61a7-9a89-4526-9616-74f51e4be2de

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ) (x : Cube ι) :
    ∑ F : Finset ι, allPairsTerm g w lam F x
      = ∑ y, if g x = true ∧ g y = false then
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ else 0 := by
  apply Fintype.sum_equiv (flipEquiv x)
  intro F
  show allPairsTerm g w lam F x = if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ diffSet x (flipSet x F), w j * lam x j * lam (flipSet x F) j)⁻¹ else 0
  rw [diffSet_flipSet]
  rfl
end AaronsonAmbainis
