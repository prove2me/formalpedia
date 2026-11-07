-- Prove2me | solution 1 for AaronsonAmbainis.lower_of_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:07.700791+00:00
-- url     : https://prove2.me/submissions/3b10eb0e-31e9-474b-ad70-0c58abced91f

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {u' : Cube ι} {y ℓ : ι → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hy : IsRow g u' y) (hu' : g u' = false) (G : Finset ι)
    (hG : ∀ j ∈ G, D * y j ≤ ℓ j) (hgG : g (flipSet u' G) = true) :
    D ≤ ∑ j ∈ G, ℓ j := by
  have hne : g (flipSet u' G) ≠ g u' := by rw [hgG, hu']; simp
  have h1 : 1 ≤ ∑ j ∈ G, y j := hy.2 G hne
  calc D = D * 1 := (mul_one D).symm
    _ ≤ D * ∑ j ∈ G, y j := mul_le_mul_of_nonneg_left h1 hD
    _ = ∑ j ∈ G, D * y j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ G, ℓ j := Finset.sum_le_sum hG
end AaronsonAmbainis
