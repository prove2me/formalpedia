-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.weights_nonneg_of_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:04.671072+00:00
-- url     : https://prove2.me/submissions/c464cdcd-0b0d-4e34-bd99-84f2b2da05e9

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_flipSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {f : Cube ι → ℝ}
    {c : Cube ι → ι → ℝ} (h : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) (x : Cube ι)
    (i : ι) : 0 ≤ c x i := by
  have h1 := h x (flipSet x {i})
  rw [diffSet_flipSet, Finset.sum_singleton] at h1
  exact (abs_nonneg _).trans h1
end AaronsonAmbainis.Bridge
