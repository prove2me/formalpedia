-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:20.155413+00:00
-- url     : https://prove2.me/submissions/51ae854a-e70c-4670-90f7-28e34b183851

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_weights_nonneg_of_row

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : RowBound) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ c : Cube ι → ι → ℝ, (∀ x i, 0 ≤ c x i) ∧
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) := by
  obtain ⟨c, h1, h2⟩ := h ι d f hf hdeg
  exact ⟨c, weights_nonneg_of_row h1, h1, h2⟩
end AaronsonAmbainis.Bridge
