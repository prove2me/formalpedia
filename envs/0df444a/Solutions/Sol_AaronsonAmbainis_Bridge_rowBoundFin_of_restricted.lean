-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBoundFin_of_restricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:58.346661+00:00
-- url     : https://prove2.me/submissions/cd5fe0e7-6d9a-4f1d-8a29-c3ed3d97dca1

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_printedConcl_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_printedConcl_of_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_const


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution
    (h : ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : Cube (Fin n) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      HasDegreeLE f d → PrintedConcl f d) : RowBoundFin := by
  intro n d f hf hdeg
  refine (printedConcl_iff f d).mp ?_
  by_cases hd : d = 0
  · subst hd
    exact printedConcl_of_const (hasDegreeLE_zero_const hdeg) 0
  by_cases hn : n = 0
  · subst hn
    exact printedConcl_of_const (fun x y => congrArg f (Subsingleton.elim x y)) d
  exact h n d (Nat.one_le_iff_ne_zero.mpr hn) (Nat.one_le_iff_ne_zero.mpr hd) f hf hdeg
end AaronsonAmbainis.Bridge
