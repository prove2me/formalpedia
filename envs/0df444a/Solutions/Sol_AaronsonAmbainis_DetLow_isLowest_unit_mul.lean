-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.isLowest_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:11.858164+00:00
-- url     : https://prove2.me/submissions/f59440e3-b029-4365-b024-18bc2d635f94

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Theorems.Thm_AaronsonAmbainis_DetLow_coeff_unit_mul

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest q m) : IsLowest (u * q) m := by
  obtain ⟨hmem, hmin⟩ := h
  refine ⟨?_, ?_⟩
  · rw [mem_support_iff, coeff_unit_mul u q hu m hmin]
    exact mem_support_iff.mp hmem
  · intro m' hm'
    by_contra hlt
    push Not at hlt
    have hmin' : ∀ m'' ∈ q.support, ∑ i, m' i ≤ ∑ i, m'' i := fun m'' h'' =>
      hlt.le.trans (hmin m'' h'')
    have h1 := coeff_unit_mul u q hu m' hmin'
    have h2 : coeff m' q = 0 := by
      by_contra hne
      have := hmin m' (mem_support_iff.mpr hne)
      omega
    rw [mem_support_iff, h1] at hm'
    exact hm' h2
end AaronsonAmbainis.DetLow
