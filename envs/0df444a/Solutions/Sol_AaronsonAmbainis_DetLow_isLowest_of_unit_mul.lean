-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.isLowest_of_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:13.37257+00:00
-- url     : https://prove2.me/submissions/ba3a6ad7-632e-4508-865c-d79de30593e5

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Theorems.Thm_AaronsonAmbainis_DetLow_coeff_unit_mul
import Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_unit_mul
import Theorems.Thm_AaronsonAmbainis_DetLow_exists_isLowest

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest (u * q) m) : IsLowest q m := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h0 := h.1
    simp at h0
  obtain ⟨m0, hm0⟩ := exists_isLowest q hq
  have hm0' := isLowest_unit_mul u q hu m0 hm0
  have hle1 : ∑ i, m i ≤ ∑ i, m0 i := h.2 m0 hm0'.1
  have hmin : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i := fun m' hm' =>
    hle1.trans (hm0.2 m' hm')
  refine ⟨?_, hmin⟩
  have h1 := h.1
  rw [mem_support_iff, coeff_unit_mul u q hu m hmin] at h1
  exact mem_support_iff.mpr h1
end AaronsonAmbainis.DetLow
