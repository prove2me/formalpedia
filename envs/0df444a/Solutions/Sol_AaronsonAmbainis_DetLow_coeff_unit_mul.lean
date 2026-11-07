-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.coeff_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:19:55.223546+00:00
-- url     : https://prove2.me/submissions/57b3b3c8-f98f-4acc-a1bc-a3997dd201a5

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ)
    (hm : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i) :
    coeff m (u * q) = coeff m q := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, m)]
  · have h0 : coeff 0 u = 1 := hu
    simp [h0]
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = m := by simpa using hab
    have ha : a ≠ 0 := by
      rintro rfl
      apply hne
      rw [zero_add] at hsum
      rw [hsum]
    have hb : coeff b q = 0 := by
      by_contra h
      have h1 := hm b (mem_support_iff.mpr h)
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (Finsupp.ext hcon)
      have h2 : 1 ≤ ∑ i, a i :=
        (Nat.one_le_iff_ne_zero.mpr hi).trans
          (Finset.single_le_sum (f := fun i => a i) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i))
      have h3 : ∑ i, m i = ∑ i, a i + ∑ i, b i := by
        rw [← hsum]
        simp [Finset.sum_add_distrib]
      omega
    simp [hb]
  · intro h
    exact absurd (by simp) h
end AaronsonAmbainis.DetLow
