-- Prove2me | solution 1 for ApproxPolySatCH.Main.coefficientIn_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:58:24.151326+00:00
-- url     : https://prove2.me/submissions/ab136db8-1b89-4649-ad09-d9dd84f149d3

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {A : Type} [CommRing A] {n : ℕ}
    (v : Fin n) (j : ℕ) (p : Poly A n) (d : Fin n →₀ ℕ) :
    (coefficientIn v j p).coeff d =
      if d v = 0 then p.coeff (d + Finsupp.single v j) else 0 := by
  classical
  rw [coefficientIn, MvPolynomial.coeff_sum]
  simp_rw [apply_ite (MvPolynomial.coeff d), MvPolynomial.coeff_zero,
    MvPolynomial.coeff_monomial]
  by_cases hd : d v = 0
  · simp only [hd, if_true]
    have hcondition (e : Fin n →₀ ℕ) (he : e v = j) :
        e - Finsupp.single v j = d ↔ e = d + Finsupp.single v j := by
      constructor
      · intro h
        calc
          e = e - Finsupp.single v j + Finsupp.single v j :=
            (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr he.ge)).symm
          _ = d + Finsupp.single v j := by rw [h]
      · intro h
        rw [h, add_tsub_cancel_right]
    have hterm (e : Fin n →₀ ℕ) :
        (if e v = j then if e - Finsupp.single v j = d then p.coeff e else 0 else 0) =
          if e = d + Finsupp.single v j then p.coeff e else 0 := by
      by_cases he : e v = j
      · simp [he, hcondition e he]
      · simp only [he, if_false]
        rw [if_neg]
        intro heq
        subst e
        simp [hd] at he
    simp_rw [hterm]
    by_cases hm : d + Finsupp.single v j ∈ p.support
    · simp [hm]
    · have hc : p.coeff (d + Finsupp.single v j) = 0 := by
        by_contra hc
        exact hm (MvPolynomial.mem_support_iff.mpr hc)
      simp [hm, hc]
  · simp only [hd, if_false]
    apply Finset.sum_eq_zero
    intro e he
    by_cases hjev : e v = j
    · simp only [hjev, if_true]
      rw [if_neg]
      intro heq
      have hz : (e - Finsupp.single v j) v = 0 := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, hjev, Nat.sub_self]
      rw [heq] at hz
      exact hd hz
    · simp [hjev]
