-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.exists_poly_of_hasDegreeLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:22.581574+00:00
-- url     : https://prove2.me/submissions/93bd75e2-8acb-4db3-b341-78141ae80031

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_totalDegree_letter

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {v : Cube ι → ι → ℝ} {a b : ℝ}
    (hv : ∀ x i, (if x i then (-1 : ℝ) else 1) = a + b * v x i)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (v x) p := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨∑ S : Finset ι, C (c S) * ∏ i ∈ S, (C a + C b * X i), ?_, fun x => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le (fun S _ => ?_)
    by_cases hS : d < S.card
    · rw [hc S hS, C_0, zero_mul, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le d
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => totalDegree_letter a b i)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      exact not_lt.mp hS
  · rw [hf x, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_mul, MvPolynomial.eval_C, map_prod]
    congr 1
    unfold chi
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact hv x i
end AaronsonAmbainis.Bridge
