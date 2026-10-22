-- Prove2me | solution 1 for AssortSearch.SearchQC.J_pos_N_neg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:00:25.980774+00:00
-- url     : https://prove2.me/submissions/ca26941b-fd74-431c-ae56-56f2f1e6e7bd

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_ProofTerms
set_option autoImplicit false

open AssortSearch.SearchQC in
theorem solution (lam VS x : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) (hx : 0 < x) :
    0 < Jfn lam VS x ∧ Nfn lam VS x < 0 := by
  have hs : 0 < x + VS := by linarith
  have ht : 0 < lam * (x + VS) := mul_pos hlam hs
  have he : Real.exp (-(lam * (x + VS))) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hep : 0 < Real.exp (-(lam * (x + VS))) := Real.exp_pos _
  have hH : 0 < Hbar lam VS x := by unfold Hbar; linarith
  have hH' : 0 < HbarDeriv lam VS x := by unfold HbarDeriv; positivity
  constructor
  · unfold Jfn
    apply div_pos _ (by positivity)
    have := mul_pos hH hVS
    have := mul_pos (mul_pos hH' hx) hs
    linarith
  · unfold Nfn
    apply div_neg_of_neg_of_pos _ (by positivity)
    unfold HbarDeriv Hbar
    -- t e^{-t} < 1 - e^{-t}
    set t := lam * (x + VS) with htdef
    have h1 : t + 1 < Real.exp t := Real.add_one_lt_exp ht.ne'
    have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have : lam * Real.exp (-t) * (x + VS) = t * Real.exp (-t) := by rw [htdef]; ring
    rw [this]
    nlinarith [mul_lt_mul_of_pos_right h1 hep]
