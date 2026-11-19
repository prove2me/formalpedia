-- Prove2me | solution 1 for APSCounting893.Main.effective_exceptional_locus_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:40:24.785863+00:00
-- url     : https://prove2.me/submissions/bae66cc2-1e2c-4b4c-b733-9f89b94cd415

import Theorems.Thm_APSCounting893_Main_perron_exceptional_polynomial
import Theorems.Thm_APSCounting893_Main_perron_nonvanishing_finite_surjective

set_option autoImplicit false
open APSCounting893.Main MvPolynomial

theorem solution (F : ReducedMap)
    (c : Affine ℂ F.n) (hc : IsNormalization (imageClosure F.F) c) :
    ∃ U : Set (Affine ℂ (F.n + 1)), GoodOpen F U ∧
      projectiveDegree (imageClosure F.F \ U) ≤ F.n * F.d ^ (2 * F.n) := by
  obtain ⟨p, b, hprod, hb, hbdeg, hpdeg, hroot, hdegree⟩ :=
    perron_exceptional_polynomial F c hc
  refine ⟨{y ∈ imageClosure F.F | MvPolynomial.eval (normalization c y) b ≠ 0},
    perron_nonvanishing_finite_surjective F c hc p b hb hprod hroot, ?_⟩
  have hset : imageClosure F.F \ {y ∈ imageClosure F.F | MvPolynomial.eval (normalization c y) b ≠ 0} =
      {y ∈ imageClosure F.F | MvPolynomial.eval (normalization c y) b = 0} := by
    ext y
    simp only [Set.mem_diff, Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact hdegree

