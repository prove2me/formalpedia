-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
-- name    : OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:16:52.633399+00:00
-- url     : https://prove2.me/theorems/8990eb4d-e2e2-4868-86d7-b5478cd7406c
-- title:
--   Finite real-weighted simplices
-- statement:
--   For real weights w indexed by a finite set of d coordinates and a real height H, define the finite weak simplex of natural exponent vectors using coordinate ranges up to the natural floor of H/w_i and the inequality sum_i w_i a_i <= H. Define the strict simplex by filtering this finite weak simplex with sum_i w_i a_i < H. These exact finite sets supply the row and column domains of the interpolation matrix; no positivity or asymptotic theorem is asserted here.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexCounting.lean#L154-L163

import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent

open Filter Topology

noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

noncomputable def strictWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (realWeightedSimplex w H).filter (fun a => ∑ i, w i * (a i : ℝ) < H)

end PiExponent

end OAI


