-- Prove2me | Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
-- name    : RiemannMasullo_RapidDecaySequenceBound
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T02:23:25.787762+00:00
-- url     : https://prove2.me/theorems/1427220c-f745-4469-a086-3e2fd42fb7b4
-- title:
--   Weighted absolute sums for lattice sequences
-- statement:
--   The j-th bound of a complex lattice sequence is the sum of its pointwise absolute values weighted by (1+‖a‖)^j.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L506-L510

import Mathlib
open scoped ENNReal
noncomputable section
namespace RiemannMasullo
variable {r : ℕ}
def rapidDecaySequenceBound (j : ℕ) (s : (Fin r → ℤ) → ℂ) : ℝ≥0∞ :=
  ∑' a : Fin r → ℤ,
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
      (‖s a‖₊ : ℝ≥0∞)
end RiemannMasullo


