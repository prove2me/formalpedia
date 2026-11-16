-- Prove2me | Definitions.Def_FracTruthSched_Supplement_expWeightLaw
-- name    : FracTruthSched_Supplement_expWeightLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:16:00.330324+00:00
-- url     : https://prove2.me/theorems/fc299ef7-1048-401e-8280-2c0c9751c093
-- title:
--   Law of the weights $E_{ij}\sim\mathrm{Exp}(1)$, i.i.d. over machines and tasks
-- statement:
--   For $n$ machines and $m$ tasks, the **weight law** is the probability measure on real $n\times m$ matrices $E=(E_{ij})$ under which the entries are independent and each $E_{ij}$ is exponentially distributed with rate $1$:
--   $$E_{ij}\sim\mathrm{Exp}(1),\qquad \Pr[E_{ij}>x]=e^{-x}\ (x\ge0),\quad\text{all independent}.$$
--
--   These are the random weights of Exp-Bounded-Square (Algorithm 1).
--
--   **Formalization Note.** Mathlib's `ProbabilityTheory.expMeasure 1`, combined by the product measure `Measure.pi` over machines and tasks. The uniform permutations of Algorithm 1 are averaged over separately in `ebsExpectedMakespan`.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §4.1, Algorithm 1, p.19

import Mathlib

set_option autoImplicit false

namespace FracTruthSched.Supplement

open MeasureTheory ProbabilityTheory

/-- The **law of the exponential weights** of Exp-Bounded-Square (Anastasiadis et al.,
arXiv:2611.06642v1, §4.1, Algorithm 1, p.19: "Draw E_ij ∼ Exp(1) independently for every i ∈ N",
for every task `j`): the product over all machines `i` and tasks `j` of the exponential
distribution with rate `1`, a probability measure on the weight matrices `E : Fin n → Fin m → ℝ`.

**Formalization Note.** `ProbabilityTheory.expMeasure 1` is Mathlib's exponential distribution with
rate `1` (density `e^{−x}` on `[0, ∞)`); `Measure.pi` makes all `n · m` weights independent. The
uniform permutations `π_j` are averaged over separately (`ebsExpectedMakespan`). -/
noncomputable def expWeightLaw (n m : ℕ) : Measure (Fin n → Fin m → ℝ) :=
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => expMeasure 1

end FracTruthSched.Supplement


