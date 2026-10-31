-- Prove2me | Definitions.Def_StochDepartSec_outcomeLaw
-- name    : StochDepartSec_outcomeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:46.454999+00:00
-- url     : https://prove2.me/theorems/948635c9-4cc2-48dc-a4e2-5110dc74a9fd
-- title:
--   Law of the arrival times, waiting times, order and seed
-- statement:
--   Let $\mathcal A$ (arrival distribution) and $\mathcal L$ (waiting time distribution) be probability measures on $\mathbb R$. The law of an outcome $\omega=(a,\ell,\sigma,u)$ is the product measure
--
--   $$
--   \mathbb P_{n,\mathcal A,\mathcal L}=\mathcal A^{\otimes n}\otimes\mathcal L^{\otimes n}\otimes\mathrm{Unif}(S_n)\otimes\mathrm{Unif}[0,1]:
--   $$
--
--   the arrival times are i.i.d. with law $\mathcal A$, the waiting times are i.i.d. with law $\mathcal L$, the overall order is uniform over the $n!$ permutations, the seed is uniform on $[0,1]$, and all four are independent.
--
--   **Formalization Note** The standing assumptions of the paper's model, that events occur in $[0,1]$ ($\mathcal A([0,1])=1$) and that waiting times are non-negative ($\mathcal L([0,\infty))=1$), are hypotheses of the theorems, not part of this definition.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
open MeasureTheory

namespace StochDepartSec

/-- The law of an outcome: arrival times i.i.d. from `A`, waiting times i.i.d. from `L`, the
overall order uniform over all `n!` permutations, and the seed uniform on `[0, 1]`, all
independent.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "an arrival time A_i is drawn independently from the arrival distribution A and a
waiting time L_i … drawn i.i.d. from some distribution L"; the order is uniformly random ("We can
therefore apply the principle of deferred decisions and assume that R_{i+1}, …, R_n will be drawn
independently at later points in time").

**Formalization Note** The law is the product measure
`A^{⊗n} ⊗ L^{⊗n} ⊗ Unif(Perm (Fin n)) ⊗ Unif[0,1]`. The standing assumptions of §2 ("events only
occur in the interval [0, 1]", waiting times non-negative) are hypotheses `A [0,1] = 1`,
`L [0,∞) = 1` of the theorems, not part of this definition. -/
noncomputable def outcomeLaw (n : ℕ) (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] : Measure (Outcome n) :=
  (Measure.pi fun _ : Fin n => A).prod ((Measure.pi fun _ : Fin n => L).prod
    ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.prod
      (volume.restrict (Set.Icc (0 : ℝ) 1))))

end StochDepartSec


