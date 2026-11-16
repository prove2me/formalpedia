-- Prove2me | Definitions.Def_FracTruthSched_Supplement_ebsAssign
-- name    : FracTruthSched_Supplement_ebsAssign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:15:42.698357+00:00
-- url     : https://prove2.me/theorems/ac683175-d55d-4389-a1b4-180b8a50f93f
-- title:
--   Exp-Bounded-Square assignment (Algorithm 1) for one realization of the draws
-- statement:
--   Let $t=(t_{ij})$ be nonnegative processing times of $m$ tasks on $n\ge1$ machines, let $E=(E_{ij})$ be real weights and let $\pi_1,\dots,\pi_m$ be permutations of the machines. For each task $j$ put
--   $$t^{\min}_j=\min_i t_{ij},\qquad N_j=\{i:\ t_{ij}\le 2\,t^{\min}_j\}.$$
--   The **Exp-Bounded-Square assignment** sends task $j$ to
--
--   1. the first machine of $N_j$ in $\pi_j$, if $t^{\min}_j=0$;
--   2. otherwise, the first machine in $\pi_j$ among the minimizers $\arg\min_{i\in N_j} E_{ij}\,t_{ij}^2$.
--
--   With $E_{ij}\sim\mathrm{Exp}(1)$ and uniform $\pi_j$, all independent, this is the random integral allocation computed by Algorithm 1; its makespan is $\mathrm{Mech}_{\mathrm{EBS}}(t)$, the subject of Theorem 4.
--
--   **Formalization Note.** The output is a map $\sigma$ from tasks to machines; "first machine in $\pi_j$" is `firstInPerm`. $N_j$ uses $\le$, as printed. The rule is defined for every real $E$; the weight law lives on nonnegative weights.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §4.1, Algorithm 1, p.19

import Mathlib
import Definitions.Def_FracTruthSched_Supplement_firstInPerm

set_option autoImplicit false

namespace FracTruthSched.Supplement

/-- The task assignment of **Exp-Bounded-Square** (Anastasiadis et al., arXiv:2611.06642v1, §4.1,
Algorithm 1, p.19) for one realization of the random draws. Given nonnegative processing times
`t`, weights `E` (`E i j` the draw `E_ij ∼ Exp(1)`) and permutations `π` (`π j` the permutation
`π_j` of the machines), task `j` is assigned as follows: with `t^min_j := min_i t_ij` and
`N_j := {i : t_ij ≤ 2 · t^min_j}`, if `t^min_j = 0` then `j` goes to the first machine of `N_j` in
`π_j`; otherwise `j` goes to a machine of `argmin_{i ∈ N_j} E_ij · (t_ij)²`, ties broken by `π_j`
(the first minimizer in `π_j`).

**Formalization Note.** The output is the integral allocation `σ : Fin m → Fin n` (task `j` wholly to
machine `σ j`). The minimum `t^min_j` is `Finset.inf'` over the machines (`n ≥ 1` by `[NeZero n]`);
`N_j` uses `≤`, as printed. "First machine in `π_j`" is `firstInPerm`. The rule is evaluated for
every real `E`; the law of `E` (`expWeightLaw`) is concentrated on nonnegative weights. Each task's
assignment uses only column `j` of `t`, row-entries `E · j` and `π j` (task independence). -/
noncomputable def ebsAssign {n m : ℕ} [NeZero n] (t E : Fin n → Fin m → ℝ)
    (π : Fin m → Equiv.Perm (Fin n)) (j : Fin m) : Fin n :=
  let tmin : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => t i j)
  let N : Finset (Fin n) := Finset.univ.filter (fun i => t i j ≤ 2 * tmin)
  if tmin = 0 then firstInPerm (π j) N
  else firstInPerm (π j)
    (N.filter (fun i => ∀ i' ∈ N, E i j * t i j ^ 2 ≤ E i' j * t i' j ^ 2))

end FracTruthSched.Supplement


