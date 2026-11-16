-- Prove2me | Definitions.Def_FracTruthSched_Supplement_firstInPerm
-- name    : FracTruthSched_Supplement_firstInPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:15:05.106749+00:00
-- url     : https://prove2.me/theorems/0cb48ef0-33af-4b19-b1f6-916784670f89
-- title:
--   First machine of a set $S$ in a permutation order $\pi$
-- statement:
--   Let $\pi$ be a permutation of the machines $\{0,\dots,n-1\}$, read as the order $\pi(0),\pi(1),\dots,\pi(n-1)$. For a nonempty set $S$ of machines, the **first machine of $S$ in $\pi$** is
--   $$\pi(k^{*}),\qquad k^{*}=\min\{k:\ \pi(k)\in S\}.$$
--
--   This is the tie-breaking rule of Exp-Bounded-Square (Algorithm 1): a task with a zero-cost machine goes to the first zero-cost machine in its permutation $\pi_j$, and a tie among minimizers of $E_{ij}t_{ij}^2$ is broken the same way.
--
--   **Formalization Note.** Position $k$ holds machine $\pi(k)$; for a uniformly random $\pi$ the other reading ($\pi^{-1}$) has the same law. For empty $S$ the value is $\pi(0)$; Algorithm 1 never applies the rule to an empty set.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §4.1, Algorithm 1, p.19

import Mathlib

set_option autoImplicit false

namespace FracTruthSched.Supplement

/-- The **first machine of a set `S` in the order `π`** (Anastasiadis et al., *Tight bounds for
fractional and randomized truthful scheduling*, arXiv:2611.06642v1, §4.1, Algorithm 1, p.19:
"Assign j to the first machine of N_j in π_j", "Break ties by π_j"). A permutation `π` of the
machines lists them in the order `π 0, π 1, …, π (n−1)`; the first machine of `S` is `π k` for the
least position `k` with `π k ∈ S`.

**Formalization Note.** Position `k` holds machine `π k` (one of the two possible readings of
"π_j as an order"; for a uniform random `π_j` the other reading, `π⁻¹`, has the same law, so the
algorithm's output distribution does not depend on the choice). If `S` is empty the value is `π 0`;
Algorithm 1 only applies the rule to nonempty sets, so this default is never used. -/
def firstInPerm {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Fin n :=
  if h : (Finset.univ.filter (fun k => π k ∈ S)).Nonempty then
    π ((Finset.univ.filter (fun k => π k ∈ S)).min' h)
  else π 0

end FracTruthSched.Supplement


