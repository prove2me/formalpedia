-- Prove2me | Definitions.Def_UnrelatedSched_FixedMachines_DeadlineLP
-- name    : UnrelatedSched_FixedMachines_DeadlineLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:29.93915+00:00
-- url     : https://prove2.me/theorems/afc3e28b-5f0b-45c9-a893-07e3f09e9cbb
-- title:
--   The linear program (LP) of the Rounding Theorem, for a sub-instance of the jobs
-- statement:
--   Consider $m$ machines and $n$ jobs, and let $p_{ij}$ be the processing time of job $j$ on machine $i$. For a threshold $t$ let $J_i(t)=\{j : p_{ij}\le t\}$ be the jobs that need at most $t$ time units on machine $i$, and $M_j(t)=\{i : p_{ij}\le t\}$ the machines that can process job $j$ in at most $t$ time units. Fix a set $R$ of jobs, machine deadlines $d_1,\dots,d_m$ and a threshold $t$. The linear program (LP) of the Rounding Theorem for the jobs in $R$ asks for real numbers $x_{ij}$ with
--
--   $$
--   \sum_{i\in M_j(t)} x_{ij}=1 \quad (j\in R),\qquad \sum_{j\in J_i(t)\cap R} p_{ij}x_{ij}\le d_i \quad (i=1,\dots,m),\qquad x_{ij}\ge 0 .
--   $$
--
--   This definition is the set of feasible solutions of that program. With $R$ the set of all jobs it is exactly the program (LP) of Theorem 1 of Lenstra, Shmoys and Tardos; the procedure of Theorem 3 uses it with $R$ the jobs left over after the long assignments have been fixed.
--
--   **Formalization Note** A solution is a full real $m\times n$ matrix $x$. The paper's program has variables only for $i\in M_j(t)$, $j\in R$; here the remaining entries are required to be $0$ (both $x_{ij}=0$ whenever $p_{ij}>t$ and $x_{ij}=0$ whenever $j\notin R$). The feasible set is therefore the paper's polytope embedded by zero-padding, an affine isomorphism, so its extreme points (`Set.extremePoints`) are exactly the paper's vertices. Deadlines and threshold are real numbers.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 3, Section 2, Theorem 1, program (LP); p. 6, Section 3

import Mathlib

namespace UnrelatedSched.FixedMachines

/-- The feasible region of the linear program (LP) of the Rounding Theorem
(Lenstra–Shmoys–Tardos, CWI Report OS-R8714, §2, Theorem 1, p. 3), for the sub-instance consisting
of the jobs in `R`.

Machines are `Fin m`, jobs are `Fin n`, `P i j` is the processing time of job `j` on machine `i`,
`dl i` is the deadline `d_i` of machine `i` and `t` is the threshold. The paper's variables `x_ij`
exist only for `j ∈ J_i(t) = {j : p_ij ≤ t}`; here `x` is a full `m × n` real matrix and the
missing variables are pinned to `0` (`t < P i j → x i j = 0`). Jobs outside `R` are not part of
the sub-instance and their columns are pinned to `0` as well. The constraints are
* `∑_{i ∈ M_j(t)} x_ij = 1` for every job `j ∈ R`,
* `∑_{j ∈ J_i(t)} p_ij x_ij ≤ d_i` for every machine `i`,
* `x_ij ≥ 0`.
With `R = Set.univ` this is exactly (LP) of Theorem 1. -/
def DeadlineLP {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (R : Set (Fin n)) (dl : Fin m → ℝ)
    (t : ℝ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x | (∀ i j, 0 ≤ x i j) ∧
       (∀ i j, t < (P i j : ℝ) → x i j = 0) ∧
       (∀ i j, j ∉ R → x i j = 0) ∧
       (∀ j, j ∈ R → ∑ i, x i j = 1) ∧
       (∀ i, ∑ j, (P i j : ℝ) * x i j ≤ dl i)}

end UnrelatedSched.FixedMachines


