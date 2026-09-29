-- Prove2me | Definitions.Def_ResourceScheduling_Poly_Q2Algorithm
-- name    : ResourceScheduling_Poly_Q2Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:30:16.943471+00:00
-- url     : https://prove2.me/theorems/c47085f1-a5c5-404e-a295-2a02ce3cfd1f
-- title:
--   The algorithm of Theorem 5 for Q2 | res1··, p_j = 1 | C_max
-- statement:
--   The algorithm of the proof of Theorem 5, for two uniform machines $M_1,M_2$ with speeds $q_1\ge q_2$, one resource $R_1$ of size $s_1$, and unit-time jobs with requirements $r_{1j}$ (p. 16):
--
--   > "Given any instance of Q2 | res1··, p_j = 1 | C_max, an optimal schedule can be obtained in the following way. Suppose that $q_1 \ge q_2$. First, schedule all jobs on $M_1$ in order of nonincreasing resource requirement. Next, successively remove the last job from $M_1$ and schedule it as early as possible on $M_2$, as long as this reduces the value of $C_{\max}$."
--
--   Precisely, fix an order $\pi(0),\pi(1),\dots,\pi(n-1)$ of the jobs (the theorems assume it is nonincreasing in $r_{1j}$; ties are arbitrary). Initially the job in position $p$ runs on $M_1$ during $[p/q_1,(p+1)/q_1)$. The $i$-th move ($i=0,1,\dots$) takes the job $\pi(n-1-i)$, the last job then on $M_1$, and starts it on $M_2$ at the earliest time
--   $$t_i=\min\{\,t\ge e_i : r_{1\pi(n-1-i)}+u_i(\tau)\le s_1 \text{ for all } \tau\in[t,t+1/q_2)\,\},$$
--   where $e_i$ is the completion time of the last job on $M_2$ ($e_0=0$, $e_{i+1}=t_i+1/q_2$) and $u_i(\tau)$ is the requirement of the job executed on $M_1$ at time $\tau$ among the jobs $\pi(0),\dots,\pi(n-2-i)$ still there ($0$ if none). Let $S_k$ be the schedule after $k$ moves. The algorithm returns $S_k$ for the least $k$ such that $k=n$ ($M_1$ is empty) or $C_{\max}(S_{k+1})\ge C_{\max}(S_k)$ (the move does not reduce $C_{\max}$ and is undone).
--
--   The minimum defining $t_i$ exists whenever $r_{1\pi(n-1-i)}\le s_1$: the set is nonempty (it contains $\max(e_i,(n-1-i)/q_1)$), bounded below by $e_i$, and closed because $u_i$ is a step function on half-open intervals. Jobs already on $M_2$ complete by $e_i\le t$, so they never run together with the moved job.
--
--   **Formalization Note** The earliest start $t_i$ is written as `sInf` of the set above; the remark in the previous paragraph is why this infimum is a minimum under the hypotheses of the theorems. The job order is an explicit argument `ord : Fin n ≃ Fin n`, `ord p` being the job in position `p` (0-based). The running time $O(n\log n)$ claimed in Theorem 5 is not formalized.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 5 ("an optimal schedule can be obtained in the following way")

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties

/-!
# The algorithm of Theorem 5 for `Q2 | res1··, p_j = 1 | C_max`

Błażewicz, Lenstra & Rinnooy Kan, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 5:
"Suppose that q_1 ≥ q_2. First, schedule all jobs on M_1 in order of nonincreasing resource
requirement. Next, successively remove the last job from M_1 and schedule it as early as possible
on M_2, as long as this reduces the value of C_max."

The order of the jobs is an argument `ord : Fin n ≃ Fin n` (`ord p` is the job in position `p`,
0-based); the theorems assume it is nonincreasing in `r_{1j}`, ties broken arbitrarily.
-/

namespace ResourceScheduling.Poly

namespace Q2Algorithm

variable (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)

/-- Job `J_j`, started on `M_2` at time `t`, satisfies the resource constraint throughout its
execution `[t, t + 1/q_2)` against the jobs in positions `0, …, c-1` of the initial `M_1`
sequence, which occupy `[p/q_1, (p+1)/q_1)` on `M_1`. (Jobs already on `M_2` complete by the
time `t` considered in `moveStart`, so they are never executed simultaneously with `J_j`.) -/
def FitsOnM₂ (c : ℕ) (j : Fin I.n) (t : ℝ) : Prop :=
  ∀ u : ℝ, t ≤ u → u < t + 1 / I.q (I.M₂ hm) →
    I.r (I.R₁ hl) j +
      (∑ p ∈ Finset.univ.filter (fun p : Fin I.n =>
          p.val < c ∧ (p.val : ℝ) / I.q (I.M₁ hm) ≤ u ∧ u < ((p.val : ℝ) + 1) / I.q (I.M₁ hm)),
        I.r (I.R₁ hl) (ord p)) ≤ I.s (I.R₁ hl)

/-- "As early as possible on `M_2`": the earliest time `t ≥ e` (with `e` the completion time of
the last job currently on `M_2`, or `0`) at which `J_j` fits on `M_2` against the `c` jobs then
on `M_1`. The set is nonempty (`t = max e (c/q_1)` fits when `r_{1j} ≤ s_1`), bounded below by
`e`, and, the `M_1` usage being a step function on half-open intervals, its infimum is attained. -/
noncomputable def moveStart (e : ℝ) (c : ℕ) (j : Fin I.n) : ℝ :=
  sInf {t : ℝ | e ≤ t ∧ FitsOnM₂ I hm hl ord c j t}

/-- The completion time of the last job on `M_2` after `i` moves (`0` when `i = 0`). The `i`-th
move (0-based) takes the job in position `n - 1 - i`, which is then the last job on `M_1`, whose
other jobs are in positions `0, …, n - 2 - i`. -/
noncomputable def m2End : ℕ → ℝ
  | 0 => 0
  | i + 1 =>
    if h : i < I.n then
      moveStart I hm hl ord (m2End i) (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)
        + 1 / I.q (I.M₂ hm)
    else m2End i

/-- The start time on `M_2` of the job moved at the `i`-th move (0-based, `i < n`). -/
noncomputable def movedStart (i : ℕ) (h : i < I.n) : ℝ :=
  moveStart I hm hl ord (m2End I hm hl ord i) (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)

/-- The schedule after `k` moves (`k ≤ n`): the job in position `p < n - k` runs on `M_1` in
`[p/q_1, (p+1)/q_1)`; the job in position `p ≥ n - k`, moved at move `n - 1 - p`, runs on `M_2`
from `movedStart (n - 1 - p)`. -/
noncomputable def afterMoves (k : ℕ) : Schedule I where
  machine j := if (ord.symm j).val + k < I.n then I.M₁ hm else I.M₂ hm
  start j :=
    if (ord.symm j).val + k < I.n then ((ord.symm j).val : ℝ) / I.q (I.M₁ hm)
    else movedStart I hm hl ord (I.n - 1 - (ord.symm j).val) (by have := (ord.symm j).isLt; omega)

/-- The number of moves the algorithm keeps: the least `k` such that `M_1` is empty after `k`
moves (`k ≥ n`) or the `(k+1)`-st move does not reduce `C_max`; that move is undone. -/
noncomputable def stopIndex : ℕ := by
  classical
  exact Nat.find (⟨I.n, Or.inl le_rfl⟩ : ∃ k : ℕ, I.n ≤ k ∨
    ¬ ((afterMoves I hm hl ord (k + 1)).makespan < (afterMoves I hm hl ord k).makespan))

end Q2Algorithm

/-- The schedule produced by the algorithm of Theorem 5 from the job order `ord`. -/
noncomputable def q2Algorithm (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (ord : Fin I.n ≃ Fin I.n) : Schedule I :=
  Q2Algorithm.afterMoves I hm hl ord (Q2Algorithm.stopIndex I hm hl ord)

end ResourceScheduling.Poly


