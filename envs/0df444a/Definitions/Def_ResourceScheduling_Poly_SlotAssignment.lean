-- Prove2me | Definitions.Def_ResourceScheduling_Poly_SlotAssignment
-- name    : ResourceScheduling_Poly_SlotAssignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:31:23.394626+00:00
-- url     : https://prove2.me/theorems/33d8902f-8323-496c-867f-46258c0c9d74
-- title:
--   Slot assignments and their bottleneck value (proof of Theorem 6)
-- statement:
--   In the proof of Theorem 6 (one resource of size $s_1$, requirements $r_{1j}\in\{0,1\}$, $m$ uniform machines with speeds $q_i$), jobs are assigned to **slots** $(i,k)$: machine $M_i$, $k$-th position, $i=1,\dots,m$, $k=1,\dots,n$. The arc from job $j$ to slot $(i,k)$ costs
--   $$c_{ijk}=\begin{cases}\infty & \text{if } i\ge s_1+1 \text{ and } r_{1j}=1,\\ k/q_i & \text{otherwise,}\end{cases}$$
--   and the variable $x_{ijk}$ is $1$ "if $J_j$ is executed on $M_i$ in the $k$th position" and $0$ otherwise, every job using exactly one slot and every slot at most one job.
--
--   A **slot assignment** here is a finite-cost such assignment: an injective map from jobs to slots in which each job with $r_{1j}=1$ goes to one of the machines $M_1,\dots,M_{s_1}$. Its **bottleneck value** is
--   $$\max_{i,j,k}\; c_{ijk}\,x_{ijk},$$
--   the largest $k/q_i$ over the slots used ($0$ when there are no jobs).
--
--   Theorem 6 states that the minimum makespan equals the minimum bottleneck value.
--
--   **Formalization Note** Machine and position indices are 0-based: a slot is a pair in `Fin m × Fin n`, and position `k` has cost $(k+1)/q_i$. Machine $M_i$ with $i\ge s_1+1$ (1-based) is index `i` with `s_1 ≤ i` (0-based). The page writes the LP relaxation $x_{ijk}\ge 0$ with the first constraint summed over $k=1,\dots,m$; this is the 0–1 assignment it describes, with the sum over $k=1,\dots,n$ (see the mission notes).
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 17–18, proof of Theorem 6

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model

/-!
# The bottleneck transportation problem of the proof of Theorem 6

Błażewicz, Lenstra & Rinnooy Kan, Discrete Appl. Math. 5 (1983), pp. 17–18, proof of Theorem 6.
Sources are the jobs `j`, sinks are the slots `(i, k)` (machine `M_i`, `k`-th position), the arc
cost is `c_{ijk} = ∞` if `i ≥ s_1 + 1` and `r_{1j} = 1`, and `k/q_i` otherwise; a 0–1 flow
assigns every job to exactly one slot and every slot to at most one job.
-/

namespace ResourceScheduling.Poly

variable (I : Instance)

/-- A slot assignment with finite cost: an injective map sending each job `J_j` to a slot
`(i, k)` (machine `M_i`, position `k + 1`, 0-based `k : Fin n`), such that a job with
`r_{1j} = 1` goes only to one of the machines `M_1, …, M_{s_1}` (0-based index `< s_1`); the
arcs with `c_{ijk} = ∞` are exactly those excluded. -/
def Instance.IsSlotAssignment (hl : I.l = 1) (x : Fin I.n → Fin I.m × Fin I.n) : Prop :=
  Function.Injective x ∧
    ∀ j, I.r ⟨0, by omega⟩ j = 1 → (x j).1.val < I.s ⟨0, by omega⟩

/-- The bottleneck value `max_{i,j,k} c_{ijk} x_{ijk}` of a slot assignment: the largest
`k / q_i` over the used slots (positions 1-based, so `(k + 1)/q_i` for `k : Fin n`), and `0`
when there are no jobs. -/
noncomputable def Instance.bottleneck (x : Fin I.n → Fin I.m × Fin I.n) : ℝ :=
  if h : (Finset.univ : Finset (Fin I.n)).Nonempty then
    Finset.univ.sup' h fun j => (((x j).2.val : ℝ) + 1) / I.q (x j).1
  else 0

end ResourceScheduling.Poly


