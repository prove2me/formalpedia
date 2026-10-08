-- Prove2me | Definitions.Def_TwoAgentSched_Shops_OpenShop
-- name    : TwoAgentSched_Shops_OpenShop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:03.730351+00:00
-- url     : https://prove2.me/theorems/5da86d46-461f-4f7d-ba92-97db370bc052
-- title:
--   Feasible schedules of the two-machine open shop
-- statement:
--   A **two-machine open shop** processes $n$ jobs on two machines $M_1$ and $M_2$. Job $i$ has one operation of length $A_i$ on $M_1$ and one of length $B_i$ on $M_2$; unlike in a flow shop, the two operations may be processed in either order. A schedule assigns to each job a start time $s_1(i)$ on $M_1$ and $s_2(i)$ on $M_2$. Processing is nonpreemptive, so job $i$ occupies $M_1$ during $[s_1(i), s_1(i)+A_i]$ and $M_2$ during $[s_2(i), s_2(i)+B_i]$.
--
--   The schedule is **feasible** when
--
--   1. no operation starts before time $0$: $s_1(i)\ge 0$ and $s_2(i)\ge 0$;
--   2. each machine processes at most one job at a time: for distinct jobs $i\neq j$,
--   $$s_h(i)+p_h(i)\le s_h(j)\quad\text{or}\quad s_h(j)+p_h(j)\le s_h(i)\qquad(h=1,2,\ p_1=A,\ p_2=B);$$
--   3. a job is processed by at most one machine at a time: for every job $i$,
--   $$s_1(i)+A_i\le s_2(i)\quad\text{or}\quad s_2(i)+B_i\le s_1(i).$$
--
--   This is the machine environment $O2$ of §10.2 of Agnetis, Mirchandani, Pacciarelli and Pacifici. It is stated for a single set of jobs, without agents, so it can be reused for any two-machine open shop problem.
--
--   **Formalization Note** Jobs are indexed by `Fin n`; start times are real numbers. Idle time is allowed.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 238–239, §10.2 (the open shop; "for the B-job only two cases are possible, i.e., visit first M_1 and then M_2 or vice versa")

import Mathlib

namespace TwoAgentSched.Shops

/-- A two-machine **open shop** schedule of `n` jobs (Agnetis, Mirchandani, Pacciarelli &
Pacifici 2004, §10.2, p. 238): job `i` has one operation of length `A i` on machine `M_1` and one
of length `B i` on machine `M_2`, which may be processed in either order. The schedule gives the
start time `s₁ i` of job `i` on `M_1` and `s₂ i` on `M_2`; processing is nonpreemptive, so job `i`
occupies `M_1` on `[s₁ i, s₁ i + A i]` and `M_2` on `[s₂ i, s₂ i + B i]`. It is feasible when:
no operation starts before time `0`; each machine processes at most one job at a time (the
intervals of two distinct jobs on the same machine do not overlap); and the two operations of a
job do not overlap in time (one of them ends before the other starts). -/
def IsOpenFeasible {n : ℕ} (A B : Fin n → ℝ) (s₁ s₂ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ s₁ i) ∧ (∀ i, 0 ≤ s₂ i) ∧
  (∀ i j, i ≠ j → s₁ i + A i ≤ s₁ j ∨ s₁ j + A j ≤ s₁ i) ∧
  (∀ i j, i ≠ j → s₂ i + B i ≤ s₂ j ∨ s₂ j + B j ≤ s₂ i) ∧
  (∀ i, s₁ i + A i ≤ s₂ i ∨ s₂ i + B i ≤ s₁ i)

end TwoAgentSched.Shops


