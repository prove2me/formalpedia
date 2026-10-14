-- Prove2me | Definitions.Def_ScheduledQueue_Stability_Setting
-- name    : ScheduledQueue_Stability_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:39.875573+00:00
-- url     : https://prove2.me/theorems/84bc82ad-854c-40e1-a222-86bafe45106c
-- title:
--   p. 2 — scheduled traffic: i.i.d. perturbations, uniform shift, arrival count N(t), S/D/1 workload
-- statement:
--   **Scheduled traffic.** Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ and a scheduling interval $h>0$. Customer $j\in\mathbb Z$ is scheduled to arrive at time $jh$, but arrives with a random **perturbation** $\xi_j$. To make the arrival process time-stationary, the time origin is shifted by $hU$. The standing assumptions are:
--
--   1. the perturbations $(\xi_j)_{j\in\mathbb Z}$ are measurable, independent and identically distributed, with $\mathbb E|\xi_0|<\infty$;
--   2. $U$ is uniformly distributed on $[0,1]$ and independent of the whole sequence $\xi=(\xi_j)_{j\in\mathbb Z}$.
--
--   The actual arrival time of customer $j$ is
--   $$A_j = jh + hU + \xi_j ,$$
--   and for $t\ge 0$ the **arrival count** is $N(t)=\#\{j\in\mathbb Z : A_j\in(0,t]\}$, so that $N(0)=0$.
--
--   **The S/D/1 workload.** Every customer brings exactly $h$ units of work to a single server that works at unit rate, and the system is empty at time $0$. The workload at time $t\ge0$ is
--   $$W(t)=\sup_{0\le s\le t}\Big(h\,\big(N(t)-N(s)\big)-(t-s)\Big).$$
--
--   These are the objects on which both main results of Araman and Glynn are stated. The input model and the arrival count are shared by Theorem 1 (under critical loading with deterministic service times $h$, the workload converges in distribution to a finite limit exactly when the perturbations are bounded above) and by Corollary 1 (with general i.i.d. finite-variance service times of mean $h$, $t^{-1/2}W(t)$ converges to a multiple of reflected Brownian motion at time $1$); the workload defined here is the deterministic-service workload of Theorem 1.
--
--   **Formalization Note.** The four objects are `ScheduledInput P ξ U` (a bundle of the standing assumptions: `iIndepFun`, `IdentDistrib` to `ξ 0`, `Integrable (ξ 0)`, `HasLaw U (volume.restrict (Icc 0 1))`, and independence of `U` from the whole sequence `fun ω j => ξ j ω`), `arrival`, `count` and `workload`. Three conventions differ from the printed page and are deliberate. (i) The paper writes $N(b)-N(a)=\sum_j I(A_j\in[a,b])$ with closed intervals, which is not additive; the half-open $(0,t]$ count agrees with it almost surely at every fixed time. (ii) The printed workload $\max_{0\le s\le t}\sum_{i=N(s)}^{N(t)}V_i-(t-s)$ includes customer $N(s)$ and would give $W(0)=h\neq0$, contradicting "the work-in-system at $t=0$ is zero"; the formula here sums over customers $N(s)+1,\dots,N(t)$, i.e. it is the printed one minus $h$, and has $W(0)=0$. (iii) Service times are the constant $h$ ("$V_1=h$ a.s."); changing them on a null event changes no law. `count` uses `Set.ncard`, which returns $0$ on an infinite set, and `workload` is a real supremum, which returns $0$ on an unbounded family; both junk values can only occur on a null event, because the expected number of arrivals in $(0,t]$ is $t/h$, so only finitely many arrivals fall in any bounded interval almost surely, and then the family is bounded above by $h\,N(t)$. The half-open count is only used at times $t\ge0$; for $t<0$ it is $0$, which is not the page's $N(t)$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, pp. 1–2, §1 ("We assume throughout this paper…", the displays for N(b) − N(a) and W(t)); p. 5, Theorem 1 (V₁ = h, W(0) = 0)

import Mathlib

namespace ScheduledQueue.Stability

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Standing assumptions of p. 2: the perturbations `(ξ_j)_{j ∈ ℤ}` are i.i.d. with `E|ξ₀| < ∞`,
and the time shift `U` is uniform on `[0, 1]` and independent of the whole sequence `ξ`. -/
structure ScheduledInput (P : Measure Ω) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) : Prop where
  measurable : ∀ j, Measurable (ξ j)
  indep : iIndepFun ξ P
  identDistrib : ∀ j, IdentDistrib (ξ j) (ξ 0) P P
  integrable : Integrable (ξ 0) P
  uniform : HasLaw U (volume.restrict (Icc (0 : ℝ) 1)) P
  indep_shift : IndepFun U (fun ω j => ξ j ω) P

/-- Actual arrival time of customer `j` (scheduled at `jh`, time origin shifted by `hU`):
`jh + hU + ξ_j`. -/
def arrival (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (j : ℤ) (ω : Ω) : ℝ :=
  j * h + h * U ω + ξ j ω

/-- `N(t)` for `t ≥ 0`: the number of arrivals in `(0, t]`, so that `N(0) = 0`. -/
noncomputable def count (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {j : ℤ | arrival h ξ U j ω ∈ Ioc 0 t}.ncard

/-- Workload of the S/D/1 queue (every service time equals `h`, unit-rate server), empty at
time `0`: `W(t) = sup_{0 ≤ s ≤ t} (h (N(t) − N(s)) − (t − s))`. -/
noncomputable def workload (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ⨆ s : Icc 0 t, (h * ((count h ξ U t ω : ℝ) - count h ξ U s ω) - (t - s))

end ScheduledQueue.Stability


