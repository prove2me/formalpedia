-- Prove2me | Definitions.Def_ScheduledQueue_Diffusion_Setting
-- name    : ScheduledQueue_Diffusion_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:26.092415+00:00
-- url     : https://prove2.me/theorems/22557994-e04e-47b9-9972-73502724911e
-- title:
--   pp. 2–3 — scheduled traffic with i.i.d. service times: arrivals, N(t), workload W(t), early/late counts 𝓔(t), 𝓛(t), and X(1) for reflected Brownian motion
-- statement:
--   This module fixes the model of Araman and Glynn (p. 2) for a single-server queue fed by scheduled traffic with general service times, together with the auxiliary counts used in the proof of Proposition 1 (p. 3).
--
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ and a slot length $h>0$.
--
--   1. **Scheduled input.** The perturbations $(\xi_j)_{j\in\mathbb Z}$ are i.i.d. real random variables with $\mathbb E|\xi_0|<\infty$, and the shift $U$ is uniform on $[0,1]$ and independent of the whole sequence $\xi=(\xi_j)_{j\in\mathbb Z}$.
--   2. **Service input.** The service times $V_1,V_2,\dots$ are i.i.d. with $\mathbb E V_1^2<\infty$, and the sequence $V$ is independent of the pair $(U,\xi)$.
--   3. **Arrivals.** Customer $j\in\mathbb Z$ is scheduled at $jh$ and, after the time origin is shifted by $hU$, arrives at
--   $$
--   A_j = jh + hU + \xi_j .
--   $$
--   4. **Counting function.** For $t\ge 0$, $N(t)=\#\{j\in\mathbb Z : A_j\in(0,t]\}$, so $N(0)=0$.
--   5. **Workload.** With customers numbered $1,2,\dots$ in order of arrival after time $0$ and a unit-rate server that is empty at time $0$,
--   $$
--   W(t)=\sup_{0\le s\le t}\Big(\sum_{i=N(s)+1}^{N(t)} V_i-(t-s)\Big).
--   $$
--   6. **Early and late customers.** $\mathcal E(t)=\#\{i : ih+Uh>t,\ ih+Uh+\xi_i\le t\}$ counts customers scheduled after $t$ who have already arrived by $t$, and $\mathcal L(t)=\#\{i : ih+Uh<t,\ ih+Uh+\xi_i\ge t\}$ counts customers scheduled before $t$ who have not yet arrived; both take values in $\{0,1,2,\dots\}\cup\{\infty\}$.
--   7. **Scheduled count and increments.** $\#\{i : ih+Uh\in(0,t]\}$ is the number of scheduled times in $(0,t]$, and $N(a,b]=\#\{j : A_j\in(a,b]\}\in\{0,1,\dots\}\cup\{\infty\}$ the number of arrivals in $(a,b]$.
--   8. **Reflected Brownian motion at time 1.** For a real process $B=(B(u))_{u\ge 0}$,
--   $$
--   X(1)=B(1)-\inf_{0\le u\le 1}B(u).
--   $$
--   When $B$ is a standard Brownian motion, $X(t)=B(t)-\inf_{0\le u\le t}B(u)$ is reflected Brownian motion with mean $0$, unit volatility and $X(0)=0$.
--
--   These objects are the vocabulary of Proposition 1 and Corollary 1: the heavy-traffic limit concerns $W(t)$, and its proof controls $N(t)$ through $\mathcal E$ and $\mathcal L$.
--
--   **Formalization Note** The page writes $W(t)=\max_{0\le s\le t}\sum_{i=N(s)}^{N(t)}V_i-(t-s)$, whose index range includes customer $N(s)$ and gives $W(0)\neq 0$, contradicting "the work-in-system at $t=0$ is zero"; the module uses the range $N(s)+1,\dots,N(t)$ (the reflection form), which has $W(0)=0$. The page defines $N$ through increments over closed intervals $[a,b]$; the module counts arrivals in $(0,t]$, which agrees almost surely at every fixed time. $N(t)$ and the scheduled count are cardinalities in $\mathbb N$ (Lean's `ncard`, which is $0$ on an infinite set; the arrival set is almost surely finite under $\mathbb E|\xi_0|<\infty$), while $\mathcal E$, $\mathcal L$ and $N(a,b]$ are extended cardinalities (`encard`), so that their finiteness is a genuine statement. The service times are indexed by $\mathbb N$ and $V_0$ is never used. The suprema are real suprema over $[0,t]$ and $[0,1]$; on the full-measure event where the counts are finite and the Brownian path is continuous they are suprema of bounded families. The sequence $V$ is independent of $(U,\xi)$ jointly, as one random element. The objects of items 1–4 repeat those of the companion mission on Theorem 1 of the same paper, under a separate namespace.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 2, §1 (model, workload, (1.1)) and p. 3, proof of Proposition 1 (definition of 𝓔 and 𝓛); p. 4, Corollary 1 (reflected Brownian motion)

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Service times (p. 2): `V₁, V₂, …` are i.i.d. with finite variance and the sequence `V` is
independent of the pair `(U, ξ)`. Customers are numbered `1, 2, …` in order of arrival after
time `0`; `V 0` is never used. -/
structure ServiceInput (P : Measure Ω) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (V : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (V i)
  indep : iIndepFun V P
  identDistrib : ∀ i, IdentDistrib (V i) (V 1) P P
  memLp : MemLp (V 1) 2 P
  indep_input : IndepFun (fun ω i => V i ω) (fun ω => (U ω, fun j => ξ j ω)) P

/-- Workload of the queue with service times `V`, empty at time `0`:
`W(t) = sup_{0 ≤ s ≤ t} (∑_{i = N(s)+1}^{N(t)} V_i − (t − s))`. -/
noncomputable def workload (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (V : ℕ → Ω → ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  ⨆ s : Icc 0 t, ((∑ i ∈ Finset.Ioc (ScheduledQueue.Stability.count h ξ U s ω) (ScheduledQueue.Stability.count h ξ U t ω), V i ω) - (t - s))

/-- `𝓔(t)`: the number of customers scheduled after `t` (`ih + Uh > t`) who arrive by `t`
(`ih + Uh + ξ_i ≤ t`), in `ℕ∞`. -/
noncomputable def early (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ∞ :=
  {i : ℤ | t < i * h + U ω * h ∧ i * h + U ω * h + ξ i ω ≤ t}.encard

/-- `𝓛(t)`: the number of customers scheduled before `t` (`ih + Uh < t`) who arrive at or
after `t` (`ih + Uh + ξ_i ≥ t`), in `ℕ∞`. -/
noncomputable def late (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ∞ :=
  {i : ℤ | i * h + U ω * h < t ∧ t ≤ i * h + U ω * h + ξ i ω}.encard

/-- The number of scheduled times `ih + Uh` in `(0, t]`. -/
noncomputable def scheduled (h : ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {i : ℤ | i * h + U ω * h ∈ Ioc 0 t}.ncard

/-- The number of arrivals in `(a, b]`, in `ℕ∞`. -/
noncomputable def arrivalsIn (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (a b : ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc a b}.encard

/-- `X(1)` for the reflected Brownian motion `X(t) = B(t) − inf_{0 ≤ u ≤ t} B(u)` driven by a
process `B` indexed by `ℝ≥0`. -/
noncomputable def reflectedAtOne {Ω' : Type*} (B : ℝ≥0 → Ω' → ℝ) (ω' : Ω') : ℝ :=
  B 1 ω' - ⨅ u : Icc (0 : ℝ≥0) 1, B u ω'

end ScheduledQueue.Diffusion


