-- Prove2me | Definitions.Def_DeterioratingJobs_Makespan_Model
-- name    : DeterioratingJobs_Makespan_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:55:09.092058+00:00
-- url     : https://prove2.me/theorems/c50b59bb-b2e7-439c-be69-57f1e234d6f2
-- title:
--   Section 1 — linearly deteriorating jobs: actual processing times $Y_i(t)=X_i+\alpha_i t$, completion times $S_k(\pi)$, makespan and expected makespan
-- statement:
--   This file sets up the linear deterioration model of §1 of Browne and Yechiali.
--
--   $N$ jobs are all available for processing at time $0$ on a single processor. Job $i$ has an **initial processing requirement** $X_i$, a random variable on a probability space $(\Omega,\mathcal F,P)$: the time needed to complete job $i$ if it is processed first. If the processing of job $i$ is delayed until time $t$, its requirement grows linearly with the delay to
--
--   $$
--   Y_i(t) = X_i + \alpha_i t,
--   $$
--
--   where $\alpha_i$ is the job's (deterministic) **growth rate**; a job stops deteriorating as soon as it is put on the processor.
--
--   Only nonpreemptive strategies without idling are considered, so a **policy** is a permutation $\pi$ of $\{1,\dots,N\}$, with $\pi(i)=j$ meaning that job $j$ is the $i$-th one processed. The **completion time** $S_k(\pi)$ of the $k$-th processed job is defined by the model itself: $S_0(\pi)=0$, and the job in position $k$ starts at $S_{k-1}(\pi)$ and takes its actual processing time $Y_{\pi(k)}(S_{k-1}(\pi))$, so
--
--   $$
--   S_k(\pi) = S_{k-1}(\pi) + X_{\pi(k)} + \alpha_{\pi(k)}\, S_{k-1}(\pi), \qquad k=1,\dots,N.
--   $$
--
--   The **makespan** is $S_N(\pi)$, the completion time of the last job, and the **expected makespan** is $\mathrm E\, S_N(\pi)=\int_\Omega S_N(\pi)\,dP$.
--
--   These are the objects of the paper's §1; its closed form (2) and its expected-makespan index rule are stated about them.
--
--   **Formalization Note** Jobs are `Fin N` with 0-based positions: `π k` is the job in position `k` (the paper's $\pi(k+1)$), and `completionTime X α π k ω` is $S_k(\pi)$ at the outcome $\omega$. The completion time is indexed by `ℕ`; for $k\ge N$ there is no further job and the value stays at $S_N$. The definition is the recursion of the model, not the closed form (2). No sign condition on $X$ or $\alpha$ and no measurability is built into the definitions; theorems state the hypotheses they need. The expected makespan is the Bochner integral, which is $0$ for a non-integrable makespan, so every theorem about it assumes the $X_i$ integrable.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), pp. 495–496, Section 1 (Y_i(t) = X_i + α_i t; S_k = Σ_1^k Y_i, S_0 = 0, Y_j = X_j + α_j S_{j−1}); the class Π, p. 495

import Mathlib

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Linear deterioration (Browne–Yechiali 1990, p. 495): if job `j` is started at time `t`, its
actual processing time is `Y_j(t) = X_j + α_j t`, where `X_j` is its initial processing requirement
and `α_j` its growth rate. The job stops deteriorating once it is put on the processor. -/
def actualProcessingTime {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (j : Fin N) (t : ℝ) (ω : Ω) : ℝ :=
  X j ω + α j * t

/-- Completion times under the nonpreemptive, non-idling schedule `π` (Browne–Yechiali 1990,
pp. 495–496). `π k` is the job processed in position `k` (0-based: the paper's `π(k+1)`).
`completionTime X α π k ω` is the completion time `S_k` of the `k`-th processed job, defined by the
model recursion `S_0 = 0`, `S_{k+1} = S_k + Y_{π(k)}(S_k)`: the job in position `k` starts at `S_k`
and takes `X_{π(k)} + α_{π(k)} S_k`. For `k ≥ N` there is no further job and `S` stays constant. -/
def completionTime {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω =>
      if h : k < N then
        completionTime X α π k ω +
          actualProcessingTime X α (π ⟨k, h⟩) (completionTime X α π k ω) ω
      else completionTime X α π k ω

/-- The makespan `S_N(π)`: the completion time of the last of the `N` jobs under `π`. -/
def makespan {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) : ℝ :=
  completionTime X α π N ω

/-- The expected makespan `E S_N(π)` under the probability measure `P`. -/
noncomputable def expectedMakespan {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) : ℝ :=
  ∫ ω, makespan X α π ω ∂P

end DeterioratingJobs.Makespan


