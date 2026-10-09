-- Prove2me | Definitions.Def_GreedWorks_OnlineTime_Model
-- name    : GreedWorks_OnlineTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:28.612151+00:00
-- url     : https://prove2.me/theorems/aa84e607-04c4-41b9-bcb9-a69c2b208f27
-- title:
--   §2, §2.1, §6, pp. 4–6, 12 — stochastic unrelated-machine instance with release dates, nonanticipatory policies, OPT's comparator class
-- statement:
--   **Instance.** There is a finite, nonempty set $M$ of unrelated parallel machines and a set of $n$ jobs $J=\{1,\dots,n\}$, indexed in order of release: job $j$ is released at the integer time $r_j\ge 0$, and $r_j\le r_k$ for $j<k$. Job $j$ has weight $w_j\ge 0$. A relation "eligible" says on which machines a job may run; on a forbidden pair the page writes $\mathbb E[P_{ij}]=\infty$. Every job has at least one eligible machine.
--
--   The processing time of job $j$ on machine $i$ is a random variable $P_{ij}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ with values in $\{0,1,2,\dots\}$. On eligible pairs it has a finite second moment and mean $\mathbb E[P_{ij}]\ge 1$. Processing times of different jobs are independent; the times of one job on different machines may be dependent. The **squared coefficient of variation** is
--   $$\mathbb{CV}[P_{ij}]^2=\frac{\operatorname{Var}[P_{ij}]}{\mathbb E[P_{ij}]^2},$$
--   and $\Delta\ge 0$ is an upper bound on $\mathbb{CV}[P_{ij}]^2$ over all eligible pairs.
--
--   **Policies.** A policy maps every realization $p=(p_{ij})$ of the processing times to a machine $\mathrm{mach}_j$ and a real start time $S_j$ for each job; the completion time is $C_j=S_j+p_{\mathrm{mach}_j,j}$. It is **feasible** if, for every realization, every job runs on an eligible machine, no job starts before its release date, and two jobs on the same machine occupy disjoint intervals $[S_j,C_j)$ (nonpreemptive processing, one job at a time per machine). It is **nonanticipatory** if its decisions up to any time $t$ depend only on what has been observed by $t$: whenever a second realization $p'$ agrees with $p$ on the realized length of every job completed by $t$, and leaves every job in process at $t$ unfinished at $t$, then the policy has started the same jobs by time $t$ under $p'$, at the same times and on the same machines.
--
--   A policy is **admissible** if it is feasible, nonanticipatory, and every completion time $C_j$ is integrable. Its expected cost is $\mathbb E\big[\sum_j w_jC_j\big]$. The benchmark $\mathsf{OPT}$ of the paper is the least expected cost of such a policy; it knows all jobs, release dates and distributions in advance, but not the realizations, and it may choose a job's machine at any time.
--
--   This is the model in which the paper's online algorithms are compared with an optimal nonanticipatory policy.
--
--   **Formalization Note** Jobs are `Fin n` in release order (`release_monotone`). Release dates are natural numbers: the time-indexed relaxation of §6.2 has integer slots $s\ge r_j$, and with a fractional release date its bound (13) fails (one job, $P\equiv 1$, $r=\tfrac12$: $\mathsf{OPT}=\tfrac32$ but every point of $(S_r)$ has value $2$). Added relative to the page: $w_j\ge 0$ (never written, used by every argument); $\Delta$ is any upper bound on the squared coefficients of variation (Definition 3 takes the maximum; every bound of the paper is increasing in $\Delta$). The page's assumption $\mathbb E[P_{ij}]\ge1$ (p. 6) and integer-valued processing times (p. 5) are standing assumptions of the paper. Comparators are characterized by an inequality "for every admissible policy" rather than an infimum, and must have integrable completion times; otherwise a Bochner integral of a non-integrable function would be $0$. Start times are real.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 4–6, §2 and §2.1 (model, Definitions 1–2), p. 7, Definition 3, p. 12, §6 (release dates)

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model

namespace GreedWorks.OnlineTime

open MeasureTheory ProbabilityTheory

/-- A stochastic unrelated-GreedWorks.OnlineList.machine instance with release dates (§2 and §6, pp. 4–6, 12).

* `M` is the finite, nonempty set of machines (`Nonempty` is a binder of every theorem);
  jobs are `Fin n`, indexed in release order (`release_monotone`, p. 12: "jobs are indexed
  such that `r_j ≤ r_k` for `j < k`").
* `release j : ℕ` is the release date `r_j`. Integer release dates are the paper's implicit
  discrete-time convention: the time-indexed relaxation has integer slots `s ≥ r_j` (p. 15).
* `P i j : Ω → ℕ` is the processing time of job `j` on GreedWorks.OnlineList.machine `i`: discrete, integer valued
  and nonnegative (p. 5).
* `eligible i j` is false exactly when the page writes `𝔼[P_ij] = ∞` (job `j` cannot run on
  GreedWorks.OnlineList.machine `i`); the law of `P i j` on such a pair is irrelevant. Every job has an eligible GreedWorks.OnlineList.machine.
* On eligible pairs `P i j` has a finite second moment and mean `𝔼[P_ij] ≥ 1` (p. 6, "by
  scaling").
* Processing times of different jobs are independent; the processing times of one job on
  different machines may be dependent (p. 2).
* `weight j ≥ 0` is the weight `w_j` (implicit on the page, used by every argument).
* `Delta ≥ 0` is an upper bound on every squared coefficient of variation
  `ℂ𝕍[P_ij]² = Var[P_ij] / 𝔼[P_ij]²` on eligible pairs (Definitions 1 and 3, pp. 5, 7). -/
structure StochasticInstance (M : Type*) [Fintype M] (n : ℕ)
    (Ω : Type*) [MeasurableSpace Ω] where
  Pr : Measure Ω
  probability : IsProbabilityMeasure Pr
  P : M → Fin n → Ω → ℕ
  measurable : ∀ i j, Measurable (P i j)
  eligible : M → Fin n → Prop
  hasMachine : ∀ j, ∃ i, eligible i j
  memLp : ∀ i j, eligible i j → MemLp (fun ω => (P i j ω : ℝ)) 2 Pr
  meanAtLeastOne : ∀ i j, eligible i j → 1 ≤ ∫ ω, (P i j ω : ℝ) ∂Pr
  independentJobs : iIndepFun (fun j ω => fun i => (P i j ω : ℝ)) Pr
  release : Fin n → ℕ
  release_monotone : Monotone release
  weight : Fin n → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  Delta : ℝ
  Delta_nonneg : 0 ≤ Delta
  cvBound : ∀ i j, eligible i j →
    variance (fun ω => (P i j ω : ℝ)) Pr ≤ Delta * (∫ ω, (P i j ω : ℝ) ∂Pr) ^ 2

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The mean processing time `𝔼[P_ij]` (the page's `p_ij := 𝔼[P_ij]` of §6). -/
noncomputable def mean (I : StochasticInstance M n Ω) (i : M) (j : Fin n) : ℝ :=
  ∫ ω, (I.P i j ω : ℝ) ∂I.Pr

/-- The squared coefficient of variation `ℂ𝕍[P_ij]² = Var[P_ij] / 𝔼[P_ij]²` (Definition 1). -/
noncomputable def cvSquared (I : StochasticInstance M n Ω) (i : M) (j : Fin n) : ℝ :=
  variance (fun ω => (I.P i j ω : ℝ)) I.Pr / (mean I i j) ^ 2

/-- The realization at the sample point `ω`. -/
def realize (I : StochasticInstance M n Ω) (ω : Ω) : GreedWorks.OnlineList.Realization M n :=
  fun i j => I.P i j ω

/-- Feasibility on every realization: each job runs on an eligible GreedWorks.OnlineList.machine, never before its
release date, and two distinct jobs on the same GreedWorks.OnlineList.machine occupy disjoint half-open intervals
`[S_j, C_j)` (a GreedWorks.OnlineList.machine processes at most one job at a time; a zero-length job occupies no
time). -/
def IsFeasible (I : StochasticInstance M n Ω) (pol : GreedWorks.OnlineList.Policy M n) : Prop :=
  ∀ p : GreedWorks.OnlineList.Realization M n,
    (∀ j, I.eligible (GreedWorks.OnlineList.machine pol p j) j) ∧
    (∀ j, (I.release j : ℝ) ≤ GreedWorks.OnlineList.start pol p j) ∧
    (∀ j k, j ≠ k → GreedWorks.OnlineList.machine pol p j = GreedWorks.OnlineList.machine pol p k →
      Disjoint (Set.Ico (GreedWorks.OnlineList.start pol p j) (GreedWorks.OnlineList.completion pol p j))
        (Set.Ico (GreedWorks.OnlineList.start pol p k) (GreedWorks.OnlineList.completion pol p k)))

/-- An admissible comparator (the class over which `OPT` is the optimum, §2.1, pp. 5–6): a
feasible, nonanticipatory policy, which knows all jobs, release dates and distributions in
advance, and whose GreedWorks.OnlineList.completion times are integrable (an infinite expected cost bounds nothing). -/
def IsAdmissible (I : StochasticInstance M n Ω) (pol : GreedWorks.OnlineList.Policy M n) : Prop :=
  IsFeasible I pol ∧ GreedWorks.OnlineList.IsNonanticipatory pol ∧
    ∀ j, Integrable (fun ω => GreedWorks.OnlineList.completion pol (realize I ω) j) I.Pr

/-- Expected total weighted GreedWorks.OnlineList.completion time `𝔼[Σ_j w_j C_j]` of a policy. -/
noncomputable def policyCost (I : StochasticInstance M n Ω) (pol : GreedWorks.OnlineList.Policy M n) : ℝ :=
  ∫ ω, ∑ j : Fin n, I.weight j * GreedWorks.OnlineList.completion pol (realize I ω) j ∂I.Pr

end GreedWorks.OnlineTime


