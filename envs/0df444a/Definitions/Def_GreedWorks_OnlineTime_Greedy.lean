-- Prove2me | Definitions.Def_GreedWorks_OnlineTime_Greedy
-- name    : GreedWorks_OnlineTime_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:55.950007+00:00
-- url     : https://prove2.me/theorems/13f2cf79-b419-45f0-8f50-4e4427add703
-- title:
--   §6.1, pp. 12–14 — online-time greedy algorithm (modified release dates, cost(j → i), WSPT), Definition 4, the dual-fitting values α, β, (12)
-- statement:
--   Consider deterministic processing times $p_{ij}\ge1$ on eligible pairs, integer release dates $r_j$ (jobs indexed in release order), weights $w_j$, and a parameter $c>0$. The **online-time greedy algorithm** handles the jobs as follows.
--
--   1. The **modified release date** of job $j$ on machine $i$ is $r_{ij}=\max\{r_j,\;c\,p_{ij}\}$.
--   2. $U_i(r_j)$ is the set of jobs assigned to machine $i$ before job $j$ (earlier index) that have not started before time $r_j$.
--   3. (Definition 4) For each machine $i$,
--   $$\operatorname{cost}(j\to i)=w_j\Big(\big(1+\tfrac1c\big)r_{ij}+p_{ij}+\sum_{\substack{k\in U_i(r_j)\\ w_k/p_{ik}\ \ge\ w_j/p_{ij}}}p_{ik}\Big)+\sum_{\substack{k\in U_i(r_j)\\ w_k/p_{ik}\ <\ w_j/p_{ij}}}w_k\,p_{ij}.$$
--   4. Job $j$ is assigned, at time $r_j$, to an eligible machine $m(j)$ minimizing $\operatorname{cost}(j\to i)$, ties broken arbitrarily.
--   5. Each machine runs the greedy **WSPT** rule with modified release dates: whenever machine $i$ is idle at time $t$ and some job $k$ assigned to it with $r_{ik}\le t$ has not started, it starts such a job with maximal ratio $w_k/p_{ik}$.
--
--   An outcome is an assignment $m$ together with start times $s_j$; $C_j=s_j+p_{m(j)j}$ and $\mathsf{ALG}=\sum_jw_jC_j$. For the dual fitting of Theorem 3 the paper defines $\alpha_j=\operatorname{cost}(j\to m(j))$ and, for a time $t$,
--   $$\beta_{i,t}=\sum_{k:\ m(k)=i,\ r_k\le t,\ C_k\ge t}w_k ,$$
--   and for a speed $f$ the values (12): $\alpha^f_j=\alpha_j/f$ and $\beta^f_{is}=\beta_{i,f\cdot s}$.
--
--   The algorithm is the paper's deterministic online-time policy; run on the means $p_{ij}=\mathbb E[P_{ij}]$ it produces the nominal schedule of the stochastic policy.
--
--   **Formalization Note** The algorithm is encoded as a predicate on an outcome $(m,s)$: assignment by minimal cost over eligible machines; no start before $r_{m(j)j}$; disjoint processing intervals on each machine; no idle time while an assigned, available job waits; and the WSPT priority among available jobs at every start. Every tie-breaking is allowed. Conventions: jobs with equal release dates are assigned in index order, and a job that starts exactly at $r_j$ counts as not yet started in $U_i(r_j)$ (arrivals at time $t$ are processed before the start decisions at $t$). The time argument of $\beta$ is real, because the speed $f$ need not be an integer.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 12–13, §6.1, Greedy Algorithm (Online Time Model for Deterministic Processing Times), Definition 4; p. 14, proof of Theorem 3 (α, β) and (12)

import Mathlib

namespace GreedWorks.OnlineTime

open Classical

/-! # The online-time greedy algorithm for deterministic processing times (§6.1, pp. 12–14)

Deterministic data: eligibility `elig`, integer release dates `r` (jobs `Fin n` in release
order), processing times `p i j` (in §6.3 these are the means `𝔼[P_ij]`), weights `w`, and
the parameter `c > 0` of the modified release dates. An outcome of the algorithm is an
assignment `m : Fin n → M` together with GreedWorks.OnlineList.start times `s : Fin n → ℝ` (the "nominal" schedule). -/

variable {M : Type*} [Fintype M] {n : ℕ}

/-- Step 1: the modified release date `r_ij := max{r_j, c · p_ij}`. -/
noncomputable def modRelease (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (i : M) (j : Fin n) :
    ℝ :=
  max (r j : ℝ) (c * p i j)

/-- Step 2: `U_i(r_j)`, the jobs assigned to GreedWorks.OnlineList.machine `i` before job `j` (smaller index; equal
release dates are processed in index order) that have not started before time `r_j`. A job
starting exactly at `r_j` counts as not yet started: arrivals at time `t` are processed before
the GreedWorks.OnlineList.start decisions at `t`. Job `j` itself is excluded. -/
noncomputable def waiting (r : Fin n → ℕ) (m : Fin n → M) (s : Fin n → ℝ) (i : M) (j : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun k => k < j ∧ m k = i ∧ (r j : ℝ) ≤ s k)

/-- Definition 4 (p. 13):
`cost(j → i) = w_j ((1 + 1/c) r_ij + p_ij + Σ_{k ∈ U_i(r_j), w_k/p_ik ≥ w_j/p_ij} p_ik)
  + Σ_{k ∈ U_i(r_j), w_k/p_ik < w_j/p_ij} w_k p_ij`. -/
noncomputable def cost (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (j : Fin n) (i : M) : ℝ :=
  w j * ((1 + 1 / c) * modRelease c r p i j + p i j +
      ∑ k ∈ (waiting r m s i j).filter (fun k => w j / p i j ≤ w k / p i k), p i k) +
    ∑ k ∈ (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j), w k * p i j

/-- `(m, s)` is an outcome of the online-time greedy algorithm (pp. 12–13), with arbitrary
tie-breaking:

* (assign, step 4) every job goes to an eligible GreedWorks.OnlineList.machine `m j` minimizing `cost(j → i)` over
  the eligible machines `i`;
* (release, step 5) no job starts before its modified release date `r_{m(j) j}`;
* (GreedWorks.OnlineList.machine) jobs on one GreedWorks.OnlineList.machine occupy disjoint intervals `[s_k, s_k + p_{m(k) k})`;
* (nondelay, step 5) a GreedWorks.OnlineList.machine is never idle at a time `t` while a job assigned to it is
  available (`r_ik ≤ t`) and not yet started (`t < s_k`);
* (priority, step 5, WSPT) when job `j` starts on a GreedWorks.OnlineList.machine, every job `k` on that GreedWorks.OnlineList.machine
  that is available and starts later has ratio `w_k/p_ik ≤ w_j/p_ij`. -/
def IsGreedy (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (elig : M → Fin n → Prop) (m : Fin n → M) (s : Fin n → ℝ) : Prop :=
  (∀ j, elig (m j) j ∧ ∀ i, elig i j → cost c r p w m s j (m j) ≤ cost c r p w m s j i) ∧
  (∀ k, modRelease c r p (m k) k ≤ s k) ∧
  (∀ j k, j ≠ k → m j = m k →
    Disjoint (Set.Ico (s j) (s j + p (m j) j)) (Set.Ico (s k) (s k + p (m k) k))) ∧
  (∀ (k : Fin n) (t : ℝ), modRelease c r p (m k) k ≤ t → t < s k →
    ∃ l, m l = m k ∧ s l ≤ t ∧ t < s l + p (m l) l) ∧
  (∀ j k, m k = m j → modRelease c r p (m k) k ≤ s j → s j < s k →
    w k / p (m k) k ≤ w j / p (m j) j)

/-- Completion time `C_j = s_j + p_{m(j) j}` in the deterministic (nominal) schedule. -/
noncomputable def nominalCompletion (p : M → Fin n → ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (j : Fin n) : ℝ :=
  s j + p (m j) j

/-- The objective value `ALG = Σ_j w_j C_j` of the deterministic schedule (`ALG_P` in the
proof of Theorem 4 when `p` are the means). -/
noncomputable def nominalValue (p : M → Fin n → ℝ) (w : Fin n → ℝ) (m : Fin n → M)
    (s : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, w j * nominalCompletion p m s j

/-- Proof of Theorem 3 (p. 14): `α_j := cost(j → m(j))`. -/
noncomputable def dualAlpha (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (j : Fin n) : ℝ :=
  cost c r p w m s j (m j)

/-- Proof of Theorem 3 (p. 14): `β_{i,t} := Σ_{k : m(k) = i, r_k ≤ t, C_k ≥ t} w_k`, at a real
time `t`. -/
noncomputable def dualBeta (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (i : M) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter
      (fun k => m k = i ∧ (r k : ℝ) ≤ t ∧ t ≤ nominalCompletion p m s k), w k

/-- (12), p. 14: `α^f_j = α_j / f`. -/
noncomputable def alphaF (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (f : ℝ) (j : Fin n) : ℝ :=
  dualAlpha c r p w m s j / f

/-- (12), p. 14: `β^f_{is} = β_{i, f·s}` for integer slots `s`. -/
noncomputable def betaF (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (f : ℝ) (i : M) (t : ℕ) : ℝ :=
  dualBeta r p w m s i (f * t)

end GreedWorks.OnlineTime


