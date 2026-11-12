-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Scheduling
-- name    : FasterWCTFPTAS_Main_Scheduling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:05:58.153384+00:00
-- url     : https://prove2.me/theorems/1a51b7f4-1bb7-4136-8475-c643393ddd6b
-- title:
--   Weighted completion time on identical machines, Smith's order, and prefix quantities
-- statement:
--   There are $m$ identical machines and $n$ jobs; job $j$ has processing time $p_j>0$ and weight $w_j\ge0$. A nonpreemptive **schedule** assigns every job to a machine, $\sigma(j)\in\{0,\dots,m-1\}$, and orders the jobs of every machine; every machine processes its jobs back to back from time $0$. Every family of per-machine orders is induced by one priority permutation $\rho$ of the jobs, so the completion time of job $j$ is
--
--   $$
--   C_j(\sigma,\rho)=\sum_{i:\ \sigma(i)=\sigma(j),\ \rho(i)\le\rho(j)}p_i,\qquad \mathrm{cost}(\sigma,\rho)=\sum_{j}w_jC_j(\sigma,\rho),
--   $$
--
--   and $\mathrm{OPT}$ is the minimum of $\mathrm{cost}$ over all $(\sigma,\rho)$. **Smith's order** processes the jobs of each machine in non-increasing order of $w_j/p_j$, ties broken by index; $\mathrm{smithCost}(\sigma)$ is the cost of $\sigma$ under this order. The instance is **sorted** when $w_1/p_1\ge\dots\ge w_n/p_n$.
--
--   For §4: for a job set $J$, $\mathrm{cost}_J(\sigma)=\sum_{j\in J}w_j\sum_{i\in J,\ \sigma(i)=\sigma(j),\ i\le j}p_i$ is the cost of the schedule of $J$ processing each machine's jobs in increasing order of index. Further, $T_i=\sum_{j=1}^i p_j$, $U_i=\sum_{j=1}^i w_jT_j$ and $W_{>i}=\sum_{j=i+1}^n w_j$, with $T_0=U_0=0$ and $W_{>n}=0$.
--
--   These are the problem $Pm\|\sum w_jC_j$ of the paper and the notation of §4.
--
--   **Formalization Note** Ratio comparisons are written without division ($w_jp_i<w_ip_j$). Jobs are indexed $0,\dots,n-1$; the paper's job $j$ is index $j-1$. Idle time never helps and is not modelled. $\mathrm{OPT}$ is a `sInf` over the finite set of schedule costs, which is its minimum whenever $m\ge1$. Processing times and weights are real numbers, as in §1; §4 assumes them integral.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 1 (PDF p. 2), §1 problem statement; p. 11 (PDF p. 12), §4 model, Smith's rule [Smi56]; p. 12 (PDF p. 13), notation p(S), T_i, U_i, W_{>i}, schedules of J

import Mathlib

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

open Finset

/-!
# The scheduling problem `Pm||Σ w_j C_j` (§1, p. 1; §4, pp. 11–12, PDF 12–13)

`m` identical machines, `n` jobs `j = 0, …, n−1` (the paper's jobs `1, …, n`) with processing
times `p_j > 0` and weights `w_j ≥ 0` (real numbers, as in §1, p. 1; §4 assumes integers, a special
case). The sign conditions are hypotheses of the theorems. A nonpreemptive schedule assigns every
job to a machine (`σ : Fin n → Fin m`) and orders the jobs of every machine; every family of
per-machine orders is induced by a single priority permutation `ρ` (job `i` precedes job `j` on a
common machine iff `ρ i < ρ j`). Machines process their jobs back to back from time `0`, so the
completion time of `j` is the total processing time of the jobs of its machine up to and
including `j`. `OPT` is the minimum cost over **all** such schedules.
-/

/-- Completion time `C_j` of job `j` in the schedule given by the assignment `σ` and the priority
permutation `ρ`. -/
noncomputable def completion {n m : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n)
    (j : Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => σ i = σ j ∧ ρ i ≤ ρ j), p i

/-- The cost `Σ_j w_j C_j` of the schedule `(σ, ρ)`. -/
noncomputable def cost {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n) : ℝ :=
  ∑ j, w j * completion p σ ρ j

/-- `OPT`: the minimum of `cost` over all nonpreemptive schedules on `m` machines (assignment and
per-machine order). The set is finite (finitely many `σ, ρ`), and nonempty when `m ≥ 1` or
`n = 0`; then `sInf` is its minimum. -/
noncomputable def OPT (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n), cost p w σ ρ = c}

/-- Smith's order: job `i` is processed no later than job `j` on a common machine when
`w_i/p_i > w_j/p_j`, or the ratios are equal and `i ≤ j` (ties by index). Written without
division: `w_j p_i < w_i p_j`, or `w_j p_i = w_i p_j` and `i ≤ j`. -/
abbrev SmithBefore {n : ℕ} (p w : Fin n → ℝ) (i j : Fin n) : Prop :=
  w j * p i < w i * p j ∨ (w j * p i = w i * p j ∧ i ≤ j)

/-- Completion time of job `j` when the jobs of every machine of `σ` are processed in Smith's
order. -/
noncomputable def smithCompletion {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) (j : Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => σ i = σ j ∧ SmithBefore p w i j), p i

/-- The cost of the assignment `σ` with every machine processing its jobs in Smith's order. -/
noncomputable def smithCost {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∑ j, w j * smithCompletion p w σ j

/-- §4's assumption "without loss of generality `w_1/p_1 ≥ … ≥ w_n/p_n`", without division:
for `i ≤ j`, `w_j p_i ≤ w_i p_j`. -/
def Sorted {n : ℕ} (p w : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i ≤ j → w j * p i ≤ w i * p j

/-- §4, p. 12 (PDF 13): the cost of a schedule of the job set `J` in which every machine
processes its jobs of `J` in increasing order of index; `σ` is read only on `J`.
`C_j(S) = Σ_{i ∈ J, σ i = σ j, i ≤ j} p_i`. -/
noncomputable def costIdxOn {n m : ℕ} (p w : Fin n → ℝ) (J : Finset (Fin n)) (σ : Fin n → Fin m) : ℝ :=
  ∑ j ∈ J, w j * ∑ i ∈ J.filter (fun i => σ i = σ j ∧ i ≤ j), p i

/-- `T_i = Σ_{j=1}^{i} p_j`, the total processing time of the first `i` jobs (`T_0 = 0`). -/
noncomputable def T {n : ℕ} (p : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => j.val < i), p j

/-- `U_i = Σ_{j=1}^{i} w_j T_j` (`U_0 = 0`); in 0-based indexing job `j` is the paper's job
`j + 1`. -/
noncomputable def U {n : ℕ} (p w : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => j.val < i), w j * T p (j.val + 1)

/-- `W_{>i} = Σ_{j=i+1}^{n} w_j`, the total weight of the last `n − i` jobs (`W_{>n} = 0`). -/
noncomputable def Wgt {n : ℕ} (w : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => i ≤ j.val), w j

end FasterWCTFPTAS.Main


