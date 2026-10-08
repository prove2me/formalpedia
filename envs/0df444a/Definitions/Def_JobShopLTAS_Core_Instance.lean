-- Prove2me | Definitions.Def_JobShopLTAS_Core_Instance
-- name    : JobShopLTAS_Core_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T06:40:51.596648+00:00
-- url     : https://prove2.me/theorems/2c19f9b1-dd0b-49f8-a287-a9ec376f20c9
-- title:
--   Job shop instance, loads $P_t$, $P_{\max}$, job lengths, feasible schedules, makespan and optimum makespan $C^*_{\max}$
-- statement:
--   A **job shop instance** has $m$ machines $M_1,\dots,M_m$ and $n$ jobs $J_1,\dots,J_n$. Job $J_j$ is a sequence of $\mu_j$ **operations** $O_{1j},\dots,O_{\mu_j j}$ that must be processed in this order; operation $O_{ij}$ is processed without interruption on machine $M_{\pi_{ij}}$ for $p_{ij}\ge 0$ time units. Consecutive operations of a job may use the same machine. The maximum number of operations of a job is $\mu=\max_j \mu_j$.
--
--   The **load** of machine $M_t$ is $P_t=\sum_{\pi_{ij}=t} p_{ij}$, the **maximum load** is $P_{\max}=\max_t P_t$, and the **length** of job $J_j$ is $l_j=\sum_{i=1}^{\mu_j} p_{ij}$.
--
--   A **feasible schedule** of a set $J$ of jobs assigns a start time $S_{ij}$ to every operation of a job in $J$, with completion time $C_{ij}=S_{ij}+p_{ij}$, such that
--   $$S_{ij}\ge 0,\qquad C_{ij}\le S_{i+1,j},\qquad \text{and}\qquad C_{ij}\le S_{i'j'}\ \text{or}\ C_{i'j'}\le S_{ij}$$
--   for every two distinct operations $O_{ij}\neq O_{i'j'}$ on the same machine. Its **makespan** is $C_{\max}=\max_{ij} C_{ij}$ over the operations of jobs in $J$ (and $0$ if there are none). The **optimum makespan** of $J$ is the infimum of the makespans of the feasible schedules of $J$; $C^*_{\max}$ is the optimum makespan of the whole job set.
--
--   **Formalization Note.** Machines are `Fin m`, jobs `Fin n`, and the operations of job $j$ are `Fin (μ j)` (0-based). An operation is a pair `⟨j, i⟩` of the sigma type `Op`. Processing times are real with `p_nonneg`; no integrality or positivity is assumed. $P_{\max}$ is `⨆ t : Fin m, load t` (a maximum over a finite nonempty set whenever $m\ge 1$); the makespan is a supremum over the finite set of operations of jobs in $J$, which is $0$ when that set is empty. The optimum makespan is `sInf` of the makespans of the feasible schedules; the schedule set is never empty (process the jobs one after another), and makespans of feasible schedules are $\ge 0$.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 288, Section 1, and p. 290, Section 2

import Mathlib

namespace JobShopLTAS.Core

/-- A job shop instance (Jansen–Solis-Oba–Sviridenko 2003, §1, p. 288): `m` machines
`M_1, …, M_m` (indexed by `Fin m`) and `n` jobs `J_1, …, J_n` (indexed by `Fin n`). Job `j`
is a sequence of `μ j` operations `O_{1j}, …, O_{μ_j j}` (indexed by `Fin (μ j)`, 0-based),
processed in this order; operation `i` of job `j` runs without interruption on machine
`π j i` for `p j i ≥ 0` time units. Consecutive operations may use the same machine. -/
structure Instance (m n : ℕ) where
  /-- number of operations `μ_j` of job `j` -/
  μ : Fin n → ℕ
  /-- machine `π_{ij}` of operation `i` of job `j` -/
  π : (j : Fin n) → Fin (μ j) → Fin m
  /-- processing time `p_{ij}` of operation `i` of job `j` -/
  p : (j : Fin n) → Fin (μ j) → ℝ
  p_nonneg : ∀ j i, 0 ≤ p j i

namespace Instance

variable {m n : ℕ} (inst : Instance m n)

/-- The operations of the instance: pairs `⟨j, i⟩` with `i : Fin (μ j)`. -/
abbrev Op := Σ j : Fin n, Fin (inst.μ j)

/-- Processing time of an operation. -/
def proc (o : inst.Op) : ℝ := inst.p o.1 o.2

/-- Machine of an operation. -/
def mach (o : inst.Op) : Fin m := inst.π o.1 o.2

/-- `µ = max_j µ_j`, the maximum number of operations of a job (§1, p. 288). -/
def maxOps : ℕ := Finset.univ.sup inst.μ

/-- The load `P_t = ∑_{π_{ij} = t} p_{ij}` of machine `t` (§2, p. 290). -/
def load (t : Fin m) : ℝ :=
  ∑ o ∈ Finset.univ.filter (fun o : inst.Op => inst.mach o = t), inst.proc o

/-- `P_max = max_t P_t`, the maximum machine load (§2, p. 290). `Fin m` is finite, so this
supremum is a maximum whenever `m ≥ 1`. -/
noncomputable def Pmax : ℝ := ⨆ t : Fin m, inst.load t

/-- The length `l_j = ∑_{i=1}^{µ_j} p_{ij}` of job `j` (§2, p. 290). -/
def jobLength (j : Fin n) : ℝ := ∑ i, inst.p j i

/-- `s` (start times `S_{ij}` of the operations) is a feasible nonpreemptive schedule of the
jobs in `J`: starts are nonnegative, every operation of a job starts after the previous
operation of that job completes (`C_{ij} = S_{ij} + p_{ij} ≤ S_{i+1,j}`), and two distinct
operations on the same machine do not overlap. Values of `s` on operations of jobs outside
`J` are irrelevant. -/
structure IsFeasibleSchedule (J : Finset (Fin n)) (s : inst.Op → ℝ) : Prop where
  start_nonneg : ∀ o : inst.Op, o.1 ∈ J → 0 ≤ s o
  precedence : ∀ j ∈ J, ∀ i i' : Fin (inst.μ j), i.val + 1 = i'.val →
    s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, i'⟩
  machine_disjoint : ∀ o o' : inst.Op, o.1 ∈ J → o'.1 ∈ J → o ≠ o' →
    inst.mach o = inst.mach o' → s o + inst.proc o ≤ s o' ∨ s o' + inst.proc o' ≤ s o

/-- The makespan `C_max = max C_{ij}` of `s` restricted to the operations of jobs in `J`
(a maximum over a finite set; `0` if that set is empty). -/
noncomputable def makespan (J : Finset (Fin n)) (s : inst.Op → ℝ) : ℝ :=
  ⨆ o : {o : inst.Op // o.1 ∈ J}, s o.1 + inst.proc o.1

/-- The optimum makespan of the jobs in `J`: the infimum of the makespans of all feasible
schedules of `J`. `C*_max` of the paper is `inst.optMakespan Finset.univ`. -/
noncomputable def optMakespan (J : Finset (Fin n)) : ℝ :=
  sInf (inst.makespan J '' {s | inst.IsFeasibleSchedule J s})

end Instance

end JobShopLTAS.Core


