-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_DP
-- name    : FasterWCTFPTAS_Main_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:31.930079+00:00
-- url     : https://prove2.me/theorems/df22119e-b5da-4ac3-9497-4d12ff45b5ee
-- title:
--   The DP sets DP_i, the recurrence map, and δ-representative sets (Definition 4.2)
-- statement:
--   Fix $m\ge2$ machines and an instance with jobs $1,\dots,n$. A **schedule of the first $i$ jobs** assigns each of the jobs $1,\dots,i$ to a machine, every machine processing its jobs in increasing order of index. It has the **load vector** $\pi^S=(p(S_1),\dots,p(S_{m-1}))\in\mathbb R^{m-1}$ (the load of the last machine $m$ is $T_i-\|\pi^S\|_1$) and the **cost value** $\theta^S=\mathrm{cost}(S)$. The set $\mathrm{DP}_i$ consists of all pairs $(\pi^S,\theta^S)$ over all schedules $S$ of the first $i$ jobs; $\mathrm{DP}_0=\{((0,\dots,0),0)\}$.
--
--   For a set $D$ of pairs and job $i$, the recurrence map is
--
--   $$
--   \widehat D=\{(\pi+e_kp_i,\ \theta+w_i(\pi_k+p_i)):(\pi,\theta)\in D,\ k\in[m-1]\}\cup\{(\pi,\ \theta+w_i(T_{i-1}-\|\pi\|_1+p_i)):(\pi,\theta)\in D\}.
--   $$
--
--   For a schedule $S$ of $\{1,\dots,i\}$ and a schedule $S'$ of $\{i+1,\dots,n\}$, $S\cup S'$ is the combined schedule of all jobs.
--
--   **Definition 4.2 (Representative set).** Let $i\in[n]$, $\delta\in(0,1)$, and $D\subseteq\mathrm{DP}_i$. A $\delta$-representative set of a set $D$ for $i$ is a subset $\widetilde D\subseteq D$ such that for every schedule $S'$ of the jobs $\{i+1,\dots,n\}$ and for every $(\pi^S,\theta^S)\in D$ there exists $(\pi^{\tilde S},\theta^{\tilde S})\in\widetilde D$ such that
--
--   $$
--   \mathrm{cost}(\tilde S\cup S')\le\mathrm{cost}(S\cup S')+\delta\,\mathrm{OPT}.
--   $$
--
--   These are the states of the classical load-vector dynamic program and the notion of approximate dominance under which the FPTAS discards states.
--
--   **Formalization Note** Jobs are indexed $0,\dots,n-1$, and "the first $i$ jobs" are the indices $<i$; machine $k\in\{0,\dots,m-2\}$ is the paper's machine $k+1$, and the paper's last machine is machine $m-1$. A schedule is an assignment $\sigma$ read only on the relevant jobs. $\|\pi\|_1=\sum_k|\pi_k|$. Definition 4.2 is defined for every $i\in\{0,\dots,n\}$ and every real $\delta$ (the proof of Theorem 1.1 uses it at $i=0$ and with $i\delta$, which can equal $1$). The pair-level quantifiers are read as "for every schedule $S$ whose pair lies in $D$ there is a schedule $\tilde S$ whose pair lies in $\widetilde D$"; since $\mathrm{cost}(S\cup S')$ depends on $S$ only through $(\pi^S,\theta^S)$ (proof of Lemma 4.6), this is the same notion. $\mathrm{OPT}$ is the optimum over all nonpreemptive schedules; on a sorted instance it equals the paper's minimum over index-ordered partitions by Smith's rule.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 12 (PDF p. 13), §4.1 DP_i and Lemma 4.1; p. 13 (PDF p. 14), Definition 4.2 and Observation 4.3

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Geometry
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

open Finset

/-!
# The exact DP and representative sets (§4.1–4.2, pp. 12–13, PDF 13–14)

Jobs are `0, …, n−1` (the paper's `1, …, n`); "the first `i` jobs" are those with index `< i`.
A schedule of a job set `J` is an assignment `σ : Fin n → Fin m` read only on `J`, every machine
processing its jobs of `J` in increasing order of index (`costIdxOn`). Machine `k ∈ {0,…,m−2}` is
the paper's machine `k + 1`; the paper's last machine `m` is machine `m − 1`, whose load is not
recorded in the load vector.
-/

/-- The first `i` jobs `{1, …, i}` (0-based: indices `< i`). -/
def firstJobs (n i : ℕ) : Finset (Fin n) := univ.filter (fun j => j.val < i)

/-- The machine of load coordinate `k ∈ [m − 1]`. -/
def coordMachine {m : ℕ} (k : Fin (m - 1)) : Fin m :=
  ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.sub_le m 1)⟩

/-- The load vector `π^S = (p(S_1), …, p(S_{m−1}))` of the schedule `σ` of the first `i` jobs. -/
noncomputable def piVec (m : ℕ) {n : ℕ} (p : Fin n → ℝ) (i : ℕ) (σ : Fin n → Fin m) : Fin (m - 1) → ℝ :=
  fun k => ∑ j ∈ (firstJobs n i).filter (fun j => σ j = coordMachine k), p j

/-- The cost value `θ^S = cost(S)` of the schedule `σ` of the first `i` jobs. -/
noncomputable def theta (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) (i : ℕ) (σ : Fin n → Fin m) : ℝ :=
  costIdxOn p w (firstJobs n i) σ

/-- The pair `(π^S, θ^S)` of the schedule `σ` of the first `i` jobs. -/
noncomputable def pairOf (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) (i : ℕ) (σ : Fin n → Fin m) : Pt m :=
  (piVec m p i σ, theta m p w i σ)

/-- `DP_i`: the set of all pairs `(π^S, θ^S)` over all schedules `S` of the first `i` jobs.
For `i = 0` (and `m ≥ 1`) it is `{((0, …, 0), 0)}`, the paper's `DP_0`. -/
noncomputable def DP (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) (i : ℕ) : Set (Pt m) :=
  Set.range (pairOf m p w i)

/-- The right-hand side of the recurrence of Lemma 4.1 applied to a set `D` of pairs, for the
job `i : Fin n` (the paper's job `i + 1`, whose predecessors number `i`, so the paper's `T_{i−1}`
is `T p i`):
`{(π + e_k p_i, θ + w_i (π_k + p_i)) : (π, θ) ∈ D, k ∈ [m−1]} ∪
 {(π, θ + w_i (T_{i−1} − ‖π‖₁ + p_i)) : (π, θ) ∈ D}`. -/
noncomputable def recur (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) (i : Fin n) (D : Set (Pt m)) : Set (Pt m) :=
  {x | ∃ y ∈ D, ∃ k : Fin (m - 1),
      x = (y.1 + Pi.single k (p i), y.2 + w i * (y.1 k + p i))} ∪
  {x | ∃ y ∈ D,
      x = (y.1, y.2 + w i * (T p i.val - ∑ k, |y.1 k| + p i))}

/-- The combined schedule `S ∪ S'` of a schedule `σ` of the first `i` jobs and a schedule `σ'`
of the remaining jobs `{i + 1, …, n}`. -/
def combine {n m : ℕ} (i : ℕ) (σ σ' : Fin n → Fin m) : Fin n → Fin m :=
  fun j => if j.val < i then σ j else σ' j

/-- **Definition 4.2** (representative set), p. 13 (PDF 14), read for every `i ∈ {0, …, n}` and
every real `δ` (reading R7). `Dt` is a `δ`-representative set of `D` for `i`: `Dt ⊆ D`, and for every
schedule `S'` of the jobs `{i + 1, …, n}` and every schedule `S` of the first `i` jobs whose pair
`(π^S, θ^S)` lies in `D`, there is a schedule `S̃` of the first `i` jobs whose pair lies in `Dt`
with `cost(S̃ ∪ S') ≤ cost(S ∪ S') + δ · OPT`. -/
def IsRepSet (m : ℕ) {n : ℕ} (p w : Fin n → ℝ) (i : ℕ) (δ : ℝ) (Dt D : Set (Pt m)) : Prop :=
  Dt ⊆ D ∧
    ∀ σ' : Fin n → Fin m, ∀ σ : Fin n → Fin m, pairOf m p w i σ ∈ D →
      ∃ σt : Fin n → Fin m, pairOf m p w i σt ∈ Dt ∧
        costIdxOn p w univ (combine i σt σ') ≤ costIdxOn p w univ (combine i σ σ') + δ * OPT m p w

end FasterWCTFPTAS.Main


