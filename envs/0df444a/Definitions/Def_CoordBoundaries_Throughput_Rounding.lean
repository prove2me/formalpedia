-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_Rounding
-- name    : CoordBoundaries_Throughput_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:59.501104+00:00
-- url     : https://prove2.me/theorems/65ba8c99-5645-4bca-884f-1d68ea4aac00
-- title:
--   Algorithm 1: slots, job–slot matchings, A×, the initial matching, good and bad jobs, J_miss, the crossing graph and the coordinated schedule
-- statement:
--   Fix a configuration solution and an outcome $\omega$. A **slot** is one execution interval $[u,v)$ of the stored schedule of $\omega_B$, with its machine and the job that produced it. Job $j$ is **compatible** with a slot $[u,v)$ when $\max\{r_j,u\}+p_j\le\min\{d_j,v\}$. A job–slot **matching** uses each job and each slot at most once; $A_\times$ is the size of a maximum matching, and a matched job runs on its slot's machine from $\max\{r_j,u\}$. A slot produced by a global job is a **boundary slot** if its block is a boundary block of that job and an **interior slot** otherwise.
--
--   The **initial integral matching** assigns each sampled local job its own slot and each global job appearing at a boundary one of its own boundary slots ($B_L(j)$ first). A **fractional matching** puts nonnegative mass on compatible pairs, at most one per job and per slot. $D_j=(1-a_j)(1-b_j)$ is the probability that $j$ is absent at both boundaries.
--
--   A global job is **good** if $a_j,b_j\ge1/4$ and **bad** otherwise; $P=\sum_{j\text{ bad}}e_j$. For tracked sets $H$, $J_{\mathrm{miss}}=\{j\text{ good}: j\notin H_{B_L(j)}\cap H_{B_R(j)}\}$. A **maximal matching $\mathcal X$ of the crossing graph** is a set of vertex-disjoint crossing pairs of good jobs to which no crossing pair of two unmatched good jobs can be added; $\nu=|\mathcal X|$.
--
--   The **coordinated schedule** of an outcome keeps all local executions, deletes all global interior executions, lets each coordinated job (good, unmatched, not excluded) keep a boundary execution if present, and keeps every other global job only at its more likely boundary (fixed tie-breaking), if present; $A_{\mathrm{keep}}$ is its cardinality. Algorithm 1 returns the larger of the matching schedule of an independent sample and the coordinated schedule of a joint sample with marginals $x$ that separates the coordinated jobs.
--
--   **Formalization Note** The tie-breaking rule is a parameter (any rule choosing a boundary with the larger marginal), and the two samples may be coupled arbitrarily.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 14–20, §3: Algorithm 1 (p. 15), slots and matching (p. 14), initial matching and D_j (p. 15), good/bad and J_miss (p. 14), crossing graph and coordinated schedule (p. 19), P (p. 19)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Relaxation

open Classical

namespace CoordBoundaries.Throughput

/-! # Algorithm 1: slots, matchings and the coordinated schedule (Tong–Xu, §3, pp. 14–20)

For a sampled outcome `ω` (one configuration per block) a *slot* is a pair `(B, j')` with
`j' ∈ ω_B`: the execution of `j'` in the stored schedule of `ω_B`, with its machine. Job `j` is
compatible with a slot `[u, v)` when `max{r_j, u} + p_j ≤ min{d_j, v}` (p. 14). `A×` is the size of
a maximum job–slot matching; `A_keep` is the size of the coordinated schedule of steps 5–6. -/

/-- A slot: (block, producing job). -/
abbrev Slot (I : Instance) (P : Partition I.T) := Fin P.len × Fin I.n

/-- Block of a given index, if it exists. -/
def toBlock {I : Instance} (P : Partition I.T) (t : ℕ) : Option (Fin P.len) :=
  if h : t < P.len then some ⟨t, h⟩ else none

/-- The slot of the initial integral matching (p. 15): a sampled local job gets its own slot; a
global job appearing at a boundary gets its own slot at `B_L(j)` if present, else at `B_R(j)`. -/
noncomputable def initSlot {I : Instance} (P : Partition I.T) (ω : Tuple I P) (j : Fin I.n) :
    Option (Slot I P) :=
  let own : ℕ → Option (Slot I P) := fun t =>
    (toBlock P t).bind fun B => if j ∈ ω B then some (B, j) else none
  if P.IsLocal j then own (P.BL j) else (own (P.BL j)).orElse fun _ => own (P.BR j)

/-- The initial integral matching as a 0/1 assignment. -/
noncomputable def initFrac {I : Instance} (P : Partition I.T) (ω : Tuple I P) (j : Fin I.n)
    (σ : Slot I P) : ℝ :=
  if initSlot P ω j = some σ then 1 else 0

/-- A collection of crossing pairs of global jobs with no job in two pairs (Lemma 3.2). -/
def Partition.IsCrossCollection {I : Instance} (P : Partition I.T)
    (X : Finset (Fin I.n × Fin I.n)) : Prop :=
  (∀ e ∈ X, P.IsGlobal e.1 ∧ P.IsGlobal e.2 ∧ P.Cross e.1 e.2) ∧
    ∀ e ∈ X, ∀ e' ∈ X, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

/-- A slot is interior when its producing job is global and its block is not one of that job's
boundary blocks (p. 15). -/
def Partition.IsInterior {I : Instance} (P : Partition I.T) (σ : Slot I P) : Prop :=
  P.IsGlobal σ.2 ∧ (σ.1 : ℕ) ≠ P.BL σ.2 ∧ (σ.1 : ℕ) ≠ P.BR σ.2

/-- Job `j` is absent at both boundaries in `ω` (`j ∉ C_{B_L(j)}` and `j ∉ C_{B_R(j)}`). -/
def Partition.AbsentBoth {I : Instance} (P : Partition I.T) (ω : Tuple I P) (j : Fin I.n) :
    Prop :=
  j ∉ atN ω (P.BL j) ∧ j ∉ atN ω (P.BR j)

namespace ConfigSol

variable {I : Instance} {P : Partition I.T} {K : ℕ} (s : ConfigSol I P K)

/-- The execution (machine, start) of slot `σ = (B, j')` in outcome `ω`, if `j' ∈ ω_B`. -/
noncomputable def slotExec (ω : Tuple I P) (σ : Slot I P) : Option (Fin I.m × ℝ) :=
  if σ.2 ∈ ω σ.1 then s.store σ.1 (ω σ.1) σ.2 else none

/-- Job `j` is adjacent to slot `σ = [u, v)`: `max{r_j, u} + p_j ≤ min{d_j, v}` (p. 14). -/
def Compat (ω : Tuple I P) (j : Fin I.n) (σ : Slot I P) : Prop :=
  ∃ (i : Fin I.m) (u : ℝ), s.slotExec ω σ = some (i, u) ∧
    max (I.r j : ℝ) u + I.p j ≤ min (I.d j : ℝ) (u + I.p σ.2)

/-- A job–slot matching: compatible pairs, each job and each slot used at most once. -/
def IsMatching (ω : Tuple I P) (M : Finset (Fin I.n × Slot I P)) : Prop :=
  (∀ e ∈ M, s.Compat ω e.1 e.2) ∧ (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

/-- `A×`: the size of a maximum job–slot matching (over all jobs and all sampled slots). -/
noncomputable def Ax (ω : Tuple I P) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin I.n × Slot I P))).filter (s.IsMatching ω)).sup Finset.card

/-- The schedule of a matching: each matched job runs on its slot's machine from `max{r_j, u}`. -/
noncomputable def matchSched (ω : Tuple I P) (M : Finset (Fin I.n × Slot I P)) : Sched I :=
  fun j =>
    if h : ∃ σ, (j, σ) ∈ M then
      (s.slotExec ω (Classical.choose h)).map fun iu => (iu.1, max (I.r j : ℝ) iu.2)
    else none

/-- A fractional matching (p. 15): nonnegative values on compatible pairs, at most one per job and
per slot. -/
def IsFracMatching (ω : Tuple I P) (f : Fin I.n → Slot I P → ℝ) : Prop :=
  (∀ j σ, 0 ≤ f j σ) ∧ (∀ j σ, f j σ ≠ 0 → s.Compat ω j σ) ∧
    (∀ j, ∑ σ, f j σ ≤ 1) ∧ (∀ σ, ∑ j, f j σ ≤ 1)

/-- `D_j = (1 − a_j)(1 − b_j)`, the probability that `j` is absent at both boundaries (p. 15).
Distinct from the aggregate deficit `𝒟 = Dagg`. -/
noncomputable def Dabs (j : Fin I.n) : ℝ := (1 - s.a j) * (1 - s.b j)

/-- A global job is good if `a_j, b_j ≥ 1/4` (p. 14). -/
def IsGood (j : Fin I.n) : Prop := P.IsGlobal j ∧ 1 / 4 ≤ s.a j ∧ 1 / 4 ≤ s.b j

/-- A global job is bad otherwise. -/
def IsBad (j : Fin I.n) : Prop := P.IsGlobal j ∧ ¬ (1 / 4 ≤ s.a j ∧ 1 / 4 ≤ s.b j)

/-- `J_miss = {j good : j ∉ H_{B_L(j)} ∩ H_{B_R(j)}}` for projected consistency (p. 14). -/
noncomputable def JmissOf (H : Fin P.len → Finset (Fin I.n)) : Finset (Fin I.n) :=
  Finset.univ.filter fun j =>
    s.IsGood j ∧ ¬ (j ∈ trackedAt H (P.BL j) ∧ j ∈ trackedAt H (P.BR j))

/-- Job `j` is covered by a pair of `X`. -/
def Matched (X : Finset (Fin I.n × Fin I.n)) (j : Fin I.n) : Prop := ∃ e ∈ X, e.1 = j ∨ e.2 = j

/-- `X` is a maximal matching of the crossing graph on good jobs (p. 19): pairwise vertex-disjoint
crossing pairs of good jobs, to which no crossing pair of two unmatched good jobs can be added. -/
def IsMaximalCrossMatching (X : Finset (Fin I.n × Fin I.n)) : Prop :=
  (∀ e ∈ X, s.IsGood e.1 ∧ s.IsGood e.2 ∧ P.Cross e.1 e.2) ∧
    (∀ e ∈ X, ∀ e' ∈ X, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
    ∀ j k, s.IsGood j → s.IsGood k → P.Cross j k → Matched X j ∨ Matched X k

/-- `P := Σ_{j bad} e_j`, the total boundary deficit of bad jobs (p. 19). -/
noncomputable def Pbad : ℝ := ∑ j ∈ Finset.univ.filter s.IsBad, s.e j

/-- The coordinated family of step 4: good jobs unmatched by `X` and outside `Jm`. -/
noncomputable def coordSet (X : Finset (Fin I.n × Fin I.n)) (Jm : Finset (Fin I.n)) :
    Finset (Fin I.n) :=
  Finset.univ.filter fun j => s.IsGood j ∧ ¬ Matched X j ∧ j ∉ Jm

/-- A fixed tie-breaking rule for "the more likely boundary" (`true` = `B_L(j)`): the chosen
boundary has the larger marginal. -/
def SideRule (side : Fin I.n → Bool) : Prop :=
  ∀ j, P.IsGlobal j → (side j = true → s.b j ≤ s.a j) ∧ (side j = false → s.a j ≤ s.b j)

/-- The stored execution of `j` in `ω` at the block of index `t`. -/
noncomputable def storeAt (ω : Tuple I P) (t : ℕ) (j : Fin I.n) : Option (Fin I.m × ℝ) :=
  if h : t < P.len then s.store ⟨t, h⟩ (ω ⟨t, h⟩) j else none

/-- The coordinated schedule (steps 5–6 of Algorithm 1): keep all local executions; drop global
interior executions; a coordinated job (in `J`) keeps its boundary execution if present (at
`B_L(j)` if it appears there); every other global job keeps its execution only at its more likely
boundary `side j`, if present. -/
noncomputable def keepSched (side : Fin I.n → Bool) (J : Finset (Fin I.n)) (ω : Tuple I P) :
    Sched I := fun j =>
  if P.IsLocal j then
    (if j ∈ atN ω (P.BL j) then s.storeAt ω (P.BL j) j else none)
  else if j ∈ J then
    (if j ∈ atN ω (P.BL j) then s.storeAt ω (P.BL j) j
     else if j ∈ atN ω (P.BR j) then s.storeAt ω (P.BR j) j else none)
  else
    (let t := if side j then P.BL j else P.BR j
     if j ∈ atN ω t then s.storeAt ω t j else none)

/-- `A_keep`: the cardinality of the coordinated schedule. -/
noncomputable def Akeep (side : Fin I.n → Bool) (J : Finset (Fin I.n)) (ω : Tuple I P) : ℕ :=
  (scheduled (s.keepSched side J ω)).card

/-- `κ` is a coupling of independent block sampling (first coordinate) and the joint law `μ`
(second coordinate). -/
def IsCoupling (μ : Tuple I P → ℝ) (κ : Tuple I P × Tuple I P → ℝ) : Prop :=
  (∀ w, 0 ≤ κ w) ∧ (∀ w, w ∉ outcomes P K ×ˢ outcomes P K → κ w = 0) ∧
    (∀ ω ∈ outcomes P K, ∑ ω' ∈ outcomes P K, κ (ω, ω') = s.prodProb ω) ∧
    (∀ ω' ∈ outcomes P K, ∑ ω ∈ outcomes P K, κ (ω, ω') = μ ω')

/-- What Algorithm 1 guarantees for the matching `X`, the excluded set `Jm` and the tie-break
`side`: a coordinated joint law exists (step 4); every matching yields a feasible schedule of its
cardinality and the coordinated schedule is feasible, on every outcome; and for every coordinated
joint law and every coupling of the two samples, `E[max{A×, A_keep}] ≥ bound`. -/
def AlgOneGuarantee (X : Finset (Fin I.n × Fin I.n)) (Jm : Finset (Fin I.n))
    (side : Fin I.n → Bool) (bound : ℝ) : Prop :=
  (∃ μ, IsLaw P K μ ∧ s.HasMarginals μ ∧ Separates P μ (s.coordSet X Jm)) ∧
  (∀ ω ∈ outcomes P K, ∀ M, s.IsMatching ω M →
      Feasible I (s.matchSched ω M) ∧ (scheduled (s.matchSched ω M)).card = M.card) ∧
  (∀ ω ∈ outcomes P K, Feasible I (s.keepSched side (s.coordSet X Jm) ω)) ∧
  ∀ μ, IsLaw P K μ → s.HasMarginals μ → Separates P μ (s.coordSet X Jm) →
    ∀ κ, s.IsCoupling μ κ →
      bound ≤ ∑ w ∈ outcomes P K ×ˢ outcomes P K,
        κ w * (max (s.Ax w.1) (s.Akeep side (s.coordSet X Jm) w.2) : ℝ)

end ConfigSol

end CoordBoundaries.Throughput


