-- Prove2me | Definitions.Def_ProjSchedTW_DelayingModes_Project
-- name    : ProjSchedTW_DelayingModes_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T22:13:58.522986+00:00
-- url     : https://prove2.me/theorems/e8be2f17-4df6-4d85-a690-f2465d1eeaf2
-- title:
--   §1.1–1.3, §2.1, §2.3.2, §2.5.1 — projects, feasible schedules, forbidden sets, minimal delaying alternatives and modes
-- statement:
--   This file sets up the resource-constrained project scheduling model of Neumann, Schwindt and Zimmermann and the objects of §2.5.1.
--
--   **Project.** The activity set is $V=\{0,1,\dots,n+1\}$, where $0$ is the project beginning, $n+1$ the project completion, and $1,\dots,n$ are the real activities. Each activity $i$ has a duration $p_i\in\mathbb Z_{\ge 0}$. The project network $N$ has arc set $E\subseteq V\times V$ with integer arc weights $\delta_{ij}$; an arc $\langle i,j\rangle$ encodes the temporal constraint $S_j-S_i\ge\delta_{ij}$ (Eq. (1.2.1)). There is a finite set $\mathcal R$ of renewable resources; resource $k$ has capacity $R_k\in\mathbb N$, and activity $i$ uses $r_{ik}\in\mathbb Z_{\ge0}$ units of it while in progress.
--
--   **Standing assumptions** (§1.1, Remarks 1.1.2, p. 11, §2.1): $n\ge 1$; $p_0=p_{n+1}=0$ and $p_i>0$ for every real activity; $E$ has no loops; $r_{0k}=r_{n+1,k}=0$ and $r_{ik}\le R_k$; and $N$ contains a path from $0$ to every node and from every node to $n+1$.
--
--   **Schedules.** A schedule is a vector $S=(S_i)_{i\in V}$ of real start times with $S_i\ge0$ and $S_0=0$ (Definition 1.3.1). It is *time-feasible* if $S_j-S_i\ge\delta_{ij}$ for all $\langle i,j\rangle\in E$. The active set at time $t$ is
--   $$\mathcal A(S,t)=\{i\in V\mid S_i\le t<S_i+p_i\},$$
--   and $r_k(S,t)=\sum_{i\in\mathcal A(S,t)}r_{ik}$ (Eqs. (2.1.1)–(2.1.2)). $S$ is *resource-feasible* if $r_k(S,t)\le R_k$ for every $k\in\mathcal R$ and every $t\ge0$, and *feasible* if it is both (Definition 2.1.1).
--
--   **Forbidden sets** (Definition 2.3.9). A set $F\subseteq V$ is *forbidden* if $\sum_{i\in F}r_{ik}>R_k$ for some $k$, *feasible* otherwise, and *minimal forbidden* if it is forbidden but no proper subset is.
--
--   **Delaying alternatives and modes** (Definitions 2.5.1 and 2.5.6). For a forbidden set $F$, a set $B\subseteq F$ is a *delaying alternative* if $F\setminus B$ is feasible, and a *minimal delaying alternative* if in addition no proper subset $B'\subset B$ is a delaying alternative. A pair $(i,B)$ with $F$ forbidden, $B$ a minimal delaying alternative for $F$, and $i\in F\setminus B$ is a *minimal delaying mode* for $F$.
--
--   These are the objects on which the branch-and-bound enumeration scheme of §2.5 branches: at a resource conflict, the forbidden active set is resolved by delaying the activities of $B$ until the completion of $i$.
--
--   **Formalization Note.** $V$ is `Fin (n + 2)` with $n+1$ as `Fin.last (n + 1)`. Start times are real; durations, capacities and requirements are natural numbers. The resource constraints are imposed for **all** $t\ge0$, not only for $0\le t\le\bar d$ as (2.1.4) literally writes; this is the reading the book's proofs and Remark 2.3.11 use. A path is a simple path (no repeated node), given as an injective sequence of nodes. Minimality is Mathlib's `Minimal` for inclusion of finite sets.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 2, 10–11, 24–25, 34, 46, 49; Remarks 1.1.2, Definition 1.3.1, Eqs. (1.2.1), (2.1.1)–(2.1.4), Definitions 2.1.1, 2.3.9, 2.5.1, 2.5.6

import Mathlib

namespace ProjSchedTW.DelayingModes

/-- A project with `n` real activities, minimum and maximum time lags, and renewable resources
(Neumann–Schwindt–Zimmermann, §1.1–1.2 and §2.1, pp. 1–8 and 24–25).
The activity set is `V = {0, 1, …, n+1}`, encoded as `Fin (n + 2)`: node `0` is the project
beginning and node `Fin.last (n + 1)` the project completion.
* `p i` is the duration of activity `i`;
* `E` is the arc set of the AoN project network `N`, and `δ i j` the (integer) weight of the arc
  `⟨i, j⟩ ∈ E`; the temporal constraint of the arc is `S_j - S_i ≥ δ_ij` (Eq. (1.2.1));
* `K` is the finite set `ℛ` of renewable resources, `R k ∈ ℕ` the capacity of resource `k` and
  `r i k ∈ ℤ≥0` the amount of resource `k` used by activity `i` while it is in progress. -/
structure Project (n : ℕ) (K : Type) [Fintype K] where
  p : Fin (n + 2) → ℕ
  E : Finset (Fin (n + 2) × Fin (n + 2))
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  r : Fin (n + 2) → K → ℕ
  R : K → ℕ

/-- A simple path in a directed graph on the node set `Fin (n + 2)`: a number `m` of arcs and an
injective sequence of nodes `v₀, v₁, …, v_m` (nodes do not repeat). The one-node sequence
(`m = 0`) is the path of length `0` from a node to itself. -/
def SimplePath (n : ℕ) : Type :=
  Σ m : Fin (n + 2), (Fin (m.1 + 1) ↪ Fin (n + 2))

noncomputable instance (n : ℕ) : Fintype (SimplePath n) :=
  inferInstanceAs (Fintype (Σ m : Fin (n + 2), (Fin (m.1 + 1) ↪ Fin (n + 2))))

/-- `P` is a simple path from node `i` to node `j` using only arcs of the arc set `A`: it starts
at `i`, ends at `j`, and each pair of consecutive nodes `⟨v_l, v_{l+1}⟩` is an arc of `A`. -/
def SimplePath.IsFromTo {n : ℕ} (A : Finset (Fin (n + 2) × Fin (n + 2))) (i j : Fin (n + 2))
    (P : SimplePath n) : Prop :=
  P.2 0 = i ∧ P.2 (Fin.last P.1.1) = j ∧
    ∀ l : Fin P.1.1, (P.2 l.castSucc, P.2 l.succ) ∈ A

/-- The length of a simple path with respect to arc weights `w`: the sum
`w v₀ v₁ + w v₁ v₂ + ⋯ + w v_{m-1} v_m` of the weights of its arcs (zero for `m = 0`). -/
def SimplePath.length {n : ℕ} (w : Fin (n + 2) → Fin (n + 2) → ℤ) (P : SimplePath n) : ℤ :=
  ∑ l : Fin P.1.1, w (P.2 l.castSucc) (P.2 l.succ)

/-- The standing assumptions of the book on a project (§1.1, p. 1 "n ≥ 1"; Remarks 1.1.2 and
p. 11; §2.1, p. 24):
1. there is at least one real activity (`n ≥ 1`);
2. the fictitious activities `0` and `n+1` have duration `0`, every real activity `1, …, n` has
   positive duration;
3. the project network has no loops;
4. `r_{0k} = r_{n+1,k} = 0` and `r_ik ≤ R_k` for all activities `i` and resources `k`;
5. for every node `i` the project network contains a path from `0` to `i` and a path from `i` to
   `n+1` (p. 11, consequence of Remarks 1.1.2). -/
def Project.StandingAssumptions {n : ℕ} {K : Type} [Fintype K] (P : Project n K) : Prop :=
  1 ≤ n ∧
  P.p 0 = 0 ∧ P.p (Fin.last (n + 1)) = 0 ∧
  (∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < P.p i) ∧
  (∀ e ∈ P.E, e.1 ≠ e.2) ∧
  (∀ k : K, P.r 0 k = 0 ∧ P.r (Fin.last (n + 1)) k = 0) ∧
  (∀ (i : Fin (n + 2)) (k : K), P.r i k ≤ P.R k) ∧
  (∀ i : Fin (n + 2), ∃ Q : SimplePath n, Q.IsFromTo P.E 0 i) ∧
  (∀ i : Fin (n + 2), ∃ Q : SimplePath n, Q.IsFromTo P.E i (Fin.last (n + 1)))

/-- A schedule (Definition 1.3.1, p. 10): real start times `S_i ≥ 0` for all activities, with
`S_0 = 0`. -/
def IsSchedule {n : ℕ} (S : Fin (n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ ∀ i, 0 ≤ S i

/-- A time-feasible schedule (Definition 1.3.1, p. 10): a schedule satisfying the temporal
constraints `S_j - S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` (Eq. (1.2.1)). The set `S_T`. -/
def Project.IsTimeFeasible {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (S : Fin (n + 2) → ℝ) : Prop :=
  IsSchedule S ∧ ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1

/-- The active set `A(S, t) = {i ∈ V | S_i ≤ t < S_i + p_i}` (Eq. (2.1.1), p. 25). -/
noncomputable def Project.activeSet {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (S : Fin (n + 2) → ℝ) (t : ℝ) : Finset (Fin (n + 2)) :=
  open Classical in Finset.univ.filter (fun i => S i ≤ t ∧ t < S i + P.p i)

/-- The amount `r_k(S, t) = ∑_{i ∈ A(S,t)} r_ik` of resource `k` used at time `t`
(Eq. (2.1.2), p. 25). -/
noncomputable def Project.usage {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ) : ℕ :=
  ∑ i ∈ P.activeSet S t, P.r i k

/-- A resource-feasible schedule (Definition 2.1.1, p. 25): a schedule satisfying the resource
constraints `r_k(S, t) ≤ R_k` for every resource `k` and **every** `t ≥ 0` (the reading of
(2.1.4) used by the proofs of the book and by Remark 2.3.11; the set `S_R`). -/
def Project.IsResourceFeasible {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (S : Fin (n + 2) → ℝ) : Prop :=
  IsSchedule S ∧ ∀ t : ℝ, 0 ≤ t → ∀ k : K, P.usage S k t ≤ P.R k

/-- A feasible schedule (Definition 2.1.1, p. 25): time-feasible and resource-feasible. The set
`S = S_T ∩ S_R`. -/
def Project.IsFeasible {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (S : Fin (n + 2) → ℝ) : Prop :=
  P.IsTimeFeasible S ∧ P.IsResourceFeasible S

/-- A forbidden set (Definition 2.3.9, Eq. (2.3.1), p. 34): a set `F ⊆ V` of activities with
`∑_{i ∈ F} r_ik > R_k` for some resource `k`. -/
def Project.IsForbidden {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (F : Finset (Fin (n + 2))) : Prop :=
  ∃ k : K, P.R k < ∑ i ∈ F, P.r i k

/-- A feasible set (Definition 2.3.9, p. 34): a set of activities that is not forbidden, i.e.
`∑_{i ∈ A} r_ik ≤ R_k` for every resource `k`. -/
def Project.IsFeasibleSet {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (A : Finset (Fin (n + 2))) : Prop :=
  ¬ P.IsForbidden A

/-- A minimal forbidden set (Definition 2.3.9, p. 34): a forbidden set no proper subset of which
is forbidden. -/
def Project.IsMinimalForbidden {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (F : Finset (Fin (n + 2))) : Prop :=
  Minimal P.IsForbidden F

/-- A delaying alternative for `F` (Definition 2.5.1, p. 46): a set `B ⊆ F` such that `F \ B` is a
feasible set. -/
def Project.IsDelayingAlternative {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (F B : Finset (Fin (n + 2))) : Prop :=
  B ⊆ F ∧ P.IsFeasibleSet (F \ B)

/-- A minimal delaying alternative for `F` (Definition 2.5.1, p. 46): a delaying alternative `B`
for `F` no proper subset `B' ⊂ B` of which is a delaying alternative for `F`. -/
def Project.IsMinimalDelayingAlternative {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (F B : Finset (Fin (n + 2))) : Prop :=
  Minimal (P.IsDelayingAlternative F) B

/-- A minimal delaying mode for `F` (Definition 2.5.6, p. 49): a pair `(i, B)` where `F` is a
forbidden set, `B` is a minimal delaying alternative for `F`, and `i ∈ F \ B`. -/
def Project.IsMinimalDelayingMode {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (F : Finset (Fin (n + 2))) (i : Fin (n + 2)) (B : Finset (Fin (n + 2))) : Prop :=
  P.IsForbidden F ∧ P.IsMinimalDelayingAlternative F B ∧ i ∈ F \ B

end ProjSchedTW.DelayingModes


