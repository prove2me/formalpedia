-- Prove2me | Definitions.Def_TemporalAgg_IsGTARun
-- name    : TemporalAgg_IsGTARun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:14.148096+00:00
-- url     : https://prove2.me/theorems/dc3b9940-e2ad-4ddc-8e9a-70122efe0325
-- title:
--   Algorithm 1 — Greedy Temporal Aggregation (GTA) and its runs
-- statement:
--   There are $n$ objects and discrete time steps $t=0,1,2,\dots$. A **state** records, for every object $u$, the time step $\mathrm{last}(u)$ at which its current realization was sampled. The **group** of a time step $s$ is $\{u : \mathrm{last}(u)=s\}$, and $g(s)$ denotes its size.
--
--   1. **Adversarial samples.** At time $t\ge1$ the adversary samples a set $A_t$ of objects: $\mathrm{last}(u)$ becomes $t$ for $u\in A_t$ and is unchanged otherwise.
--   2. **Loop condition.** Two time steps $t_1\ne t_2$ are a **candidate pair** if both groups are nonempty and their sizes differ by at most a factor of $2$: $g(t_1)\le 2g(t_2)$ and $g(t_2)\le 2g(t_1)$. A state with no candidate pair is **stable**.
--   3. **Loop iteration.** For a candidate pair, all objects of both groups are sampled at the current time $t$ (they join the group of $t$; one of $t_1,t_2$ may be $t$ itself). The iteration costs $g(t_1)+g(t_2)$ algorithmic samples.
--   4. **One time step of GTA.** After the adversary's samples, the loop is iterated, choosing any candidate pair each time, until the state is stable. The algorithmic samples of the step are the total cost of its iterations.
--   5. **Run.** A run against the sequence $(A_t)_{t\ge1}$ is a sequence of states $\mathrm{last}_0,\mathrm{last}_1,\dots$ and counts $\mathrm{alg}_1,\mathrm{alg}_2,\dots$ such that $\mathrm{last}_0\equiv0$ (all objects are sampled at time 0) and, for every $t\ge1$, $\mathrm{last}_t$ and $\mathrm{alg}_t$ are the outcome of one time step of GTA from $\mathrm{last}_{t-1}$.
--
--   This is the algorithm of the mission. It keeps the realizations of all objects concentrated on few time steps, which is the temporal aggregation principle.
--
--   **Formalization Note** The candidate pair is chosen existentially: a run is any resolution of the nondeterministic choice in Algorithm 1, and the theorems quantify over all runs. Groups in the loop condition must be nonempty; two empty groups would satisfy "differ by at most a factor of 2" forever, contradicting the paper's "so the loop terminates". The sampling of every object at time $0$ is not counted as adversarial or algorithmic. The module also defines the group size, the adversary's step, the candidate pair, the merge, one loop iteration (on pairs of a state and a sample counter), stability and one time step.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.2, p.3; Algorithm 1 and §3.1, p.16

import Mathlib

namespace TemporalAgg

/-! Greedy Temporal Aggregation (Haeupler, Paramonov, *Temporal Aggregation: Maintaining
Randomness against Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 42ebf866…, §1.2 p.3, §1.4 p.7, Algorithm 1 and §3.1, p.16).

A state of the process is `last : Fin n → ℕ`: `last u` is the time step at which the current
realization of object `u` was sampled. The *group* of a time step `s` is `{u | last u = s}`. -/

/-- Size of the group of time step `s`: the number of objects whose current realization was
sampled at time `s` (§3.1, p.16). -/
def groupSize {n : ℕ} (last : Fin n → ℕ) (s : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => last u = s)).card

/-- The adversary's samples at time `t` (§1.2, p.3): every object of `A` is sampled at time `t`,
the others keep their realizations. -/
def adversaryStep {n : ℕ} (t : ℕ) (A : Finset (Fin n)) (last : Fin n → ℕ) : Fin n → ℕ :=
  fun u => if u ∈ A then t else last u

/-- The loop condition of Algorithm 1 (p.16) for the pair `t₁ ≠ t₂`: both groups are nonempty
and their sizes differ by at most a factor of 2.

**Formalization Note** Groups are required to be nonempty: two empty groups would satisfy
"differ by at most a factor of 2", sampling them changes nothing, and the loop would never stop,
contradicting "so the loop terminates" and "the sizes of any two nonempty groups differ by more
than a factor of 2" (p.16). "At most a factor of 2" is `a ≤ 2b ∧ b ≤ 2a`. -/
def MergeCandidate {n : ℕ} (last : Fin n → ℕ) (t₁ t₂ : ℕ) : Prop :=
  t₁ ≠ t₂ ∧ 0 < groupSize last t₁ ∧ 0 < groupSize last t₂ ∧
    groupSize last t₁ ≤ 2 * groupSize last t₂ ∧ groupSize last t₂ ≤ 2 * groupSize last t₁

/-- Sampling all objects of the groups of `t₁` and `t₂` at the current time `t`: they move into
the group of `t` (p.16; one of `t₁, t₂` may be `t` itself). -/
def mergeInto {n : ℕ} (t t₁ t₂ : ℕ) (last : Fin n → ℕ) : Fin n → ℕ :=
  fun u => if last u = t₁ ∨ last u = t₂ then t else last u

/-- One iteration of the loop of Algorithm 1 at time `t`, on pairs (state, number of algorithmic
samples so far): some candidate pair `t₁ ≠ t₂` is chosen (any one), all objects of both groups
are sampled, and the counter grows by the two group sizes.

**Formalization Note** The pair is chosen existentially, so the relation covers every way of
resolving the nondeterministic choice in Algorithm 1. -/
def MergeStep {n : ℕ} (t : ℕ) (a b : (Fin n → ℕ) × ℕ) : Prop :=
  ∃ t₁ t₂, MergeCandidate a.1 t₁ t₂ ∧ b.1 = mergeInto t t₁ t₂ a.1 ∧
    b.2 = a.2 + groupSize a.1 t₁ + groupSize a.1 t₂

/-- The loop of Algorithm 1 has stopped: no pair of time steps satisfies its condition. -/
def Stable {n : ℕ} (last : Fin n → ℕ) : Prop :=
  ∀ t₁ t₂, ¬ MergeCandidate last t₁ t₂

/-- One time step `t ≥ 1` of GTA: starting from `last`, the adversary samples `A`, then the loop
runs (some finite sequence of iterations) until it stops in `last'`; `c` is the number of
algorithmic samples of this step. -/
def GTAStep {n : ℕ} (t : ℕ) (A : Finset (Fin n)) (last last' : Fin n → ℕ) (c : ℕ) : Prop :=
  Relation.ReflTransGen (MergeStep t) (adversaryStep t A last, 0) (last', c) ∧ Stable last'

/-- A run of Greedy Temporal Aggregation against the adversarial sample sets `A t` (`t ≥ 1`):
`last t` is the state at the end of time step `t` and `alg t` the number of algorithmic samples
at time `t`.

**Formalization Note** At time 0 all objects are sampled (§1.2, p.3), so `last 0` is constantly
`0`; `A 0` and `alg 0` play no role (the time-0 sampling is neither adversarial nor algorithmic in
the counts). `IsGTARun` is a predicate, not a function: every resolution of the choice of merge
pair in Algorithm 1 is a run. -/
def IsGTARun {n : ℕ} (A : ℕ → Finset (Fin n)) (last : ℕ → Fin n → ℕ) (alg : ℕ → ℕ) : Prop :=
  last 0 = (fun _ => 0) ∧
    ∀ t : ℕ, GTAStep (t + 1) (A (t + 1)) (last t) (last (t + 1)) (alg (t + 1))

end TemporalAgg


