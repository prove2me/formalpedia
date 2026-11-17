-- Prove2me | Definitions.Def_TemporalAgg_Supplement_jmState
-- name    : TemporalAgg_Supplement_jmState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:18:29.818784+00:00
-- url     : https://prove2.me/theorems/ca1ef553-b133-4d19-981d-192732f175d1
-- title:
--   The job–machine setting under proactive resampling (Theorem B.1)
-- statement:
--   There are $n$ jobs and $M$ machines. A **routine** $\{j,x_1,\dots,x_k\}$ contains exactly one job $j$ and represents that $j$ can be assigned to the machines $x_1,\dots,x_k$. Every job is assigned to exactly one of its routines and uses its machines. An **instance** fixes the routines, a machine $x^\star$, a horizon $T$ and a deterministic adaptive adversary.
--
--   * **Time 0.** Every job is assigned to a uniformly random routine (not an adversarial sample).
--   * **Time $t\ge1$.** Seeing the whole history, the adversary deletes one machine $x_t$, which deletes every routine containing it. Every job that used $x_t$ is assigned to a uniformly random one of its remaining routines (an adversarial sample at time $t$). Then proactive resampling reassigns, uniformly among its current routines, every job with an adversarial sample at some $s<t$ with $t=s+2^i$.
--
--   Let $G_t$ be the set of routines alive at time $t$ and $R_t(u)$ the routines of $G_t$ containing $u$ (a job or a machine). The **load** $\mathrm{load}_t(x)$ is the number of jobs using machine $x$ at time $t$, and
--
--   $$
--   \mathrm{target}_t(x)=\sum_{j}\frac{|R_t(x)\cap R_t(j)|}{|R_t(j)|}
--   $$
--
--   is the expected load of $x$ if all jobs were sampled simultaneously at time $t$. An instance is **valid** if, on every history, each of the steps $1,\dots,T$ deletes a machine not deleted before and every job keeps at least one routine at all times $t\le T$.
--
--   The law is realized by independent uniform numbers $\xi_{j,t}\in\{0,\dots,N-1\}$, $N=|\text{routines}|!$, driving the (re)assignment of job $j$ at time $t$.
--
--   **Formalization Note** A job both forced and proactively resampled at the same step is drawn once. A job with $R_t(j)=\emptyset$ would contribute $0$ to the target; valid instances never empty a job.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), App. B.1, p.38 (the setting, load and target); §1.3, p.5 (proactive resampling)

import Mathlib
import Definitions.Def_TemporalAgg_Supplement_ProactiveDue

namespace TemporalAgg.Supplement

/-! The job–machine setting of Bhattacharya, Saranurak and Sukprasert under proactive resampling
(Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries*,
STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, App. B.1, p.38).

Jobs are `Fin n`, machines `Fin M`. A routine `{j, x₁, …, x_k}` contains exactly one job `j` and
represents that `j` can be assigned to the machines `x₁, …, x_k`; it is the pair
`(j, {x₁, …, x_k})`. Every job is assigned to exactly one of its routines and uses its machines. -/

/-- A routine: its job and its set of machines. -/
abbrev Routine (n M : ℕ) := Fin n × Finset (Fin M)

/-- An assignment of every job to a routine. -/
abbrev Assignment (n M : ℕ) := Fin n → Routine n M

/-- An instance with `n` jobs: `M` machines, the initial set of routines, the machine `x⋆`, the
horizon `T` (number of deletions), and a deterministic adaptive adversary which at time `t ≥ 1`,
seeing the history `h` (the assignments at the end of steps `0, …, t−1`, a list of length `t`),
deletes the machine `delete h`. -/
structure JMInstance (n : ℕ) where
  M : ℕ
  routines : Finset (Routine n M)
  xstar : Fin M
  T : ℕ
  delete : List (Assignment n M) → Fin M

/-- The routines surviving the deletion of the machines `del`: those containing none of them. -/
def liveRoutines {n M : ℕ} (routines : Finset (Routine n M)) (del : Finset (Fin M)) :
    Finset (Routine n M) :=
  routines.filter (fun r => Disjoint r.2 del)

/-- `R(j)`: the routines of `live` containing the job `j`. -/
def jobRoutines {n M : ℕ} (live : Finset (Routine n M)) (j : Fin n) : Finset (Routine n M) :=
  live.filter (fun r => r.1 = j)

/-- A routine of `j` among `live` chosen by the number `r`: entry `r mod |R(j)|` of a fixed
enumeration of `R(j)`; `dflt` if `j` has no routine left.

**Formalization Note** If `r` is uniform on `{0, …, N−1}` with `|R(j)| ∣ N`, this is a uniformly
random routine of `j`. The process uses `N = |routines|!`, which every `1 ≤ |R(j)| ≤ |routines|`
divides. -/
noncomputable def pickRoutine {n M : ℕ} (live : Finset (Routine n M)) (j : Fin n) (r : ℕ)
    (dflt : Routine n M) : Routine n M :=
  let l := (jobRoutines live j).toList
  if h : l.length = 0 then dflt else l.get ⟨r % l.length, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩

/-- State at the end of a time step: deleted machines, current assignment, adversarial sample times
of every job, and the history of assignments. -/
structure JMState (n M : ℕ) where
  deleted : Finset (Fin M)
  asg : Assignment n M
  adv : Fin n → Finset ℕ
  hist : List (Assignment n M)

/-- Time 0: every job picks a uniformly random routine (driven by `ξ j 0`). Not adversarial: no
proactive schedule starts. -/
noncomputable def jmInit {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) : JMState n I.M :=
  let a : Assignment n I.M := fun j => pickRoutine I.routines j (ξ j 0) (j, ∅)
  ⟨∅, a, fun _ => ∅, [a]⟩

/-- One time step `t ≥ 1` (p.38): the adversary deletes the machine `x_t`, which deletes every
routine containing it; every job that used `x_t` is resampled, i.e. assigned to a uniformly random
one of its remaining routines (an adversarial sample at time `t`); then proactive resampling
resamples, uniformly among its current routines, every job with an adversarial sample at some
`s < t` with `t = s + 2ⁱ`. Resamples are driven by `ξ j t`.

**Formalization Note** A job both forced and proactively resampled at `t` is drawn once (two fresh
uniform draws from the same set have the law of one). -/
noncomputable def jmStep {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) (t : ℕ)
    (s : JMState n I.M) : JMState n I.M := by
  classical
  exact
    let x := I.delete s.hist
    let del' := insert x s.deleted
    let live := liveRoutines I.routines del'
    let forced : Fin n → Prop := fun j => x ∈ (s.asg j).2
    let adv' : Fin n → Finset ℕ := fun j => if forced j then insert t (s.adv j) else s.adv j
    let a' : Assignment n I.M := fun j =>
      if forced j ∨ ProactiveDue (s.adv j) t then pickRoutine live j (ξ j t) (s.asg j) else s.asg j
    ⟨del', a', adv', s.hist ++ [a']⟩

/-- **The job–machine process under proactive resampling.** `jmState I ξ t` is the state at the end
of time step `t`.

**Formalization Note** (probabilistic model) With all `ξ j t` independent uniform on
`Fin |routines|!`, every (re)sample is, given the history, a uniformly random current routine of
the job, as in the paper. -/
noncomputable def jmState {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) : ℕ → JMState n I.M
  | 0 => jmInit I ξ
  | t + 1 => jmStep I ξ (t + 1) (jmState I ξ t)

/-- `G_t`: the routines alive at the end of time step `t`. -/
noncomputable def jmLive {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) (t : ℕ) : Finset (Routine n I.M) :=
  liveRoutines I.routines (jmState I ξ t).deleted

/-- `load_t(x)`: the number of jobs using machine `x` at time `t`. -/
noncomputable def jmLoad {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) (t : ℕ) (x : Fin I.M) :
    ℕ := by
  classical
  exact (Finset.univ.filter (fun j => x ∈ ((jmState I ξ t).asg j).2)).card

/-- `target_t(x) = ∑_{j ∈ J} |R_t(x) ∩ R_t(j)| / |R_t(j)|` (p.38), the expected load of `x` if all
jobs were sampled simultaneously at time `t`; `R_t(·)` are routine sets of `G_t`.

**Formalization Note** A job with `R_t(j) = ∅` contributes `0` (division by zero); the instances of
Theorem B.1 are required never to empty a job. -/
noncomputable def jmTarget {n : ℕ} (I : JMInstance n) (ξ : Fin n → ℕ → ℕ) (t : ℕ) (x : Fin I.M) :
    ℝ :=
  ∑ j, (((jobRoutines (jmLive I ξ t) j).filter (fun r => x ∈ r.2)).card : ℝ) /
    ((jobRoutines (jmLive I ξ t) j).card : ℝ)

/-- Validity of an instance on every history: at every step `t = 1, …, T` the adversary deletes a
machine not deleted before (one deletion per time step), and every job keeps at least one routine
at all times `t ≤ T`. -/
def JMValid {n : ℕ} (I : JMInstance n) : Prop :=
  ∀ ξ : Fin n → ℕ → ℕ,
    (∀ t < I.T, I.delete (jmState I ξ t).hist ∉ (jmState I ξ t).deleted) ∧
    (∀ t ≤ I.T, ∀ j, (jobRoutines (jmLive I ξ t) j).Nonempty)

/-- The randomness of the first `T + 1` time steps, `η j s ∈ Fin N` for `s ≤ T`, extended by `0`. -/
def jmRand {n T N : ℕ} (η : Fin n → Fin (T + 1) → Fin N) : Fin n → ℕ → ℕ :=
  fun j s => if h : s < T + 1 then (η j ⟨s, h⟩ : ℕ) else 0

end TemporalAgg.Supplement


