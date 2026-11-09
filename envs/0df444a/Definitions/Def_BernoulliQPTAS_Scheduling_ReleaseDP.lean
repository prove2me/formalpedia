-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP
-- name    : BernoulliQPTAS_Scheduling_ReleaseDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:40.363484+00:00
-- url     : https://prove2.me/theorems/f0a385fd-a7eb-44f1-96c5-1c30e36ebdad
-- title:
--   Rounded machine releases and the exact acyclic Bellman recursion
-- statement:
--   Fix an integer $K\ge1$ and put $\gamma=1+1/K$ and $g_p=p/K$. A positive job started at $s$ completes at $s+p$ but reserves its machine until
--
--   $$R_p(s)=g_p\bigl(\lceil s/g_p\rceil+K\bigr).$$
--
--   A zero job leaves its machine available immediately. Grid-non-idling means starting at the minimum current release time. The logical state consists of the sorted absolute rational release vector and the remaining suffix of each class order. Remaining suffixes are encoded by labeled remaining-job sets reachable through class-first removals. The Bellman value is zero when no jobs remain and otherwise minimizes
--
--   $$\ell_1+q_jp_j+(1-q_j)V(\ell,\nu-e_c)+q_jV(\ell^{(c)},\nu-e_c),\qquad j=j_c(\nu),$$
--
--   over eligible class heads. Values use exact rational arithmetic; ties are broken by job label. Reachability includes every eligible class action and both outcomes, independently of which action eventually minimizes the value. The semantic minimizing policy maintains physical machine labels and breaks equal-release ties by label.
--
--   This module defines the mathematical recursion and its semantic execution. It does not implement memoized table preprocessing or claim a computation-time bound.
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Section 4.1–4.4, pp.10–13; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

/-- Section 4.1: this rounds machine availability, not job completion. -/
noncomputable def reuseReal (p : ℝ) (K : ℕ) (s : ℝ) : ℝ :=
  (p / K) * ((⌈s / (p / K)⌉ : ℤ) + (K : ℝ))

def reuseRat (p : ℚ) (K : ℕ) (s : ℚ) : ℚ :=
  (p / K) * ((⌈s / (p / K)⌉ : ℤ) + (K : ℚ))

noncomputable def reserveAdvance {N m : ℕ} (I : Instance N m) (K : ℕ)
    (s : State N m) (a : Action N m) (positive : Bool) : State N m :=
  ⟨s.remaining.erase a.job, a.time, fun i =>
    if i = a.machine then
      if positive then Real.toNNReal (reuseReal (I.size a.job) K a.time) else a.time
    else max (s.free i) a.time⟩

noncomputable def ReuseAdmissible {N m : ℕ} (I : Instance N m) (K : ℕ) :
    State N m → PolicyTree N m → Prop
  | s, .done => s.remaining = ∅
  | s, .start a z p => Feasible s a ∧
      ReuseAdmissible I K (reserveAdvance I K s a false) z ∧
      ReuseAdmissible I K (reserveAdvance I K s a true) p

noncomputable def GridNonIdling {N m : ℕ} (I : Instance N m) (K : ℕ) :
    State N m → PolicyTree N m → Prop
  | _, .done => True
  | s, .start a z p => a.time = minRelease s ∧
      GridNonIdling I K (reserveAdvance I K s a false) z ∧
      GridNonIdling I K (reserveAdvance I K s a true) p

/-- Sorted absolute rational releases and a suffix of each class's fixed job order.
    The suffix invariant is established by the transitions from the initial state;
    it is not a supplied counting certificate. -/
structure DPState (N : ℕ) where
  releases : List ℚ
  remaining : Finset (Fin N)
  deriving DecidableEq

def sortedReleases (xs : List ℚ) : List ℚ := xs.mergeSort (fun x y => decide (x ≤ y))

def dpInitial (N m : ℕ) (U : Finset (Fin N)) : DPState N :=
  ⟨List.replicate m 0, U⟩

def decisionTime {N : ℕ} (s : DPState N) : ℚ := s.releases.headD 0

noncomputable def eligible {N m : ℕ} (I : Instance N m) (s : DPState N) : Finset (Fin N) := by
  classical
  exact s.remaining.filter fun j => ClassFirst I s.remaining j

def dpAfter {N m : ℕ} (I : Instance N m) (K : ℕ) (s : DPState N)
    (j : Fin N) (positive : Bool) : DPState N :=
  ⟨if positive then sortedReleases (reuseRat (I.size j) K (decisionTime s) :: s.releases.tail)
    else s.releases, s.remaining.erase j⟩

/-- Minimize exact rational values, breaking ties by the job label. -/
def bestChoice {N : ℕ} (value : Fin N → ℚ) (jobs : List (Fin N)) : Option (Fin N × ℚ) :=
  jobs.foldl (fun best j => match best with
    | none => some (j, value j)
    | some (i, v) => if value j < v ∨ (value j = v ∧ j.val < i.val)
        then some (j, value j) else some (i, v)) none

def transitionValue {N m : ℕ} (I : Instance N m) (K : ℕ)
    (value : DPState N → ℚ) (s : DPState N) (j : Fin N) : ℚ :=
  decisionTime s + I.probability j * I.size j +
    (1 - I.probability j) * value (dpAfter I K s j false) +
    I.probability j * value (dpAfter I K s j true)

/-- Section 4.3's well-founded recursion. At a reachable state the recursion
    depth is exactly the number of remaining jobs. -/
noncomputable def bellman {N m : ℕ} (I : Instance N m) (K : ℕ) :
    ℕ → DPState N → ℚ
  | 0, _ => 0
  | fuel + 1, s =>
      ((bestChoice (transitionValue I K (bellman I K fuel) s) (eligible I s).toList).map Prod.snd).getD 0

noncomputable def minimizingJob {N m : ℕ} (I : Instance N m) (K fuel : ℕ)
    (s : DPState N) : Option (Fin N) :=
  (bestChoice (transitionValue I K (bellman I K fuel) s) (eligible I s).toList).map Prod.fst

/-- The full reachable graph includes every eligible class and both outcomes. -/
noncomputable def reachable {N m : ℕ} (I : Instance N m) (K : ℕ) :
    ℕ → DPState N → Finset (DPState N)
  | 0, s => {s}
  | fuel + 1, s => {s} ∪ (eligible I s).biUnion fun j =>
      reachable I K fuel (dpAfter I K s j false) ∪ reachable I K fuel (dpAfter I K s j true)

noncomputable def releaseTimes {N m : ℕ} (I : Instance N m) (K : ℕ) : Finset ℚ :=
  (reachable I K N (dpInitial N m Finset.univ)).biUnion fun s => s.releases.toFinset

noncomputable def releaseVectorsAt {N m : ℕ} (I : Instance N m) (K : ℕ) (t : ℚ) : Finset (List ℚ) :=
  ((reachable I K N (dpInitial N m Finset.univ)).filter fun s => decisionTime s = t).image DPState.releases

def sizeClasses {N m : ℕ} (I : Instance N m) : Finset ℚ := Finset.univ.image I.size

def classCount {N m : ℕ} (I : Instance N m) (p : ℚ) : ℕ :=
  (Finset.univ.filter fun j => I.size j = p).card

/-- Physical labels accompany sorted releases during execution. They are not
    restrictions on which identical machine the benchmark can use. -/
structure PhysicalDPState (N m : ℕ) where
  free : Fin m → ℚ
  remaining : Finset (Fin N)

def logicalState {N m : ℕ} (s : PhysicalDPState N m) : DPState N :=
  ⟨sortedReleases ((List.finRange m).map s.free), s.remaining⟩

def firstMachine {N m : ℕ} (s : PhysicalDPState N m) : Option (Fin m) :=
  ((List.finRange m).mergeSort (fun i j => decide
    (s.free i < s.free j ∨ (s.free i = s.free j ∧ i.val ≤ j.val)))).head?

def physicalAfter {N m : ℕ} (I : Instance N m) (K : ℕ)
    (s : PhysicalDPState N m) (j : Fin N) (i : Fin m) (positive : Bool) : PhysicalDPState N m :=
  ⟨Function.update s.free i (if positive then reuseRat (I.size j) K (s.free i) else s.free i),
    s.remaining.erase j⟩

/-- Semantic execution of the minimizing decisions. This is not a preprocessing
    implementation or a charged-time program. -/
noncomputable def dpTree {N m : ℕ} (I : Instance N m) (K : ℕ) :
    ℕ → PhysicalDPState N m → PolicyTree N m
  | 0, _ => .done
  | fuel + 1, s =>
      match minimizingJob I K fuel (logicalState s), firstMachine s with
      | some j, some i => .start ⟨j, i, Real.toNNReal (s.free i)⟩
          (dpTree I K fuel (physicalAfter I K s j i false))
          (dpTree I K fuel (physicalAfter I K s j i true))
      | _, _ => .done

noncomputable def dpPolicy {N m : ℕ} (I : Instance N m) (K : ℕ) : PolicyTree N m :=
  dpTree I K N ⟨fun _ => 0, Finset.univ⟩

/-- Lemma 4.3's second sentence: `t` chooses, in each state, a class attaining the minimum
    of the recursion, starts its first remaining job, and uses a machine of minimum
    release. Ties may be broken in any way, and differently in different states. -/
noncomputable def ChoosesMinimum {N m : ℕ} (I : Instance N m) (K : ℕ) :
    ℕ → PhysicalDPState N m → PolicyTree N m → Prop
  | _, s, .done => s.remaining = ∅
  | 0, _, .start _ _ _ => False
  | fuel + 1, s, .start a z p =>
      a.time = Real.toNNReal (s.free a.machine) ∧
      (∀ i, s.free a.machine ≤ s.free i) ∧
      a.job ∈ eligible I (logicalState s) ∧
      (∀ j ∈ eligible I (logicalState s),
        transitionValue I K (bellman I K fuel) (logicalState s) a.job ≤
          transitionValue I K (bellman I K fuel) (logicalState s) j) ∧
      ChoosesMinimum I K fuel (physicalAfter I K s a.job a.machine false) z ∧
      ChoosesMinimum I K fuel (physicalAfter I K s a.job a.machine true) p

noncomputable def reuseOptimum {N m : ℕ} (I : Instance N m) (K : ℕ) : ℝ≥0∞ :=
  ⨅ π : {π : RandomPolicy N m // ∀ᵐ t ∂π.law,
    ReuseAdmissible I K (initialState Finset.univ) t ∧
    GridNonIdling I K (initialState Finset.univ) t ∧
    RespectsClasses I (initialState Finset.univ) t}, randomCost I π.val

end BernoulliQPTAS.Scheduling


