-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Model
-- name    : BernoulliQPTAS_Scheduling_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:21.622267+00:00
-- url     : https://prove2.me/theorems/be7b7091-4b24-4e32-b713-bfbf9b9ca492
-- title:
--   Bernoulli jobs, real-time causal trees, and independent private randomness
-- statement:
--   Let $N$ jobs be labeled by $0,\ldots,N-1$ and let $m$ machines have distinct labels. Job $j$ has positive rational size $p_j$ and rational probability $0<q_j\le1$. Its independent outcome is $X_j=p_j$ with probability $q_j$ and zero otherwise. The outcome vector has the finite product law
--
--   $$\Pr(\omega)=\prod_j q_j^{\mathbf1[\omega_j=1]}(1-q_j)^{\mathbf1[\omega_j=0]}.$$
--
--   A deterministic causal tree chooses a job, a machine, and a nonnegative real start time at each node. Only after the chosen job starts does the tree branch on its outcome. A state records the remaining jobs, current time, and individual machine availability times. Admissibility requires chronological starts on free machines and the start of every remaining job exactly once on every branch. Intentional idling and sequential starts at the same time are allowed. A private randomized policy is an arbitrary probability law on the Borel space of causal trees, independent of the job outcomes.
--
--   These objects provide the unrestricted scheduling benchmark. Non-idling, class ordering, optimality, and resource bounds are not fields of the policy type.
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Section 2, pp.6–7; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Mathlib

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators

namespace BernoulliQPTAS.Scheduling

/-- Section 2, p.6: input data. The number of jobs may be zero for subset instances. -/
structure Instance (N m : ℕ) where
  size : Fin N → ℚ
  probability : Fin N → ℚ
  size_pos : ∀ j, 0 < size j
  probability_pos : ∀ j, 0 < probability j
  probability_le_one : ∀ j, probability j ≤ 1

/-- A decision includes an arbitrary nonnegative real start time. -/
structure Action (N m : ℕ) where
  job : Fin N
  machine : Fin m
  time : ℝ≥0

/-- A finite causal deterministic policy. The two continuations are selected only
    after the outcome of the job in the node is revealed. -/
inductive PolicyTree (N m : ℕ) where
  | done : PolicyTree N m
  | start : Action N m → PolicyTree N m → PolicyTree N m → PolicyTree N m

/-- p.7: arbitrary residual states; machine releases are normalized at use. -/
structure State (N m : ℕ) where
  remaining : Finset (Fin N)
  now : ℝ≥0
  free : Fin m → ℝ≥0

/-- Finite independent Bernoulli outcomes, including zero-probability branches. -/
abbrev Outcome (N : ℕ) := Fin N → Bool

noncomputable def processing {N m : ℕ} (I : Instance N m) (j : Fin N)
    (positive : Bool) : ℝ≥0 :=
  if positive then ⟨(I.size j : ℝ), by exact_mod_cast (I.size_pos j).le⟩ else 0

noncomputable def chance {N m : ℕ} (I : Instance N m) (j : Fin N) : ℝ≥0 :=
  ⟨(I.probability j : ℝ), by exact_mod_cast (I.probability_pos j).le⟩

noncomputable def outcomeWeight {N m : ℕ} (I : Instance N m) (ω : Outcome N) : ℝ≥0 :=
  ∏ j, if ω j then chance I j else 1 - chance I j

/-- The explicit product law; no outcomes are supplied to a node before its action. -/
noncomputable def outcomeLaw {N m : ℕ} (I : Instance N m) : MeasureTheory.Measure (Outcome N) :=
  ∑ ω, (outcomeWeight I ω : ℝ≥0∞) • MeasureTheory.Measure.dirac ω

/-- Initially all machines are free. Subsets use the same labeled jobs and machines. -/
def initialState {N m : ℕ} (U : Finset (Fin N)) : State N m := ⟨U, 0, fun _ => 0⟩

noncomputable def minRelease {N m : ℕ} (s : State N m) : ℝ≥0 :=
  sInf (Set.range fun i => max (s.free i) s.now)

/-- An actual processing update, without rounded reservations. -/
noncomputable def advance {N m : ℕ} (I : Instance N m) (s : State N m)
    (a : Action N m) (positive : Bool) : State N m :=
  ⟨s.remaining.erase a.job, a.time,
    fun i => if i = a.machine then a.time + processing I a.job positive
      else max (s.free i) a.time⟩

/-- Physical feasibility, including deliberate idle time and chronological starts. -/
def Feasible {N m : ℕ} (s : State N m) (a : Action N m) : Prop :=
  a.job ∈ s.remaining ∧ s.now ≤ a.time ∧ s.free a.machine ≤ a.time

/-- All remaining jobs must be started exactly once, on every branch. -/
noncomputable def Admissible {N m : ℕ} (I : Instance N m) :
    State N m → PolicyTree N m → Prop
  | s, .done => s.remaining = ∅
  | s, .start a z p => Feasible s a ∧
      Admissible I (advance I s a false) z ∧ Admissible I (advance I s a true) p

noncomputable def NonIdling {N m : ℕ} (I : Instance N m) :
    State N m → PolicyTree N m → Prop
  | _, .done => True
  | s, .start a z p => a.time = minRelease s ∧
      NonIdling I (advance I s a false) z ∧ NonIdling I (advance I s a true) p

/-- Realized actions: the policy only branches on outcomes already revealed. -/
def trace {N m : ℕ} : PolicyTree N m → Outcome N → List (Action N m)
  | .done, _ => []
  | .start a z p, ω => a :: (if ω a.job then trace p ω else trace z ω)

/-- A finite coding by node addresses, giving the usual Borel structure on trees
    with discrete job/machine labels and nonnegative real time coordinates. -/
def nodeAt {N m : ℕ} : PolicyTree N m → List Bool → Option (Action N m)
  | .done, _ => none
  | .start a _ _, [] => some a
  | .start _ z p, b :: bs => if b then nodeAt p bs else nodeAt z bs

def treeCode {N m : ℕ} (t : PolicyTree N m) :
    List Bool → Bool × ℕ × ℕ × ℝ≥0 :=
  fun address => match nodeAt t address with
    | none => (false, 0, 0, 0)
    | some a => (true, a.job.val, a.machine.val, a.time)

instance treeMeasurableSpace {N m : ℕ} : MeasurableSpace (PolicyTree N m) :=
  MeasurableSpace.comap treeCode inferInstance

/-- Independent private randomness is a probability law on causal deterministic
    trees, chosen before the independent job outcomes. No support restriction to
    finite mixtures, rational times, or non-idling policies is imposed. -/
structure RandomPolicy (N m : ℕ) where
  law : MeasureTheory.Measure (PolicyTree N m)
  probability : MeasureTheory.IsProbabilityMeasure law

end BernoulliQPTAS.Scheduling


