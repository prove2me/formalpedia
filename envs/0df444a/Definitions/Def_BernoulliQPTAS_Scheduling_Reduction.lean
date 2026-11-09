-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Reduction
-- name    : BernoulliQPTAS_Scheduling_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:50.61784+00:00
-- url     : https://prove2.me/theorems/4177803c-14b4-40f9-9737-f7d839197972
-- title:
--   The large/small/medium wrapper with arbitrary randomized medium policy
-- statement:
--   For $2\le m<N$ and $0<\varepsilon\le1$, put $P=\sum_jq_jp_j$ and
--
--   $$T=NP/\varepsilon,\qquad\sigma=\varepsilon P/N^2,\qquad D=\varepsilon P/N.$$
--
--   Large jobs have $p_j\ge T$, small jobs have $p_j<\sigma$, and medium jobs are the others. Given a policy $A$ for medium jobs, the specified wrapper tests the large jobs on one machine at time zero until the first positive outcome. If one is positive, it immediately switches to ordinary list scheduling of all remaining jobs. If all large jobs are zero, it list-schedules the small jobs, waits until $D$, and runs $A$ with every start time shifted by $D$. The list order is a parameter, an arbitrary fixed list of all jobs; machine ties use machine labels. Empty lists and an empty medium set are handled by the same definitions.
--
--   For randomized $A$, the wrapper applies this deterministic transformation to each privately sampled causal tree. The associated law is its pushforward; Theorem 3.1 explicitly asserts that it is a probability law on admissible policies, so the default zero value of a nonmeasurable measure map cannot establish its conclusion.
--
--   This module covers the Section 3 reduction. Geometric rounding and the charged computation of Section 4.5 are in the Program definition.
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Section 3, pp.9–10; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

def meanRat {N m : ℕ} (I : Instance N m) : ℚ := ∑ j, I.probability j * I.size j

noncomputable def largeThreshold {N m : ℕ} (I : Instance N m) (ε : ℝ) : ℝ :=
  N * (meanRat I : ℝ) / ε

noncomputable def smallThreshold {N m : ℕ} (I : Instance N m) (ε : ℝ) : ℝ :=
  ε * (meanRat I : ℝ) / (N : ℝ) ^ 2

noncomputable def largeJobs {N m : ℕ} (I : Instance N m) (ε : ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun j => largeThreshold I ε ≤ (I.size j : ℝ)

noncomputable def smallJobs {N m : ℕ} (I : Instance N m) (ε : ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun j => (I.size j : ℝ) < smallThreshold I ε

noncomputable def mediumJobs {N m : ℕ} (I : Instance N m) (ε : ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ \ (largeJobs I ε ∪ smallJobs I ε)

/-- Attach a continuation after every leaf; no job outcome is inspected early. -/
def appendTree {N m : ℕ} : PolicyTree N m → PolicyTree N m → PolicyTree N m
  | .done, a => a
  | .start x z p, a => .start x (appendTree z a) (appendTree p a)

def shiftTree {N m : ℕ} (D : ℝ≥0) : PolicyTree N m → PolicyTree N m
  | .done => .done
  | .start a z p => .start ⟨a.job, a.machine, D + a.time⟩ (shiftTree D z) (shiftTree D p)

noncomputable def earliestMachine {N m : ℕ} (s : State N m) : Option (Fin m) :=
  ((List.finRange m).mergeSort (fun i j => decide
    (max (s.free i) s.now < max (s.free j) s.now ∨
      (max (s.free i) s.now = max (s.free j) s.now ∧ i.val ≤ j.val)))).head?

/-- Ordinary fixed-order list scheduling, using actual processing times. -/
noncomputable def listSchedule {N m : ℕ} (I : Instance N m) :
    List (Fin N) → State N m → PolicyTree N m
  | [], _ => .done
  | j :: jobs, s => match earliestMachine s with
      | none => .done
      | some i =>
          let a : Action N m := ⟨j, i, minRelease s⟩
          .start a (listSchedule I jobs (advance I s a false))
            (listSchedule I jobs (advance I s a true))

/-- Section 3's wrapper: one positive large job switches to ordinary list
    scheduling of the remaining jobs in the fixed `order`. If all large jobs are zero,
    finish the small jobs and wait until D. -/
noncomputable def testLarge {N m : ℕ} (I : Instance N m) (i : Fin m) (order : List (Fin N))
    (small : List (Fin N)) (D : ℝ≥0) (A : PolicyTree N m) :
    List (Fin N) → State N m → PolicyTree N m
  | [], s => appendTree (listSchedule I small s) (shiftTree D A)
  | j :: jobs, s =>
      let a : Action N m := ⟨j, i, 0⟩
      let positiveState := advance I s a true
      .start a (testLarge I i order small D A jobs (advance I s a false))
        (listSchedule I (order.filter (· ∈ positiveState.remaining)) positiveState)

/-- p.9, "in any fixed order": `order` is a fixed list of all jobs. -/
noncomputable def reductionWrapper {N m : ℕ} (I : Instance N m) (ε : ℝ) (order : List (Fin N))
    (A : PolicyTree N m) : PolicyTree N m :=
  match (List.finRange m).head? with
  | none => .done
  | some i => testLarge I i order (order.filter (· ∈ smallJobs I ε))
      (Real.toNNReal (ε * (meanRat I : ℝ) / N)) A
      (order.filter (· ∈ largeJobs I ε)) (initialState Finset.univ)

/-- Pushforward of private coins through the specified wrapper. Probability and
    measurability are conclusions to establish, rather than supplied certificates. -/
noncomputable def wrapperLaw {N m : ℕ} (I : Instance N m) (ε : ℝ) (order : List (Fin N))
    (A : RandomPolicy N m) : MeasureTheory.Measure (PolicyTree N m) :=
  A.law.map (reductionWrapper I ε order)

noncomputable def wrapperCost {N m : ℕ} (I : Instance N m) (ε : ℝ) (order : List (Fin N))
    (A : RandomPolicy N m) : ℝ≥0∞ :=
  ∫⁻ t, treeCost I t ∂(wrapperLaw I ε order A)

end BernoulliQPTAS.Scheduling


