-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Objective
-- name    : BernoulliQPTAS_Scheduling_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:01.285542+00:00
-- url     : https://prove2.me/theorems/1507e581-8b7e-4f2f-8025-dd5c447003e8
-- title:
--   Extended expected cost, unrestricted optimum, and class ordering
-- statement:
--   For a causal tree $T$, let $S_j^T$ and $C_j^T=S_j^T+X_j$ be actual start and completion times. A randomized policy $\pi$ is a probability law on such trees. Define
--
--   $$\operatorname{cost}(T)=\sum_\omega\Pr(\omega)\sum_j C_j^T(\omega),\qquad \operatorname{cost}(\pi)=\int \operatorname{cost}(T)\,d\pi(T),\qquad \operatorname{OPT}(s)=\inf_{\pi\text{ admissible from }s}\operatorname{cost}(\pi).$$
--
--   Costs and the infimum take values in the extended nonnegative reals. Consequently an infinite expected cost remains infinite. Subset instances retain the original labels and machines but change the remaining-job set. Write $P(U)=\sum_{j\in U}q_jp_j$. Equal-size classes are ordered by probability and then job label. The finite family of deterministic non-idling candidate trees is recursively enumerated without an optimality certificate. For a realized prefix $S$, $W_r(S)$ is its total processing volume after removing the $r$ largest processing times; it is zero when the prefix has at most $r$ jobs.
--
--   This is the common objective and ordering layer for all supporting statements. It also supplies the physical feasibility predicate for a single realized schedule.
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Section 2, pp.6–8; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Model

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

noncomputable def totalMean {N m : ℕ} (I : Instance N m)
    (U : Finset (Fin N)) : ℝ≥0∞ :=
  ∑ j ∈ U, (chance I j : ℝ≥0∞) * (processing I j true : ℝ≥0∞)

/-- Completion is at s+X, never at a rounded machine release. -/
noncomputable def realizedCost {N m : ℕ} (I : Instance N m)
    (t : PolicyTree N m) (ω : Outcome N) : ℝ≥0∞ :=
  ((trace t ω).map fun a => (a.time : ℝ≥0∞) + (processing I a.job (ω a.job) : ℝ≥0∞)).sum

noncomputable def treeCost {N m : ℕ} (I : Instance N m) (t : PolicyTree N m) : ℝ≥0∞ :=
  ∑ ω : Outcome N, (outcomeWeight I ω : ℝ≥0∞) * realizedCost I t ω

noncomputable def randomCost {N m : ℕ} (I : Instance N m)
    (π : RandomPolicy N m) : ℝ≥0∞ :=
  ∫⁻ t, treeCost I t ∂π.law

/-- Almost-sure physical feasibility is the sole benchmark restriction. -/
noncomputable def RandomAdmissible {N m : ℕ} (I : Instance N m) (s : State N m)
    (π : RandomPolicy N m) : Prop :=
  ∀ᵐ t ∂π.law, Admissible I s t

noncomputable def optimum {N m : ℕ} (I : Instance N m) (s : State N m) : ℝ≥0∞ :=
  ⨅ π : {π : RandomPolicy N m // RandomAdmissible I s π}, randomCost I π.val

/-- A deterministic policy is a special case of a randomized policy. -/
noncomputable def deterministic {N m : ℕ} (t : PolicyTree N m) : RandomPolicy N m :=
  ⟨MeasureTheory.Measure.dirac t, inferInstance⟩

/-- The finite candidate family constructed by non-idling enumeration; feasibility
    and optimality of this family are conclusions of Lemma 2.1, not assumptions. -/
noncomputable def nonIdleTrees {N m : ℕ} (I : Instance N m) :
    ℕ → State N m → Finset (PolicyTree N m)
  | 0, s => if s.remaining = ∅ then {.done} else ∅
  | fuel + 1, s => by
      classical
      exact if s.remaining = ∅ then {.done} else
        s.remaining.biUnion fun j => (Finset.univ.filter (fun i : Fin m =>
          max (s.free i) s.now = minRelease s)).biUnion fun i : Fin m =>
          let a : Action N m := ⟨j, i, minRelease s⟩
          ((nonIdleTrees I fuel (advance I s a false)).product
            (nonIdleTrees I fuel (advance I s a true))).image fun zp => .start a zp.1 zp.2

/-- Nondecreasing probability, then job label, inside an equal-size class. -/
def ClassFirst {N m : ℕ} (I : Instance N m) (U : Finset (Fin N)) (j : Fin N) : Prop :=
  j ∈ U ∧ ∀ i ∈ U, I.size i = I.size j →
    I.probability j < I.probability i ∨
      (I.probability j = I.probability i ∧ j.val ≤ i.val)

noncomputable def RespectsClasses {N m : ℕ} (I : Instance N m) :
    State N m → PolicyTree N m → Prop
  | _, .done => True
  | s, .start a z p => ClassFirst I s.remaining a.job ∧
      RespectsClasses I (advance I s a false) z ∧
      RespectsClasses I (advance I s a true) p

/-- Residual processing after removing the r largest realized processing times. -/
noncomputable def residualVolume {N m : ℕ} (I : Instance N m) (ω : Outcome N)
    (r : ℕ) (jobs : List (Fin N)) : ℝ≥0∞ :=
  ((((jobs.map fun j => processing I j (ω j)).mergeSort (fun x y => decide (y ≤ x))).drop r).map
    fun x => (x : ℝ≥0∞)).sum

noncomputable def traceState {N m : ℕ} (I : Instance N m) (s : State N m)
    (actions : List (Action N m)) (ω : Outcome N) : State N m :=
  actions.foldl (fun state a => advance I state a (ω a.job)) s

noncomputable def EarliestTrace {N m : ℕ} (I : Instance N m) (s : State N m)
    (actions : List (Action N m)) (ω : Outcome N) : Prop :=
  ∀ k a, actions[k]? = some a → a.time = minRelease (traceState I s (actions.take k) ω)

/-- Start time of a labeled job, used only for admissible complete policies. -/
noncomputable def startTime {N m : ℕ} (t : PolicyTree N m) (ω : Outcome N)
    (j : Fin N) : ℝ≥0 :=
  (((trace t ω).find? fun a => a.job = j).map Action.time).getD 0

/-- Physical feasibility of one complete realization, without imposing a
    policy's behavior on any other outcome realization. -/
noncomputable def RealizedAdmissible {N m : ℕ} (I : Instance N m)
    (actions : List (Action N m)) (ω : Outcome N) : Prop :=
  (actions.map Action.job).Perm (List.finRange N) ∧
    ∀ k a, actions[k]? = some a →
      Feasible (traceState I (initialState Finset.univ) (actions.take k) ω) a

end BernoulliQPTAS.Scheduling


