-- Prove2me | Definitions.Def_MaxPressure_FluidStab_Supplement_Histories
-- name    : MaxPressure_FluidStab_Supplement_Histories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:03:47.490122+00:00
-- url     : https://prove2.me/theorems/85f54a3c-346b-459c-86cd-16ea3f7cb68d
-- title:
--   §§2.4–2.5, pp. 200–201; App. A.1 — physical histories and all-state stability
-- statement:
--   A realized service history records cumulative effort $T$, buffer contents $Z$, engagement levels, service starts and finishes, arrival-ordered job labels, immutable job ownership and decision times. A job remains owned by its activity when processing is frozen. Engagement levels obey the published allocation constraints, and cumulative effort is their time integral. A nonpreemptive open episode runs at level one until its processing requirement is exhausted. Starts select the leading fresh job of every constituent buffer; jobs cannot be assigned twice. Only finitely many episodes and decisions occur on each bounded time interval.
--
--   An initial state gives finite queue contents, arbitrary finite residual requirements of open or frozen activities, their held jobs and outstanding destinations. These residuals and destinations are inserted before the ordinary primitive sequences. Completed episodes, rather than unstarted zero-duration renewal opportunities, drive the physical routing and buffer equations. Instantaneous time-zero completions are included in $Z(0)$ after those completions. Unstarted episodes have infinite start time; started jobs may remain frozen forever in a general preemptive history.
--
--   For a policy assigning such a history to every initial state and sample point, stability means
--
--   $$\forall s\text{ legal},\quad \Pr\!\left(\forall i,\ \lim_{t\to\infty} Z_i^s(t)/t=0\right)=1.$$
--
--   Maximum pressure is an attained domination condition at each decision, over the same physical set used for Lemma 2. No residual blocking estimate, occupation limit, fluid identity or stability property is part of legality or the policy rule.
--
--   **Formalization Note** The generic history data are separate from the paper-specific legality predicate. Job labels put initially held jobs before initially fresh jobs; labels of identical initial jobs can always be chosen this way. Randomization is included in the sample space. Causality is not imposed, so the target theorems also quantify over anticipating choices satisfying the physical conditions. Additional locally finite decision times are allowed; this includes local switch slot boundaries.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), §§2.4–2.5, pp. 200–201; App. A.1 — physical histories and all-state stability

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Allocations

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

variable {I J K : ℕ}

/-- Initial jobs are numbered from 0 in each buffer. `residual j` is the remaining
requirement of an already open (possibly frozen) activity; `held` records its jobs.
`destination` records the still outstanding destinations of these jobs. -/
structure InitialState (I J : ℕ) where
  queue : Fin I → ℕ
  residual : Fin J → Option ℝ
  held : Fin J → Fin I → ℕ
  destination : Fin J → Fin (I + 1) → Fin (I + 1)

/-- Legal initial holdings; general preemptive states can contain frozen activities
sharing processors. Nonpreemptive states additionally have compatible commitments. -/
def InitialState.Legal (N : FluidStab.Network I J K) (s : InitialState I J)
    (np : Bool) : Prop :=
  (∀ j r, s.residual j = some r → 0 ≤ r) ∧
  (∀ j i, (s.residual j).isSome → N.B j i.succ = 1 → s.held j i < s.queue i) ∧
  (∀ j j' i, j ≠ j' → (s.residual j).isSome → (s.residual j').isSome →
    N.B j i.succ = 1 → N.B j' i.succ = 1 → s.held j i ≠ s.held j' i) ∧
  (∀ j i, (s.residual j).isSome → N.B j i.succ = 1 →
    ∀ q, q < s.held j i → ∃ j', (s.residual j').isSome ∧
      N.B j' i.succ = 1 ∧ s.held j' i = q) ∧
  (∀ j, s.destination j 0 ≠ 0 ∨ N.B j 0 = 0) ∧
  (np = true → ∀ k, (∑ j : Fin J, if (s.residual j).isSome then N.A k j else 0) ≤ 1)

/-- Insert the one initially open residual and its routing outcome before the ordinary
primitive sequence. Finite initial perturbations leave (3), (4), (29) unchanged. -/
noncomputable def delayedPrimitives {Ω : Type*} (N : FluidStab.Network I J K)
    (P : Throughput.Primitives I J Ω) (s : InitialState I J) :
    Throughput.Primitives I J Ω where
  eta j n ω := match s.residual j with
    | none => P.eta j n ω
    | some r => if n = 1 then r else P.eta j (n - 1) ω
  Phi j i i' n ω := match s.residual j with
    | none => P.Phi j i i' n ω
    | some _ => if n = 0 then 0 else
        (if N.B j i = 1 ∧ s.destination j i = i' then 1 else 0) +
          P.Phi j i i' (n - 1) ω

/-- A realized physical service history. Episode n≥1 of activity j permanently owns
`job j n i` in buffer i from its start until completion, even while frozen. Birth
labels are ordered by arrival, with arbitrary ordering of simultaneous arrivals.
`∞` start/finish means never starts/finishes; no finite stopping time is imposed. -/
structure History (I J : ℕ) where
  Z : ℝ → Fin I → ℝ
  T : ℝ → Fin J → ℝ
  rate : ℝ → Fin J → ℝ
  start : Fin J → ℕ → WithTop ℝ
  finish : Fin J → ℕ → WithTop ℝ
  job : Fin J → ℕ → Fin I → ℕ
  birth : Fin I → ℕ → WithTop ℝ
  decisions : Set ℝ

/-- Actual completed episodes, as opposed to renewal opportunities. Finiteness is a
clause of LegalHistory before ncard is used in any theorem. This also handles zero
requirements: an unstarted zero-duration job is not a completion. -/
noncomputable def finished (h : History I J) (j : Fin J) (t : ℝ) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ h.finish j n ≤ (t : WithTop ℝ)}.ncard

/-- Open jobs just before a decision, after all completions at that time. Initial
residual jobs count as held at t=0; freshly started jobs at t do not count twice. -/
noncomputable def before (s : InitialState I J) (h : History I J) (t : ℝ) : Finset (Fin J) :=
  by
  classical
  exact Finset.univ.filter fun j => ∃ n : ℕ, 1 ≤ n ∧
    (h.start j n < (t : WithTop ℝ) ∨ (t = 0 ∧ n = 1 ∧ (s.residual j).isSome)) ∧
    (t : WithTop ℝ) < h.finish j n

noncomputable def snapshot (s : InitialState I J) (h : History I J) (t : ℝ) : Snapshot I J :=
  ⟨h.Z t, before s h t⟩

/-- General physical histories of §2.4, pp. 200–201. No limiting occupation measure,
fluid equation, EAA, independence or stability is included. `np` only controls
preemption. Rates may be fractional unless separately required to be integer.
The episode and ownership clauses give physical meaning to cumulative service. -/
noncomputable def LegalHistory {Ω : Type*} (N : FluidStab.Network I J K)
    (P : Throughput.Primitives I J Ω) (s : InitialState I J) (ω : Ω)
    (h : History I J) (np : Bool) : Prop :=
  let Q := delayedPrimitives N P s
  let V := fun j n => BellWilliams2001.ThresholdPolicy.partialSum (fun l => Q.eta j l ω) n
  s.Legal N np ∧
  (∀ j t, 0 ≤ t → {n : ℕ | 1 ≤ n ∧ h.start j n ≤ (t : WithTop ℝ)}.Finite) ∧
  (∀ j n, 1 ≤ n → (0 : WithTop ℝ) ≤ h.start j n ∧
    h.start j n ≤ h.finish j n ∧ h.finish j n ≤ h.start j (n + 1)) ∧
  (∀ j r, s.residual j = some r → h.start j 1 = 0) ∧
  (∀ j n (u : ℝ), 1 ≤ n → h.start j n = (u : WithTop ℝ) →
    u ∈ h.decisions ∧ h.T u j = V j (n - 1)) ∧
  (∀ j n (v : ℝ), 1 ≤ n → h.finish j n = (v : WithTop ℝ) → h.T v j = V j n) ∧
  (∀ j t, 0 ≤ t → V j (finished h j t) ≤ h.T t j ∧
    h.T t j ≤ V j (finished h j t + 1)) ∧
  (∀ j n (t : ℝ), 1 ≤ n → h.start j n ≤ (t : WithTop ℝ) →
    (t : WithTop ℝ) < h.finish j n → h.T t j < V j n) ∧
  (∀ j, ContinuousOn (fun t => h.T t j) (Set.Ici 0) ∧ h.T 0 j = 0 ∧
    ∀ t, 0 ≤ t → IntegrableOn (fun u => h.rate u j) (Set.Icc 0 t) volume ∧
      h.T t j = ∫ u in (0 : ℝ)..t, h.rate u j) ∧
  (∀ t, 0 ≤ t → h.rate t ∈ allocSet N) ∧
  (∀ t j, 0 ≤ t → 0 < h.rate t j → ∃ n, 1 ≤ n ∧
    h.start j n ≤ (t : WithTop ℝ) ∧ (t : WithTop ℝ) < h.finish j n) ∧
  (np = true → ∀ (t : ℝ) j n, 0 ≤ t → 1 ≤ n → h.start j n ≤ (t : WithTop ℝ) →
    (t : WithTop ℝ) < h.finish j n → h.rate t j = 1) ∧
  (∀ t, 0 ≤ t → (∀ i, 0 ≤ h.Z t i) ∧
    (∀ i, (∑ j ∈ before s h t, N.B j i.succ) ≤ h.Z t i)) ∧
  (np = true → ∀ t, 0 ≤ t → (snapshot s h t).Legal N) ∧
  (∀ (t : ℝ) i, 0 ≤ t → h.Z t i = (s.queue i : ℝ) +
    (∑ i' : Fin (I + 1), ∑ j : Fin J,
      (Q.Phi j i' i.succ (finished h j t * if N.B j i' = 1 then 1 else 0) ω : ℝ)) -
    ∑ j, (finished h j t : ℝ) * N.B j i.succ) ∧
  (∀ (t : ℝ) i, 0 ≤ t → {q | h.birth i q ≤ (t : WithTop ℝ)}.Finite ∧
    {q | h.birth i q ≤ (t : WithTop ℝ)}.ncard = s.queue i +
      ∑ i' : Fin (I + 1), ∑ j : Fin J,
        Q.Phi j i' i.succ (finished h j t * if N.B j i' = 1 then 1 else 0) ω) ∧
  (∀ i, Monotone (h.birth i)) ∧
  (∀ j n i (u : ℝ), 1 ≤ n → N.B j i.succ = 1 → h.start j n = (u : WithTop ℝ) →
    h.birth i (h.job j n i) ≤ (u : WithTop ℝ) ∧
    ∀ q, h.birth i q ≤ (u : WithTop ℝ) → q < h.job j n i →
      ∃ j' n', N.B j' i.succ = 1 ∧ 1 ≤ n' ∧ h.job j' n' i = q ∧
        h.start j' n' ≤ (u : WithTop ℝ)) ∧
  (∀ j n j' n' i, 1 ≤ n → 1 ≤ n' → N.B j i.succ = 1 → N.B j' i.succ = 1 →
    h.start j n ≠ ⊤ → h.start j' n' ≠ ⊤ → h.job j n i = h.job j' n' i →
      j = j' ∧ n = n') ∧
  (∀ j i, (s.residual j).isSome → N.B j i.succ = 1 → h.job j 1 i = s.held j i) ∧
  (0 ∈ h.decisions) ∧
  (∀ t : ℝ, 0 ≤ t → (h.decisions ∩ Set.Icc 0 t).Finite) ∧
  (∀ j n (t : ℝ), 1 ≤ n → h.finish j n = (t : WithTop ℝ) → t ∈ h.decisions) ∧
  (∀ u v, 0 ≤ u → u < v → (Set.Ioo u v ∩ h.decisions = ∅) →
    ∀ t ∈ Set.Ico u v, h.rate t = h.rate u)

/-- At a decision the chosen allocation maximizes over physically feasible choices.
No residual blocking bound or fluid-limit identity is a policy axiom. -/
noncomputable def IsMaximumPressure (N : FluidStab.Network I J K) (s : InitialState I J)
    (h : History I J) (C : Set (Fin J → ℝ)) (np : Bool) : Prop :=
  ∀ t ∈ h.decisions,
    h.rate t ∈ C ∩ physicallyFeasible N (snapshot s h t) np ∧
    ∀ a ∈ C ∩ physicallyFeasible N (snapshot s h t) np,
      pressure N a (h.Z t) ≤ pressure N (h.rate t) (h.Z t)

/-- A policy contains arbitrary history-dependent choices and arbitrary randomized tie
rules, realized on Ω; every initial state has its own run. Randomization may be part
of Ω. No Markov or stationary restriction is imposed. -/
abbrev Policy (I J : ℕ) (Ω : Type*) := InitialState I J → Ω → History I J

noncomputable def Admissible {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (P : Throughput.Primitives I J Ω)
    (Pr : Measure Ω) (p : Policy I J Ω) (np : Bool) : Prop :=
  ∀ s, s.Legal N np →
    (∀ (t : ℝ) i, 0 ≤ t → Measurable (fun ω => (p s ω).Z t i)) ∧
    ∀ᵐ ω ∂Pr, LegalHistory N P s ω (p s ω) np

/-- Definition 2: the initial-state quantifier is outside the almost-sure one. -/
def Stable {Ω : Type*} [MeasurableSpace Ω] (N : FluidStab.Network I J K)
    (Pr : Measure Ω) (p : Policy I J Ω) (np : Bool) : Prop :=
  ∀ s, s.Legal N np → Throughput.PathwiseStable Pr (fun ω => (p s ω).Z)

noncomputable def IntegerPolicy {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (Pr : Measure Ω) (p : Policy I J Ω) (np : Bool) : Prop :=
  ∀ s, s.Legal N np → ∀ᵐ ω ∂Pr, ∀ t, 0 ≤ t → (p s ω).rate t ∈ integerAllocs N

noncomputable def MaximumPressurePolicy {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (Pr : Measure Ω) (p : Policy I J Ω)
    (C : Set (Fin J → ℝ)) (np : Bool) : Prop :=
  ∀ s, s.Legal N np → ∀ᵐ ω ∂Pr, IsMaximumPressure N s (p s ω) C np

end MaxPressure.FluidStab.Supplement


