-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularModel
-- name    : MLAMaxDelay_RandomizedTimer_Supplement_SubmodularModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:51:03.580628+00:00
-- url     : https://prove2.me/theorems/f70f2dd5-f1b7-459c-8f44-e086117d5cb2
-- title:
--   Submodular service-cost models, abstract schedules, optimum and dynamic program
-- statement:
--   **Definition 6.1.** Let $U$ be a set of labelled request occurrences, each with an arrival time $a(r)\ge 0$, and let $\mathcal O$ be a set of service objects. A **submodular service-cost model** consists of a set function $\kappa$ on finite subsets of $U$ and, for every object $\sigma$, a spatial cost $\mathrm{sp}(\sigma)$ and a clearing rule $\mathrm{cl}(\sigma,P)\subseteq P$ giving the batch $\sigma$ clears when the pending set is $P$, such that
--
--   1. $\kappa(\emptyset)=0$, and $A\subseteq B$ implies $\kappa(A)\le\kappa(B)$ (so $\kappa\ge 0$);
--   2. $\kappa$ is submodular: $\kappa(A\cup\{e\})-\kappa(A)\ge\kappa(B\cup\{e\})-\kappa(B)$ for $A\subseteq B$, $e\notin B$, equivalently $\kappa(A)+\kappa(B)\ge\kappa(A\cup B)+\kappa(A\cap B)$;
--   3. every service clearing a batch $A$ has spatial cost at least $\kappa(A)$: $\mathrm{sp}(\sigma)\ge\kappa(\mathrm{cl}(\sigma,P))$;
--   4. for every finite nonempty $A$ some object, executed while the pending set is exactly $A$, clears $A$ at spatial cost exactly $\kappa(A)$.
--
--   The batch and the spatial cost depend only on the object and the current pending set, so a service has no effect on the availability or cost of later services.
--
--   An input is a finite $I\subseteq U$. A schedule is a list of services $(t,\sigma)$. A service at $t$ sees the arrived, not yet cleared requests (complete epochs at $t$ first), clears $\mathrm{cl}(\sigma,\cdot)$ of them and costs $\mathrm{sp}(\sigma)+\max_{r\in B}(t-a(r))$ for a nonempty batch $B$. A schedule is feasible if it is chronological, starts at nonnegative times and clears every request; infeasible schedules cost $+\infty$, and $\mathrm{OPT}(I)$ is the infimum over all finite schedules. With the distinct arrival times $a_1<\dots<a_n$ and $R[i,j]$ the requests of epochs $i,\dots,j$, set $C(i,j)=\kappa(R[i,j])$ and let $D(i,j)$ be the optimum of the subinstance $R[i,j]$.
--
--   The **abstract dynamic program** is Algorithm 1 with $C(p,j)=\kappa(R[p,j])$, the same minimising-predecessor rule and recovery, serving each recovered block $R[p,j]$ at $a_j$ by an attaining object (chosen from item 4).
--
--   **Formalization Note** Epoch intervals are zero-based and half-open. The attaining object is chosen by classical choice; an empty block emits no service.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 15, Definition 6.1; pp. 4–6, Section 2 and Algorithm 1; p. 16, Theorem 6.4(i); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace MLAMaxDelay.RandomizedTimer.Supplement

open scoped ENNReal

/-- Definition 6.1, p. 15. A submodular service-cost model on a universe `U` of labelled
request occurrences with arrival times `a(r) ≥ 0`, and a type `Obj` of service objects.

* `κ A` is the minimum joint-service cost of a finite set `A`: `κ ∅ = 0`, monotone (hence
  nonnegative, so `κ A ∈ ℝ≥0` needs no separate field) and submodular (the published diminishing-returns predicate, equivalent on finite
  sets to `κ A + κ B ≥ κ (A ∪ B) + κ (A ∩ B)`).
* A service object `σ` executed while the pending set is `P` clears the batch `clears σ P ⊆ P`
  and has spatial cost `spatialCost σ`. Both depend only on `σ` and the current pending set:
  a service has no effect on the availability or cost of later services, and every object is
  executable at every time.
* Every service that clears a batch `A` has spatial cost at least `κ A`.
* For every finite nonempty `A` some object, executed with pending set exactly `A`, clears `A`
  at spatial cost exactly `κ A`. -/
structure SubmodularModel (U : Type) [DecidableEq U] (Obj : Type) where
  arrival : U → ℝ
  arrival_nonneg : ∀ r, 0 ≤ arrival r
  κ : Finset U → ℝ
  κ_empty : κ ∅ = 0
  κ_mono : ∀ A B, A ⊆ B → κ A ≤ κ B
  κ_submodular : SubsamplingSM.Offline.IsSubmodular κ
  spatialCost : Obj → ℝ
  clears : Obj → Finset U → Finset U
  clears_subset : ∀ σ P, clears σ P ⊆ P
  spatialCost_ge : ∀ σ P, κ (clears σ P) ≤ spatialCost σ
  attain : ∀ A : Finset U, A.Nonempty → ∃ σ, clears σ A = A ∧ spatialCost σ = κ A

variable {U Obj : Type} [DecidableEq U]

/-- An abstract service `(t, σ)` and a schedule (an ordered list of services). An input is a
finite set of occurrences `I : Finset U`. -/
abbrev SMService (Obj : Type) := ℝ × Obj
abbrev SMSchedule (Obj : Type) := List (SMService Obj)

/-- Empty batches use 0; every use on a nonempty batch is the genuine minimum. -/
noncomputable def smFirstArrival (M : SubmodularModel U Obj) (A : Finset U) : ℝ :=
  if h : A.Nonempty then (A.image M.arrival).min' (h.image M.arrival) else 0

noncomputable def smLastArrival (M : SubmodularModel U Obj) (A : Finset U) : ℝ :=
  if h : A.Nonempty then (A.image M.arrival).max' (h.image M.arrival) else 0

/-- The pending set at the service: arrived (complete epochs at time `t` are visible first) and
not yet cleared; the actual cleared batch is what the object clears from it. -/
noncomputable def smCleared (M : SubmodularModel U Obj) (remaining : Finset U)
    (s : SMService Obj) : Finset U := by
  classical
  exact M.clears s.2 (remaining.filter (fun r => M.arrival r ≤ s.1))

/-- Spatial cost plus the maximum delay of the cleared batch. -/
noncomputable def smCharge (M : SubmodularModel U Obj) (B : Finset U) (s : SMService Obj) : ℝ :=
  M.spatialCost s.2 + if B = ∅ then 0 else s.1 - smFirstArrival M B

noncomputable def smTraceFrom (M : SubmodularModel U Obj) :
    Finset U → SMSchedule Obj → List (SMService Obj × Finset U × ℝ)
  | _, [] => []
  | remaining, s :: rest =>
    let B := smCleared M remaining s
    (s, B, smCharge M B s) :: smTraceFrom M (remaining \ B) rest

noncomputable def smTrace (M : SubmodularModel U Obj) (I : Finset U) (S : SMSchedule Obj) :=
  smTraceFrom M I S

noncomputable def smRemainingAfter (M : SubmodularModel U Obj) :
    Finset U → SMSchedule Obj → Finset U
  | remaining, [] => remaining
  | remaining, s :: rest => smRemainingAfter M (remaining \ smCleared M remaining s) rest

def SMFeasible (M : SubmodularModel U Obj) (I : Finset U) (S : SMSchedule Obj) : Prop :=
  S.Pairwise (fun s t => s.1 ≤ t.1) ∧ (∀ s ∈ S, 0 ≤ s.1) ∧ smRemainingAfter M I S = ∅

noncomputable def smRawCost (M : SubmodularModel U Obj) (I : Finset U) (S : SMSchedule Obj) : ℝ :=
  ((smTrace M I S).map (fun e => e.2.2)).sum

/-- Infeasible schedules cost `⊤`. -/
noncomputable def smCost (M : SubmodularModel U Obj) (I : Finset U) (S : SMSchedule Obj) : ℝ≥0∞ := by
  classical
  exact if SMFeasible M I S then ENNReal.ofReal (smRawCost M I S) else ⊤

/-- The genuine offline optimum over all finite schedules. -/
noncomputable def smOptimum (M : SubmodularModel U Obj) (I : Finset U) : ℝ≥0∞ :=
  ⨅ S : SMSchedule Obj, smCost M I S

noncomputable def smOptimumReal (M : SubmodularModel U Obj) (I : Finset U) : ℝ :=
  (smOptimum M I).toReal

/-- Distinct arrival epochs in increasing order (zero-based). -/
noncomputable def smEpochs (M : SubmodularModel U Obj) (I : Finset U) : List ℝ :=
  (I.image M.arrival).sort (· ≤ ·)

noncomputable def smEpochTime (M : SubmodularModel U Obj) (I : Finset U) (i : ℕ) : ℝ :=
  (smEpochs M I)[i]?.getD 0

/-- Source `R[i,j]` is the half-open zero-based `[i-1, j)` here; empty intervals are `∅`. -/
noncomputable def smIntervalRequests (M : SubmodularModel U Obj) (I : Finset U) (i j : ℕ) :
    Finset U := by
  classical
  exact I.filter (fun r => M.arrival r ∈ ((smEpochs M I).drop i |>.take (j - i)))

/-- `C(i,j) = κ(R[i,j])`. -/
noncomputable def smIntervalC (M : SubmodularModel U Obj) (I : Finset U) (i j : ℕ) : ℝ :=
  M.κ (smIntervalRequests M I i j)

/-- `D(i,j)`: the genuine optimum of the subinstance `R[i,j]`. -/
noncomputable def smIntervalD (M : SubmodularModel U Obj) (I : Finset U) (i j : ℕ) : ℝ :=
  smOptimumReal M (smIntervalRequests M I i j)

/-- A minimum-cost service object for a nonempty batch (chosen from the axiom); an empty batch
emits no service. -/
noncomputable def attainingService (M : SubmodularModel U Obj) (t : ℝ) (A : Finset U) :
    SMSchedule Obj :=
  if h : A.Nonempty then [(t, Classical.choose (M.attain A h))] else []

structure SMDPEntry (Obj : Type) where
  value : ℝ
  predecessor : ℕ
  schedule : SMSchedule Obj

noncomputable def smEntryAt (tab : List (SMDPEntry Obj)) (p : ℕ) : SMDPEntry Obj :=
  tab[p]?.getD ⟨0, 0, []⟩

noncomputable def smDPCandidate (M : SubmodularModel U Obj) (I : Finset U)
    (tab : List (SMDPEntry Obj)) (j p : ℕ) : ℝ :=
  (smEntryAt tab p).value + smIntervalC M I p j + smEpochTime M I (j - 1) - smEpochTime M I p

/-- First strict minimizer over the zero-based predecessors `[0, j)`. -/
noncomputable def smBestPredecessor (M : SubmodularModel U Obj) (I : Finset U)
    (tab : List (SMDPEntry Obj)) (j : ℕ) : ℕ :=
  (List.range j).foldl (fun best p =>
    if smDPCandidate M I tab j p < smDPCandidate M I tab j best then p else best) 0

/-- Theorem 6.4(i): Algorithm 1 with `C(p,j) = κ(R[p,j])`, the same minimizing predecessor rule
and recovery, serving each recovered block `R[p,j]` at `aⱼ` by an attaining object. -/
noncomputable def smDPTable (M : SubmodularModel U Obj) (I : Finset U) : ℕ → List (SMDPEntry Obj)
  | 0 => [⟨0, 0, []⟩]
  | j + 1 =>
    let tab := smDPTable M I j
    let p := smBestPredecessor M I tab (j + 1)
    tab ++ [⟨smDPCandidate M I tab (j + 1) p, p,
      (smEntryAt tab p).schedule ++
        attainingService M (smEpochTime M I j) (smIntervalRequests M I p (j + 1))⟩]

/-- The abstract dynamic program based on recurrence (2): its value and recovered schedule. -/
noncomputable def smOffline (M : SubmodularModel U Obj) (I : Finset U) : SMDPEntry Obj :=
  smEntryAt (smDPTable M I (smEpochs M I).length) (smEpochs M I).length

end MLAMaxDelay.RandomizedTimer.Supplement


