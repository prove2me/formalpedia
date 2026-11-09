-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Model
-- name    : MLAMaxDelay_RandomizedTimer_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:15:16.935326+00:00
-- url     : https://prove2.me/theorems/0a3fbe6d-ed0e-4191-aab0-ff6c3757b16e
-- title:
--   Labelled requests, actual service costs, and offline optima
-- statement:
--   An input consists of finitely many labelled occurrences with nonnegative real arrival times and vertex locations. A service at $t$ clears all previously unserved occurrences that have arrived by $t$ and lie in its rooted subtree. For its actual nonempty cleared batch $B$, the charge is
--   $$w(S)+t-\min_{r\in B}a(r).$$
--   The chronological trace computes these batches and charges; infeasible schedules have cost $+\infty$. The offline value is the infimum over all actual feasible rooted service schedules. The footprint $U(A)$ is the root and all root paths to occurrences in $A$, and $\kappa(A)=w(U(A))$. Separately, $\phi(A)=\kappa(A)+\max a(A)-\min a(A)$ and $\Phi^\star$ minimizes the sum of these ideal costs over arbitrary nonempty disjoint batches partitioning the input. The empty partition is allowed on the empty input.
--
--   **Formalization Note.** Natural labels preserve multiplicities. Empty extrema are defined as zero and empty services pay their spatial cost; neither changes the optimum. Useful services in any feasible execution are finite in number, at most the number of occurrences, so finite schedule lists represent the same optimum. Extended nonnegative reals represent infinite costs without subtraction of infinities.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 4–6, Section 2 and Section 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Tree

namespace MLAMaxDelay.RandomizedTimer

open scoped ENNReal

/-- Section 2, p. 4. Finite natural labels name occurrences, not locations.
Values of arrival/location outside `requests` are ignored. -/
structure Input (V : Type) where
  requests : Finset ℕ
  arrival : ℕ → ℝ
  location : ℕ → V
  nonneg : ∀ r ∈ requests, 0 ≤ arrival r

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def restrictInput (I : Input V) (A : Finset ℕ) : Input V where
  requests := I.requests ∩ A
  arrival := I.arrival
  location := I.location
  nonneg := by intro r hr; exact I.nonneg r (Finset.mem_inter.mp hr).1

noncomputable def footprint (T : WeightedTree V) (I : Input V) (A : Finset ℕ) : Finset V := by
  classical
  exact {T.root} ∪ Finset.univ.filter (fun v => ∃ r ∈ A, HarelTarjan.Compressed.IsAncestor T.toRootedTree v (I.location r))

noncomputable def kappa (T : WeightedTree V) (I : Input V) (A : Finset ℕ) : ℝ :=
  spatialWeight T (footprint T I A)

/-- Empty batches use 0; all uses of extrema in ideal batch costs have nonempty batches. -/
noncomputable def firstArrival (I : Input V) (A : Finset ℕ) : ℝ :=
  if h : A.Nonempty then (A.image I.arrival).min' (h.image I.arrival) else 0

noncomputable def lastArrival (I : Input V) (A : Finset ℕ) : ℝ :=
  if h : A.Nonempty then (A.image I.arrival).max' (h.image I.arrival) else 0

abbrev Service (V : Type) := ℝ × Finset V
abbrev Schedule (V : Type) := List (Service V)

/-- Actual newly cleared batch. Full arrivals at time t are visible before the service. -/
noncomputable def cleared (I : Input V) (remaining : Finset ℕ) (s : Service V) : Finset ℕ := by
  classical
  exact remaining.filter (fun r => I.arrival r ≤ s.1 ∧ I.location r ∈ s.2)

noncomputable def serviceCharge (T : WeightedTree V) (I : Input V)
    (B : Finset ℕ) (s : Service V) : ℝ :=
  spatialWeight T s.2 + if B = ∅ then 0 else s.1 - firstArrival I B

/-- The actual chronological trace: service, cleared batch, and actual charge. -/
noncomputable def traceFrom (T : WeightedTree V) (I : Input V) :
    Finset ℕ → Schedule V → List (Service V × Finset ℕ × ℝ)
  | _, [] => []
  | remaining, s :: rest =>
    let B := cleared I remaining s
    (s, B, serviceCharge T I B s) :: traceFrom T I (remaining \ B) rest

noncomputable def trace (T : WeightedTree V) (I : Input V) (S : Schedule V) :=
  traceFrom T I I.requests S

noncomputable def remainingAfter (I : Input V) : Finset ℕ → Schedule V → Finset ℕ
  | remaining, [] => remaining
  | remaining, s :: rest => remainingAfter I (remaining \ cleared I remaining s) rest

/-- Empty services may be deleted; the spatial cost is charged even on them. -/
def Feasible (T : WeightedTree V) (I : Input V) (S : Schedule V) : Prop :=
  S.Pairwise (fun s t => s.1 ≤ t.1) ∧
  (∀ s ∈ S, 0 ≤ s.1 ∧ RootedService T.toRootedTree s.2) ∧
  remainingAfter I I.requests S = ∅

noncomputable def rawCost (T : WeightedTree V) (I : Input V) (S : Schedule V) : ℝ :=
  ((trace T I S).map (fun e => e.2.2)).sum

/-- Infeasible executions have infinite cost, rather than a default real value. -/
noncomputable def cost (T : WeightedTree V) (I : Input V) (S : Schedule V) : ℝ≥0∞ := by
  classical
  exact if Feasible T I S then ENNReal.ofReal (rawCost T I S) else ⊤

/-- Genuine offline schedule optimum, without consecutive-partition restrictions. -/
noncomputable def optimum (T : WeightedTree V) (I : Input V) : ℝ≥0∞ :=
  ⨅ S : Schedule V, cost T I S

/-- A real view for finite-input interval algebra. Finiteness is a conclusion of
`partition_optimum`, not an assumption or an alternative definition of optimum. -/
noncomputable def optimumReal (T : WeightedTree V) (I : Input V) : ℝ :=
  (optimum T I).toReal

noncomputable def idealCost (T : WeightedTree V) (I : Input V) (A : Finset ℕ) : ℝ :=
  kappa T I A + lastArrival I A - firstArrival I A

/-- Arbitrary nonempty disjoint batches, not only consecutive epochs. -/
def IsPartition (I : Input V) (P : Finset (Finset ℕ)) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧ (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧ P.biUnion id = I.requests

noncomputable def partitionOptimum (T : WeightedTree V) (I : Input V) : ℝ≥0∞ :=
  ⨅ P : {P : Finset (Finset ℕ) // IsPartition I P},
    ENNReal.ofReal (∑ B ∈ P.val, idealCost T I B)

end MLAMaxDelay.RandomizedTimer


