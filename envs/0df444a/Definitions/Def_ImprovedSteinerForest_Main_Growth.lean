-- Prove2me | Definitions.Def_ImprovedSteinerForest_Main_Growth
-- name    : ImprovedSteinerForest_Main_Growth
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:27:31.276926+00:00
-- url     : https://prove2.me/theorems/3d8e32f3-cb04-4cf9-9816-a3f364e4af5b
-- title:
--   Extended moat growth with parameter ε as a relation on runs; y_U, ℓ, Σy, phases, support cuts, first deactivation, actively connected collections, gain
-- statement:
--   **Extended moat growth** (§2.2) with a nonnegative rational parameter $\varepsilon$ maintains a partition of $V$ into moats, initially one per vertex, cut weights $y_U\ge 0$ and a budget per moat, initially $0$. A moat $U$ is **demand-active** if $\sigma(U)\ne\emptyset$ and **budget-active** if $\sigma(U)=\emptyset$ and its budget is positive; active moats grow $y_U$ at rate one; demand-active moats earn budget at rate $\varepsilon$, budget-active moats spend it at rate one. The edge-packing constraints
--   $$\sum_{U:\,f\in\delta(U)} y_U\le c_f\qquad(f\in E_G)$$
--   hold throughout; when an edge becomes tight, the moats at its endpoints merge and their budgets add, simultaneous mergers being processed one at a time in the fixed edge order; after all tight edges at a time are processed, activity is determined; the process stops when no moat is active.
--
--   A run is recorded as steps $k=0,\dots,\mathrm{len}$: step $k$ starts at time $\sum_{i<k}\mathrm{dur}_i$ with partition $\mathrm{part}_k$ and active set $\mathrm{active}_k$, lasts $\mathrm{dur}_k\ge 0$, and either keeps the partition or merges the two moats joined by one edge. A run is valid when: the initial partition is the singletons; active moats are exactly those with $\sigma(U)\ne\emptyset$ or positive budget; packing holds and budgets are nonnegative at every step; if a tight edge joins two moats at the start of step $k$, step $k$ has duration $0$ and merges along the least such edge; otherwise step $k<\mathrm{len}$ is a positive phase with some active moat and no merger that ends at the first event (an edge joining two moats becomes tight, or a budget-active moat's budget reaches $0$); and the last step has no tight edge between moats and no active moat. The budget of a moat $U$ is $\sum_{W\subseteq U}(\varepsilon[\sigma(W)\ne\emptyset]-[\sigma(W)=\emptyset])\,y_W$ with the weights grown so far (all moats merged into $U$ are its subsets).
--
--   Derived quantities: $y_U$ (total time $U$ is an active moat), $\ell=\sum_{\sigma(U)\ne\emptyset}y_U$, $\sum_U y_U$, the positive phases, the support cuts $\{U: y_U>0\}$, the merger forest. The **first deactivation time** of $v$ is the first settled time at which its moat is inactive; $u,v$ are **actively connected** if they lie in a common moat at some step whose time is at most both first deactivation times; an **actively connected collection** is a finite collection of nonempty vertex sets each inside one class. Its **gain** is (2.2):
--   $$\mathrm{gain}(\mathcal S)=2\sum_{\text{phases}}(\text{duration})\,\bigl(|A|-|A/\mathcal S|\bigr),$$
--   where $A$ is the set of active moats of the phase and $|A/\mathcal S|$ counts them after identifying, transitively, active moats meeting a common set of $\mathcal S$. The bit length of a rational is the binary length of its numerator plus that of its denominator.
--
--   **Formalization Note.** The process is deterministic, so a valid run is unique; it is encoded as a relation `IsGrowthRun ε I R` on records (the pattern of the published `PCSFBreach_Main_PrimalDual`). Durations and weights are rational. Zero-duration steps carry simultaneous mergers and contribute nothing to $y$ or to the gain. `moatOf` returns `∅` for a vertex outside every part, which never happens on a run.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 14, §2.2 and Eq. (2.1); p. 15, §2.3 and Eq. (2.2)

import Mathlib
import Definitions.Def_ImprovedSteinerForest_Main_Instance
set_option autoImplicit false

namespace ImprovedSteinerForest.Main

open Finset

/-- A record of **extended moat growth** (§2.2, p. 14) on an instance `I`, as a sequence of steps
`k = 0, …, len − 1` followed by the final state `len`. Step `k` starts at time `time k` with the
moat partition `part k` and the set `active k` of active moats, lasts `dur k` (zero for a merger
step) and, if `merge k = some f`, ends by merging the two moats joined by the tight edge `f`.
A positive-duration step is a positive phase; zero-duration steps carry the simultaneous mergers,
one at a time. Whether a record is a run of the process with parameter `ε` is `IsGrowthRun`. -/
structure GrowthRun (I : Instance) where
  len : ℕ
  part : ℕ → Finset (Finset (Fin I.n))
  active : ℕ → Finset (Finset (Fin I.n))
  dur : ℕ → ℚ
  merge : ℕ → Option I.Edge

namespace GrowthRun

variable {I : Instance} (R : GrowthRun I)

/-- Start time `Σ_{i<k} dur i` of step `k`. -/
def time (k : ℕ) : ℚ := ∑ i ∈ range k, R.dur i

open scoped Classical in
/-- Cut weight of `U` grown before step `k`: the total duration of the steps `i < k` in which `U`
is an active moat. -/
noncomputable def yBefore (U : Finset (Fin I.n)) (k : ℕ) : ℚ :=
  ∑ i ∈ range k, if U ∈ R.active i then R.dur i else 0

/-- The final cut weight `y_U` (p. 14: "the total time for which `U` grows"). -/
noncomputable def y (U : Finset (Fin I.n)) : ℚ := R.yBefore U R.len

open scoped Classical in
/-- Load `Σ_{U : f ∈ δ(U)} y_U` of edge `f` at the start of step `k` (left side of (2.1)). -/
noncomputable def load (f : I.Edge) (k : ℕ) : ℚ :=
  ∑ U : Finset (Fin I.n), if I.Crosses f U then R.yBefore U k else 0

open scoped Classical in
/-- Budget of the moat `U` at the start of step `k` (p. 14): a moat earns budget at rate `ε` while
demand-active (`σ(W) ≠ ∅`) and spends it at rate one while budget-active (`σ(W) = ∅`); on a merger
budgets add. Every moat that merged into `U` is a subset of `U`, so the budget is
`Σ_{W ⊆ U} (ε·[σ(W) ≠ ∅] − [σ(W) = ∅]) · y_W(before k)`. -/
noncomputable def budget (ε : ℚ) (U : Finset (Fin I.n)) (k : ℕ) : ℚ :=
  ∑ W ∈ univ.filter (fun W : Finset (Fin I.n) => W ⊆ U),
    (if (I.sigma W).Nonempty then ε else -1) * R.yBefore W k

open scoped Classical in
/-- The tight edges that join two different moats of `part k` at the start of step `k`. -/
noncomputable def tightCrossing (k : ℕ) : Finset I.Edge :=
  univ.filter (fun f => R.load f k = I.c f ∧
    ∃ X ∈ R.part k, ∃ Y ∈ R.part k, X ≠ Y ∧ I.eu f ∈ X ∧ I.ev f ∈ Y)

/-- `part k'` arises from `part k` by merging the two moats containing the endpoints of `f`. -/
def MergesBy (k k' : ℕ) (f : I.Edge) : Prop :=
  ∃ X ∈ R.part k, ∃ Y ∈ R.part k, X ≠ Y ∧ I.eu f ∈ X ∧ I.ev f ∈ Y ∧
    R.part k' = insert (X ∪ Y) ((R.part k).erase X |>.erase Y)

/-- Step `k ≤ len` is **settled**: every tight edge at its start time has been processed, so activity
is determined (p. 14: "After processing all tight edges at a given time, determine which moats are
active"). -/
def Settled (k : ℕ) : Prop := R.tightCrossing k = ∅

/-- The positive phases. -/
noncomputable def positivePhases : Finset ℕ := (range R.len).filter (fun k => 0 < R.dur k)

open scoped Classical in
/-- The support cuts: the vertex sets with positive final weight `y_U > 0` (p. 14). -/
noncomputable def supportCuts : Finset (Finset (Fin I.n)) :=
  univ.filter (fun U => 0 < R.y U)

open scoped Classical in
/-- `ℓ = Σ_{σ(U) ≠ ∅} y_U` (p. 14). -/
noncomputable def ell : ℚ := ∑ U ∈ univ.filter (fun U : Finset (Fin I.n) => (I.sigma U).Nonempty), R.y U

/-- `Σ_U y_U`. -/
noncomputable def sumY : ℚ := ∑ U : Finset (Fin I.n), R.y U

open scoped Classical in
/-- The merger forest: the edges whose tightness caused a merger (p. 14). -/
noncomputable def mergerForest : Finset I.Edge :=
  univ.filter (fun f => ∃ k < R.len, R.merge k = some f)

open scoped Classical in
/-- The moat of `part k` containing `v` (`∅` if none, which never happens on a run). -/
noncomputable def moatOf (k : ℕ) (v : Fin I.n) : Finset (Fin I.n) :=
  if h : ∃ U ∈ R.part k, v ∈ U then Classical.choose h else ∅

open scoped Classical in
/-- First deactivation time of `v` (p. 15): the first time at which its moat is inactive, read at
the settled steps (the final step `len` is settled and has no active moat on a run). -/
noncomputable def deact (v : Fin I.n) : ℚ :=
  let ks := (range (R.len + 1)).filter (fun k => R.Settled k ∧ R.moatOf k v ∉ R.active k)
  if h : ks.Nonempty then R.time (ks.min' h) else R.time R.len

/-- `u` and `v` are **actively connected** (p. 15): they enter a common moat no later than either
vertex's first deactivation. -/
def ActConn (u v : Fin I.n) : Prop :=
  ∃ k ≤ R.len, (∃ U ∈ R.part k, u ∈ U ∧ v ∈ U) ∧ R.time k ≤ R.deact u ∧ R.time k ≤ R.deact v

/-- An **actively connected collection** (p. 15): a finite collection of nonempty vertex sets, each
contained in an active class. -/
def IsActConnColl (𝒮 : Finset (Finset (Fin I.n))) : Prop :=
  ∀ S ∈ 𝒮, S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, R.ActConn u v

open scoped Classical in
/-- The active classes: the equivalence classes of `ActConn` (p. 15). -/
noncomputable def activeClasses : Finset (Finset (Fin I.n)) :=
  univ.image (fun v => univ.filter (fun w => R.ActConn v w))

end GrowthRun

/-- The number of sets after identifying (transitively) the members of `A` that meet a common set
of `𝒮`: the number of connected components of the graph on `A` joining two members met by a common
`S ∈ 𝒮`. -/
noncomputable def quotCount {V : Type} [DecidableEq V] (A : Finset (Finset V))
    (𝒮 : Finset (Finset V)) : ℕ :=
  Nat.card (SimpleGraph.fromRel
    (fun X Y : A => ∃ S ∈ 𝒮, (S ∩ X.1).Nonempty ∧ (S ∩ Y.1).Nonempty)).ConnectedComponent

namespace GrowthRun

variable {I : Instance} (R : GrowthRun I)

/-- `gain(𝒮) = 2 Σ_phases (duration)(decrease in the number of active moats)` (Eq. (2.2), p. 15),
where in each phase the active moats meeting a common set of `𝒮` are identified transitively.
Zero-duration steps contribute nothing. -/
noncomputable def gain (𝒮 : Finset (Finset (Fin I.n))) : ℚ :=
  2 * ∑ k ∈ range R.len, R.dur k * (((R.active k).card : ℚ) - (quotCount (R.active k) 𝒮 : ℚ))

end GrowthRun

/-- `R` is a run of **extended moat growth** with parameter `ε` on `I` (§2.2, p. 14):
1. initially every vertex is its own moat;
2. durations are nonnegative; a step either keeps the partition (`merge = none`) or merges the two
   moats joined by its edge;
3. at every step the active moats are exactly the moats that are demand-active (`σ(U) ≠ ∅`) or have
   positive budget;
4. edge packing (2.1) holds and budgets are nonnegative at every step;
5. tight edges are processed one at a time in the fixed edge order: if some tight edge joins two
   moats at the start of step `k`, then step `k` has duration zero and merges along the least such
   edge;
6. otherwise, step `k < len` is a phase: some moat is active, nothing merges, the duration is
   positive, and it ends at the first event: an edge joining two moats becomes tight, or a
   budget-active moat's budget reaches zero;
7. the process stops at the first settled step without active moats. -/
def IsGrowthRun (ε : ℚ) (I : Instance) (R : GrowthRun I) : Prop :=
  R.part 0 = Finset.univ.image (fun v : Fin I.n => ({v} : Finset (Fin I.n))) ∧
  (∀ k < R.len, 0 ≤ R.dur k ∧
    (R.merge k = none → R.part (k + 1) = R.part k) ∧
    (∀ f, R.merge k = some f → R.MergesBy k (k + 1) f)) ∧
  (∀ k ≤ R.len, R.active k =
    (R.part k).filter (fun U => (I.sigma U).Nonempty ∨ 0 < R.budget ε U k)) ∧
  (∀ k ≤ R.len, (∀ f, R.load f k ≤ I.c f) ∧ ∀ U ∈ R.part k, 0 ≤ R.budget ε U k) ∧
  (∀ k ≤ R.len, ∀ h : (R.tightCrossing k).Nonempty,
    k < R.len ∧ R.dur k = 0 ∧ R.merge k = some ((R.tightCrossing k).min' h)) ∧
  (∀ k < R.len, R.Settled k →
    (R.active k).Nonempty ∧ R.merge k = none ∧ 0 < R.dur k ∧
    ((R.tightCrossing (k + 1)).Nonempty ∨
      ∃ U ∈ R.active k, (I.sigma U) = ∅ ∧ R.budget ε U (k + 1) = 0)) ∧
  R.Settled R.len ∧ R.active R.len = ∅

end ImprovedSteinerForest.Main

namespace ImprovedSteinerForest.Main

/-- Bit length of a rational number in lowest terms: binary length of the numerator's absolute
value plus binary length of the denominator. -/
def ratBitLength (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

end ImprovedSteinerForest.Main


