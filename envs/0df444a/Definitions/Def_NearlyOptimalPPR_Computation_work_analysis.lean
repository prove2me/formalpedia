-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
-- name    : NearlyOptimalPPR_Computation_work_analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T10:52:26.247831+00:00
-- url     : https://prove2.me/theorems/e6f318d5-5c36-434e-8bab-7616192ca246
-- title:
--   Recursive PageRank work and finite-prefix bookkeeping
-- statement:
--   This interface records the quantities used to analyze Algorithms 6–9 of the recursive personalized PageRank computation. For an open level, it supplies the virtual potential and residual, budget energy, discovery credit, cache energy and capacity, and the events that incur charged work. Call identifiers and prefix event sets distinguish successive recursive calls at the same level.
--
--   The central bookkeeping compares the nonnegative energy of a call with its current budget and incoming charges:
--
--   $$E_j\le Q_j+W_j.$$
--
--   This module defines the quantities and predicates; their preservation, event counts, termination, and work bounds are separate proof obligations. These interfaces allow the finite-prefix argument to account for the completed update that crosses a budget.
--
--   **Formalization Note** Some definitions are auxiliary operational predicates and finite-set summaries used to translate the source's analysis. They do not assume termination, accuracy, or a running-time bound.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 6–9 pp.14–22, Lemma 4.4 p.18 and Section 5 pp.23–29 (budget, discovery, and finite-prefix work accounting).

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def virtualReference (st : RecursiveState n) : ℕ → Fin n → ℝ
  | 0 => fun _ => 0
  | j+1 => fun v => if v ∈ (st.frames j).active then (st.frames (j+1)).reference v
      else virtualReference st j v+3*(st.frames j).q/8

def virtualPotential (st : RecursiveState n) (j : ℕ) (v : Fin n) : ℝ :=
  st.x v-virtualReference st j v

def virtualResidual (g : InputGraph n) (st : RecursiveState n) : ℕ → Fin n → ℝ
  | 0 => (st.frames 0).residual
  | j+1 => fun v => if v ∈ (st.frames j).active then (st.frames (j+1)).residual v
      else virtualResidual g st j v+(st.frames j).q*LocalPush.deg g.graph v/2

def thresholdSum (st : RecursiveState n) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (st.frames i).q

def ThresholdRelation (st : RecursiveState n) : Prop :=
  ∀ j < st.top, (st.frames (j+1)).q = (st.frames j).theta

def StackInvariant (st : RecursiveState n) : Prop :=
  ∀ i < st.top, (st.frames i).pc = .afterChild

def birthAllowance (st : RecursiveState n) (j : ℕ) : ℝ :=
  (j+3 : ℕ)*(st.frames j).q/2

def energyRow (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (v : Fin n) : ℝ :=
  max (residual g.graph α s st.x v-
    (thresholdSum st j+(st.frames j).q+(if v ∈ (st.frames j).active then 0 else birthAllowance st j))*
      LocalPush.deg g.graph v) 0

def budgetEnergy (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) : ℝ :=
  ∑ v, energyRow g s α st j v

def energyArgument (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (v : Fin n) : ℝ :=
  residual g.graph α s st.x v-
    (thresholdSum st j+(st.frames j).q+(if v ∈ (st.frames j).active then 0 else birthAllowance st j))*
      LocalPush.deg g.graph v

def ReturnDrained (st : RecursiveState n) : Prop :=
  ((st.frames st.top).pc = .normal ∨ (st.frames st.top).pc = .finishEpisode) → pendingPush st = none

def EntryDrained (st : RecursiveState n) : Prop :=
  (st.frames st.top).pc = .beginEpisode → pendingPush st = none

def BudgetEnergyInvariant (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) : Prop :=
  ∀ j ≤ st.top, (st.frames j).openBudget = true →
    budgetEnergy g s α st j ≤ (st.frames j).Q+(st.frames j).W

def discoveryCredit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  3*(st.frames j).q/8*(volumeNat g (st.frames j).active : ℝ)+
    ∑ v ∈ parentDomain st j \ (st.frames j).active, LocalPush.deg g.graph v*relative st j v

def rootScanPotential (g : InputGraph n) (st : RecursiveState n) : ℝ :=
  5/(st.frames 0).q*discoveryCredit g st 0+(volumeNat g (st.frames 0).active : ℝ)

def StoredCreditInvariant (g : InputGraph n) (st : RecursiveState n) : Prop :=
  (volumeNat g st.stored : ℝ) ≤ rootScanPotential g st

def referenceData (st : RecursiveState n) (j : ℕ) := (thresholdSum st j,virtualReference st j)

def ForcingInvariant (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) : Prop :=
  ∀ j ≤ st.top, ∀ v, (LocalPush.Lα g.graph α *ᵥ virtualReference st j) v ≤
    LocalPush.e s v+(3*α/8)*thresholdSum st j*LocalPush.deg g.graph v

def ReferenceNonnegative (st : RecursiveState n) : Prop :=
  ∀ j ≤ st.top, ∀ v, 0 ≤ virtualReference st j v

def drainProduction (st : RecursiveState n) : Option (ℕ × Fin n) :=
  if anyExhausted st then none else pendingPush st

def stepProduction (st : RecursiveState n) : Option (ℕ × Fin n) :=
  if st.done then none else if componentComplete st then none else
  match (st.frames st.top).pc with
  | .initialDrain | .restartDrain =>
      if ancestorExhausted st then none else if (pendingPush st).isSome then drainProduction st else none
  | .leafDrain =>
      if anyExhausted st then none else if (pendingPush st).isSome then drainProduction st else none
  | .afterChild =>
      if ancestorExhausted st then none else if exhausted st st.top then none else drainProduction st
  | _ => none

def pushIncrement (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : ℝ :=
  min ((st.frames t).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames t).q/8-relative st t v)

def ownProduction (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (t,v) => if t=j then LocalPush.deg g.graph v*pushIncrement g st t v else 0

def incomingProduction (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (t,v) => if t≤j then (1-α)*LocalPush.deg g.graph v*pushIncrement g st t v else 0

def birthProduction (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (t,v) =>
      if t=j ∧ relative st t v+pushIncrement g st t v=3*(st.frames t).q/8 then
        ((j+3 : ℕ) : ℝ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0

def stepDebit (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) : ℕ × ℝ≥0∞ :=
  if st.done then (st.top,0) else
  if componentComplete st then (0,jointCost m g st (st.frames 0).active+((st.frames 0).active.card+1 : ℕ)) else
  let j := st.top
  let f := st.frames j
  let cheap : ℕ × ℝ≥0∞ := (j,1)
  let push : ℕ × ℝ≥0∞ := match pendingPush st with
    | none => cheap
    | some (t,v) => (t,(32*(st.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α st t v) : ℕ))
  let drain := if anyExhausted st then cheap else push
  match f.pc with
  | .initialDrain =>
      if ancestorExhausted st then cheap else
      if (pendingPush st).isSome then drain else cheap
  | .restartDrain =>
      if ancestorExhausted st then cheap else
      if (pendingPush st).isSome then drain else cheap
  | .beginEpisode => (j,(16*(volumeNat g f.active+1)*keyCost st : ℕ))
  | .fullSolve =>
      if anyExhausted st then cheap else
      if f.active ⊆ st.stored ∧ ∀ v ∈ f.active, 0 < g.graph.degree v then (j,jointCost m g st f.active) else cheap
  | .normalize =>
      if anyExhausted st then cheap else
      if j=ℓ then cheap else
        (j,(16*(volumeNat g f.active+1)*keyCost st+8*(ℓ+2)*(f.block+2) : ℕ))
  | .leafDrain =>
      if anyExhausted st then cheap else
      if (pendingPush st).isSome then drain else
      if f.high=∅ then cheap else
        let C := f.cache ∪ f.high
        if C ⊆ st.stored ∧ ∀ v ∈ C, 0 < g.graph.degree v then (j,jointCost m g st C) else cheap
  | .afterChild =>
      if ancestorExhausted st then cheap else
      if exhausted st j then cheap else drain
  | .finishEpisode =>
      if ancestorExhausted st then cheap else
      if exhausted st j then cheap else (j,(16*(volumeNat g f.active+1) : ℕ))
  | .normal | .interrupted =>
      if j=0 then (0,(8*f.active.card+2 : ℕ)) else cheap

def EpisodeShape (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top, (st.frames i).openBudget = true → (st.frames i).Q = (st.frames i).theta*(st.frames i).block

def ChildScale (st : RecursiveState n) : Prop :=
  ∀ i < st.top, (st.frames (i+1)).N = (st.frames i).block

def ScaleInvariant (st : RecursiveState n) : Prop := EpisodeShape st ∧ ChildScale st

def outsideMass (g : InputGraph n) (F : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ v ∈ Fᶜ, LocalPush.deg g.graph v*x v

def fullSolveEvent (g : InputGraph n) (st : RecursiveState n) (id : ℕ) : Prop :=
  st.done = false ∧ ¬componentComplete st ∧ (st.frames st.top).pc = .fullSolve ∧
    ¬anyExhausted st ∧ ((st.frames st.top).active ⊆ st.stored ∧
      ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v) ∧ (st.frames st.top).id = id

def episodeEvent (st : RecursiveState n) (id : ℕ) : Prop :=
  st.done = false ∧ ¬componentComplete st ∧ (st.frames st.top).pc = .beginEpisode ∧ (st.frames st.top).id = id

def cachedSolveEvent (g : InputGraph n) (st : RecursiveState n) (id : ℕ) : Prop :=
  st.done=false ∧ ¬componentComplete st ∧ (st.frames st.top).pc=.leafDrain ∧
    ¬anyExhausted st ∧ pendingPush st=none ∧ (st.frames st.top).high ≠ ∅ ∧
    ((st.frames st.top).cache ∪ (st.frames st.top).high ⊆ st.stored ∧
      ∀ v ∈ (st.frames st.top).cache ∪ (st.frames st.top).high, 0 < g.graph.degree v) ∧
    (st.frames st.top).id=id

def cacheExcess (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  ∑ v ∈ (st.frames j).cache, max ((st.frames j).residual v-(st.frames j).theta*LocalPush.deg g.graph v) 0

def FullSolveDrained (st : RecursiveState n) : Prop :=
  (st.frames st.top).pc = .fullSolve → pendingPush st = none

def currentPC (st : RecursiveState n) : NormalizePC := (st.frames st.top).pc

def ActiveDensity (g : InputGraph n) (ℓ j : ℕ) (q : ℝ) (st : RecursiveState n) : Prop :=
  ∀ v ∈ (st.frames j).active,
    (st.frames j).residual v ≤ (kappa ℓ j : ℝ)*q*LocalPush.deg g.graph v

def InterruptedInvariant (st : RecursiveState n) : Prop :=
  (st.frames st.top).pc = .interrupted → ancestorExhausted st

def ReturnDensity (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n) : Prop :=
  ((st.frames st.top).pc = .afterChild → ¬anyExhausted st →
    pendingPush st = none ∧ ActiveDensity g ℓ st.top (st.frames st.top).theta st) ∧
  ((st.frames st.top).pc = .finishEpisode → ActiveDensity g ℓ st.top (st.frames st.top).theta st) ∧
  ((st.frames st.top).pc = .normal → ActiveDensity g ℓ st.top (st.frames st.top).q st)

def cacheCapacity (st : RecursiveState n) (j : ℕ) : ℝ :=
  if (st.frames j).openBudget then max (2*((st.frames j).block : ℝ)-((st.frames j).cache.card : ℝ)) 0 else 0

def newCacheCharge (g : InputGraph n) (st : RecursiveState n) : ℝ :=
  if cachedSolveEvent g st (st.frames st.top).id ∧ ¬(st.frames st.top).high ⊆ (st.frames st.top).cache then 1 else 0

def episodeCapacityCharge (st : RecursiveState n) : ℝ :=
  if episodeEvent st (st.frames st.top).id then 2*((st.frames st.top).block : ℝ) else 0

def frozenFrame (f : NormalizeFrame n) := (f.q,f.N,f.block,f.id)

def noNewCacheCharge (g : InputGraph n) (st : RecursiveState n) : ℝ :=
  if cachedSolveEvent g st (st.frames st.top).id ∧ (st.frames st.top).high ⊆ (st.frames st.top).cache
    then (st.frames st.top).q else 0

def NewCallInformation (st next : RecursiveState n) : Prop :=
  ∃ info : CallInformation, next.top=st.top+1 ∧ next.nextId=st.nextId+1 ∧ info.level=next.top ∧
    (next.frames next.top).id=st.nextId ∧ info.scale=(next.frames next.top).N ∧
    info.block=(next.frames next.top).block ∧
    next.information=Function.update st.information st.nextId (some info)

def InformationIDBound (st : RecursiveState n) : Prop :=
  ∀ id info, st.information id = some info → id < st.nextId

def CallLocations (st : RecursiveState n) : Prop :=
  ∀ id info, st.information id = some info → id ∈ st.closed ∨
    info.level ≤ st.top ∧ (st.frames info.level).id=id ∧
      (st.frames info.level).N=info.scale ∧ (st.frames info.level).block=info.block

def OpenIDBound (st : RecursiveState n) : Prop := ∀ j ≤ st.top, (st.frames j).id < st.nextId

def openIDs (st : RecursiveState n) : Finset ℕ := (Finset.range (st.top+1)).image (fun i => (st.frames i).id)

def ClosedIDBound (st : RecursiveState n) : Prop := ∀ id ∈ st.closed, id < st.nextId

def OpenFrameInformation (st : RecursiveState n) : Prop :=
  ∀ j ≤ st.top, st.information (st.frames j).id=some ⟨j,(st.frames j).N,(st.frames j).block⟩

def RunningOpenNotClosed (st : RecursiveState n) : Prop :=
  st.done=false → ∀ j ≤ st.top, (st.frames j).id ∉ st.closed

noncomputable def enumerateTimes (S : Finset ℕ) (k : ℕ) : ℕ :=
  if h : k < S.card then S.orderEmbOfFin rfl ⟨k,h⟩ else S.sup id+(k-S.card)+1

def ScaleBounds (N₀ : ℝ) (st : RecursiveState n) : Prop :=
  ∀ j ≤ st.top, 1 ≤ (st.frames j).N ∧ ((st.frames j).block : ℝ) ≤ (st.frames j).N ∧ (st.frames j).N ≤ N₀

def activatedDegree (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (t,v) => if t=j ∧ relative st t v+pushIncrement g st t v=3*(st.frames t).q/8
      then LocalPush.deg g.graph v else 0

def discoveryEffort (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (t,v) => if t=j then LocalPush.deg g.graph v+1 else 0

def discoveryEffortPotential (g : InputGraph n) (st : RecursiveState n) (j : ℕ) : ℝ :=
  2*(volumeNat g (st.frames j).active : ℝ)+10/(st.frames j).q*discoveryCredit g st j

def ownPushEvent (st : RecursiveState n) (id : ℕ) : Prop :=
  ∃ j v, stepProduction st=some (j,v) ∧ (st.frames j).id=id

def callDiscoveryEffort (g : InputGraph n) (st : RecursiveState n) (id : ℕ) : ℝ :=
  match stepProduction st with
  | none => 0
  | some (j,v) => if (st.frames j).id=id then LocalPush.deg g.graph v+1 else 0

def queueLogConstant : ℝ := 1+(Real.log 128+4)/Real.log 2

def primitiveLogConstant : ℝ := 1+queueLogConstant*(1+Real.log 2)

noncomputable def massRank (L μ : ℝ) : ℕ :=
  ⌈Real.log (max μ L/L)/Real.log 2⌉₊

def hitCount (D : ℕ → Finset ι) (v : ι) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun k => v ∈ D k)).card

def adjacencyFlow (g : InputGraph n) (H : Finset (Fin n)) (x : Fin n → ℝ) (v : Fin n) : ℝ :=
  ∑ u ∈ H, if g.graph.Adj v u then x u else 0

def restrictedPotential (H : Finset (Fin n)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun v => if v ∈ H then y v else 0

def doubledSet (H : Finset (Fin n)) (h y : Fin n → ℝ) : Finset (Fin n) :=
  H.filter (fun v => y v < h v)

def doublingExcess (H : Finset (Fin n)) (h y : Fin n → ℝ) : Fin n → ℝ :=
  fun v => max (h v-restrictedPotential H y v) 0

def adjustedSource (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) : Fin n → ℝ :=
  fun v => LocalPush.e s v-(LocalPush.Lα g.graph α *ᵥ virtualReference st j) v-
    thresholdSum st j*LocalPush.deg g.graph v

def fullSolveDoubles (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) : Finset (Fin n) :=
  doubledSet (st.frames j).active (solveOn g α (st.frames j).active (st.frames j).residual)
    (virtualPotential st j)

def fullPairInput (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (run : ℕ → RecursiveState n)
    (j : ℕ) (τ : ℕ → ℕ) (i : ℕ) : ℝ :=
  (∑ k ∈ Finset.Ico (τ i+1) (τ (i+1)), incomingProduction g α (run k) j)+
    4*(kappa ℓ 0 : ℝ)*((run (τ i)).frames j).q*
      (volumeNat g (((run (τ (i+1))).frames j).active \ ((run (τ i)).frames j).active) : ℝ)

def callDiscoveryCharge (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (id : ℕ) : ℝ≥0∞ :=
  match stepProduction st with
  | none => 0
  | some (j,v) => if (st.frames j).id=id then
      ((32*(st.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α st j v) : ℕ) : ℝ≥0∞) else 0

def accountCharge (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n) (id : ℕ) : ℝ≥0∞ :=
  if ∃ i ≤ (stepDebit m g α ℓ st).1, (st.frames i).id=id then (stepDebit m g α ℓ st).2 else 0

def ownStepCharge (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n) (id : ℕ) : ℝ≥0∞ :=
  if (st.frames (stepDebit m g α ℓ st).1).id=id then (stepDebit m g α ℓ st).2 else 0

def controlRank : NormalizePC → ℕ
  | .initialDrain => 9
  | .fullSolve => 8
  | .normalize => 7
  | .leafDrain => 6
  | .afterChild => 5
  | .finishEpisode => 4
  | .restartDrain => 3
  | .beginEpisode => 2
  | .normal | .interrupted => 1

def callControlPotential (st : RecursiveState n) (j id : ℕ) : ℕ :=
  if id ∈ st.closed then 0 else controlRank (st.frames j).pc

def controlEvent (g : InputGraph n) (st : RecursiveState n) (id : ℕ) : Prop :=
  st.done=false ∧ stepProduction st=none ∧ ¬cachedSolveEvent g st id ∧
    (st.frames (if componentComplete st then 0 else st.top)).id=id

def CallIDInvariant (st : RecursiveState n) : Prop :=
  (st.frames 0).id = 0 ∧ 0 < st.nextId ∧ ∀ i ≤ st.top, i ≠ 0 → 0 < (st.frames i).id

def RootChargeInvariant (st : RecursiveState n) : Prop := st.work = st.charged 0

def RootClosedInvariant (st : RecursiveState n) : Prop := (0 ∈ st.closed ↔ st.done = true)

def RootLedger (st : RecursiveState n) : Prop :=
  CallIDInvariant st ∧ RootChargeInvariant st ∧ RootClosedInvariant st

def episodeBudget (st : RecursiveState n) (j : ℕ) : ℝ :=
  max (∑ v ∈ (st.frames j).active, (st.frames j).residual v) ((st.frames j).q*(st.frames j).block)

def childSnapshot (st : RecursiveState n) (j id : ℕ) : Finset ℕ :=
  if j < st.top ∧ (st.frames j).id=id then {(st.frames (j+1)).id} else ∅

def seenChildren (run : ℕ → RecursiveState n) (j id : ℕ) : ℕ → Finset ℕ
  | 0 => childSnapshot (run 0) j id
  | T+1 => seenChildren run j id T ∪ childSnapshot (run (T+1)) j id

def descendantStepCharge (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (j id : ℕ) : ℝ≥0∞ :=
  if j < (stepDebit m g α ℓ st).1 ∧ (st.frames j).id=id then (stepDebit m g α ℓ st).2 else 0

def DoneClosed (st : RecursiveState n) : Prop :=
  st.done=true → ∀ j, j ≤ st.top → (st.frames j).id ∈ st.closed

def ChildCounterInvariant (st : RecursiveState n) : Prop :=
  (∀ i, (st.frames i).childrenThisEpisode ≤ 1 ∧
    ((st.frames i).pc = .fullSolve ∨ (st.frames i).pc = .normalize → (st.frames i).childrenThisEpisode = 0)) ∧
  ∀ id k, k ∈ st.episodeChildCounts id → k ≤ 1

end
end NearlyOptimalPPR.Computation


