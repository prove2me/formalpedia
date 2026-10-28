-- Prove2me | Definitions.Def_CountingMatroid_Model_Program
-- name    : CountingMatroid_Model_Program
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:40:11.07521+00:00
-- url     : https://prove2.me/theorems/f05921cf-483b-4ca9-b42f-16e7fe1c9379
-- title:
--   Charged annealing and median-estimation program
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean independence-query functions on subsets of $[n]$, and let rational parameters satisfy $0<\varepsilon,\delta<1$. Given a candidate feasibility procedure and a family of Boolean tapes, this bundle defines the deterministic charged composition of preprocessing, bounded annealing runs, and median selection.
--
--   Preprocessing returns $1$ when $n=0$, returns $0$ when the supplied feasibility procedure answers negatively, and otherwise enters annealing. The bounded integer sampler reads blocks of width $\lfloor\log_2(v-1)\rfloor+1$ for a range size $v>1$, accepting the first block below $v$ within a supplied trial cap; it returns failure if the cap is exhausted. Range size zero fails, while range size one returns zero without reading bits. Repeated multiplication defines natural and rational powers. Two finite searches compute halving and draw-trial parameters, and schedule constructs all phase, restart, observation, draw, and repetition fields through charged arithmetic.
--
--   For $G=[n]\times\{0,1\}$, a state is a subset of $G$. The classifier recognizes transversals, ordered empty/full defects with all other pairs singly occupied, and invalid states. The selection scan chooses a zero-based occupied or unoccupied label in pair order. If $\widehat r(S)$ is the imported paired-rank scan value, weight evaluation returns $$q^{\,n-\widehat r(S)}\quad\text{for a transversal},\qquad w_{ik}q^{\,n-\widehat r(S)}\quad\text{for a defect }(i,k),$$ and failure for an invalid supplied kind; natural subtraction is truncated. Here $q$ and the distinct-index multipliers $w_{ik}$ are rational inputs. A chain attempt first reads a holding bit; otherwise it proposes an occupied/unoccupied exchange, rejects an invalid candidate, and compares the rational weight ratio using a capped draw.
--
--   A fresh-transversal procedure selects one label at each pair from successive tape bits. A restart cursor stores a state, tape position, and shared attempt count. Trace return seeks a positive-time return to a transversal subject to the shared cap; restartPhase begins freshly and crosses the stored phase kernels with the prescribed number of trace returns.
--
--   An observation cursor stores a state, tape position, state-kind counts, and a rational numerator sum. Recording a transversal adds $\rho^{\,n-\widehat r(S)}$ to that sum; recording a defect only increments its count. An observation phase records its starting state and then follows one correlated chain trajectory. Finishing rejects a zero transversal or off-diagonal defect count, forms $$\widehat R_j=\widehat u_j/\widehat p_0,$$ and, before the final phase, updates each defect multiplier by $$w_{ik}^{\mathrm{new}}=w_{ik}^{\mathrm{old}}\,\widehat p_0/\widehat p_{ik}.$$ Here the empirical frequencies and numerator mean divide the recorded counts or sum by the schedule's observation count.
--
--   An annealing cursor carries learned tables, current multipliers, a product, and a tape position. A bounded run starts with all multipliers $4$ and product $1$, multiplies successive phase ratios, and returns $$2^n\prod_{j=0}^{L-1}\widehat R_j$$ on success; an abort returns zero and the run's original cursor. Finally, charged insertion sorting and indexed selection define the rational median, with default zero for an empty list. The estimator runs the scheduled number of bounded runs using a separate supplied tape for each run and returns their median.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Model/Program.lean#L37-L543

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

section


set_option autoImplicit false

/-!
# Charged annealing estimator

Correspondence ledger: main.tex:283–293 -> `preprocess` (empty ground and exact
feasibility dispatch), with the cited matroid-intersection code still an
explicit `FeasibilityImplementation` parameter. main.tex:1333–1346 ->
`Subroutines.pairedRank` and its original-oracle greedy scans. main.tex:1105–
1150 -> `schedule`, `leastHalvings`, and `leastDrawTrials`. main.tex:1392–1421
-> `boundedUniform`, including both hard rejection cap and `v=1` zero-bit case.
main.tex:746–751 -> `classifyState`, `selectPaired`, `weightOfKind`, `chainStep`.
main.tex:1163–1201 -> `freshTransversal`, `traceReturn`, `restartPhase`,
`observePhase`, `finishPhase`, and the phase loop in `boundedRun`.
main.tex:1202–1205, 1442–1448 -> zero on abort, ratio product, independent
bounded-run dispatch and charged median in `estimate`.

The paper's analytical partition sums and transport figure are intentionally
absent from the program (statement decision). The cited executable
matroid-intersection pretest remains missing (borrowed implementation gap).
The paired-rank identity, tape coverage, arithmetic representation, and RAM
bit-cost realization remain proof obligations. `estimate` is the full charged
composition relative to the named solver parameter, not yet a closed
executable witness for the paper's unconditional headline.
-/

namespace CountingMatroid.Program

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- `some 1` for the empty ground, `some 0` after a negative exact feasibility
pretest, and `none` to enter the annealing loop. -/
def preprocess (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    Arlib.Computation.Charged Op Cell (Option ℚ) := do
  let empty ← inputSizeIsZero n
  if empty then
    pure (some 1)
  else
    let feasible ← solver.run n r o₁ o₂
    if feasible then pure none else pure (some 0)

/-- Draw `v`'s uniform integer with at most `trials` rejection trials. `none`
means that the cap was exhausted. The natural cursor points to the next fresh
fair bit of the separately supplied tape. -/
def boundedUniform (tape : ℕ → Bool) (trials v cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (Option ℕ × ℕ) := do
  let invalid ← lessThan v 1
  if invalid then
    pure (none, cursor)
  else
  let singleton ← lessThan v 2
  if singleton then
    pure (some 0, cursor)
  else
    let width ← uniformWidth v
    let outcome ← Arlib.Computation.Charged.repeatFor (fun _ acc => do
      let done ← isSome acc.1
      if done then pure acc
      else
        let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
          let bit ← fairBit tape inner.2
          let value ← appendBit inner.1 bit
          let next ← successor inner.2
          pure (value, next)) width (0, acc.2)
        let accepted ← lessThan trial.1 v
        if accepted then pure (some trial.1, trial.2)
        else pure (none, trial.2)) trials ((none : Option ℕ), cursor)
    pure outcome

/-- Multiplication loop used for the integer powers in the paper's formulas. -/
def natPower (base exponent : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => natMul acc base) exponent 1

/-- Multiplication loop for the phase weights `q_j = ρ^j`. -/
def ratPower (base : ℚ) (exponent : ℕ) :
    Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => ratMul acc base) exponent 1

/-- Least b with `2⁻ᵇ ≤ threshold` for a positive rational threshold below
one. The denominator's binary length provides a finite search cap. -/
def leastHalvings (threshold : ℚ) : Arlib.Computation.Charged Op Cell ℕ := do
  let cap ← binaryLoopBound threshold.den
  let result ← Arlib.Computation.Charged.repeatWhile (fun _ acc => do
    let needsStep ← ratLess threshold acc.2
    if needsStep then
      let b ← successor acc.1
      let power ← ratDiv acc.2 2
      pure (some (b, power))
    else pure none) cap (0, (1 : ℚ))
  pure result.1

/-- Least positive d with `M·2⁻ᵈ ≤ 1/32`. -/
def leastDrawTrials (M : ℕ) : Arlib.Computation.Charged Op Cell ℕ := do
  let cap ← binaryLoopBound M
  let target ← natMul 32 M
  let result ← Arlib.Computation.Charged.repeatWhile (fun _ acc => do
    let needsStep ← lessThan acc.2 target
    if needsStep then
      let d ← successor acc.1
      let power ← natMul acc.2 2
      pure (some (d, power))
    else pure none) cap (1, 2)
  pure result.1

/-- The annealing and amplification parameters, with every multiplication,
division, comparison, power and ceiling routed through charged primitives. -/
def schedule (n : ℕ) (p : InputParams) :
    Arlib.Computation.Charged Op Cell AnnealingSchedule := do
  let epsilonTenth ← ratDiv p.ε 10
  let bε ← leastHalvings epsilonTenth
  let twoN ← natMul 2 n
  let twoNq ← ratOfNat twoN
  let inverseTwoN ← ratDiv 1 twoNq
  let rho ← ratSub 1 inverseTwoN
  let nPlusB ← natAdd n bε
  let L ← natMul twoN nPlusB
  let LPlusOne ← successor L
  let etaDenNat ← natMul 32 LPlusOne
  let etaDen ← ratOfNat etaDenNat
  let eta ← ratDiv p.ε etaDen
  let nFourth ← natPower n 4
  let nTimesL ← natMul n LPlusOne
  let traceInner ← natAdd nTimesL 2
  let traceScale ← natMul 20 nFourth
  let tau ← natMul traceScale traceInner
  let LSquare ← natPower LPlusOne 2
  let nSquare ← natPower n 2
  let restartFactor ← natMul 2000 LSquare
  let restartFactor ← natMul restartFactor nSquare
  let restartCap ← natMul restartFactor tau
  let nFourteenth ← natPower n 14
  let observationFactor ← natMul 10000000000 LPlusOne
  let observationFactor ← natMul observationFactor nFourteenth
  let observationNumerator ← ratOfNat observationFactor
  let etaSquare ← ratMul eta eta
  let observationQuotient ← ratDiv observationNumerator etaSquare
  let observations ← rationalCeil observationQuotient
  let attemptsAndObservations ← natAdd restartCap observations
  let threeL ← natMul 3 L
  let drawCalls ← natMul threeL attemptsAndObservations
  let drawTrials ← leastDrawTrials drawCalls
  let bδ ← leastHalvings p.δ
  let tenBδ ← natMul 10 bδ
  let repetitions ← successor tenBδ
  pure (AnnealingSchedule.mk bε rho L eta tau restartCap observations
    drawCalls drawTrials bδ repetitions)

/-- Scan all pairs and recognize Ω₀ or one ordered empty/full defect. An
invalid result is rejected before the Metropolis weight is evaluated. -/
def classifyState {n : ℕ} (state : PairedSet n) :
    Arlib.Computation.Charged Op Cell (StateKind n) := do
  let result ← Arlib.Computation.Charged.foldl (fun acc i => do
    let x ← containsPaired state (i, false)
    let y ← containsPaired state (i, true)
    if x then
      if y then
        let seen ← isSome acc.2.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (acc.1, some i, acc.2.2)
      else pure acc
    else
      if y then pure acc
      else
        let seen ← isSome acc.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (some i, acc.2.1, acc.2.2))
    (List.finRange n) ((none : Option (Fin n)), (none : Option (Fin n)), false)
  if result.2.2 then pure .invalid
  else
    match result.1, result.2.1 with
    | none, none => pure .transversal
    | some i, some j =>
        let diagonal ← indexEqual i j
        if diagonal then pure .invalid else pure (.defect i j)
    | _, _ => pure .invalid

/-- Visit one pair while selecting the k-th occupied or unoccupied element. -/
def selectionVisit {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (k : ℕ) (acc : Option (PairedGround n) × ℕ)
    (element : PairedGround n) :
    Arlib.Computation.Charged Op Cell (Option (PairedGround n) × ℕ) := do
  let inside ← containsPaired state element
  if occupied then
    if inside then
      let hit ← natEqual acc.2 k
      let next ← successor acc.2
      if hit then pure (some element, next) else pure (acc.1, next)
    else pure acc
  else
    if inside then pure acc
    else
      let hit ← natEqual acc.2 k
      let next ← successor acc.2
      if hit then pure (some element, next) else pure (acc.1, next)

/-- Enumerate the 2n paired labels in the fixed order xᵢ,yᵢ and select by
zero-based position within the occupied or unoccupied sublist. -/
def selectPaired {n : ℕ} (state : PairedSet n) (occupied : Bool) (k : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (PairedGround n)) := do
  let result ← Arlib.Computation.Charged.foldl (fun acc i =>
    Arlib.Computation.Charged.foldl
      (selectionVisit state occupied k) [((i, false) : PairedGround n), (i, true)] acc)
      (List.finRange n) ((none : Option (PairedGround n)), 0)
  pure result.1

/-- Evaluate λ(S) using the paired-rank scan; no rank oracle is input. -/
def weightOfKind {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n)
    (kind : StateKind n) : Arlib.Computation.Charged Op Cell (Option ℚ) := do
  match kind with
  | .invalid => pure none
  | .transversal =>
      let rank ← pairedRank r o₁ o₂ state
      let deficiency ← natSub n rank
      let weight ← ratPower q deficiency
      pure (some weight)
  | .defect i j =>
      if h : i ≠ j then
        let rank ← pairedRank r o₁ o₂ state
        let deficiency ← natSub n rank
        let weight ← ratPower q deficiency
        let multiplier ← multiplierRead weights ⟨i, j, h⟩
        let product ← ratMul multiplier weight
        pure (some product)
      else pure none

/-- Lazy exchange Metropolis attempt at `q,w`. `none` is exactly the capped
rejection-draw abort. An exchange outside Ω is rejected and keeps the state. -/
def chainStep {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (drawTrials : ℕ) (q : ℚ)
    (weights : Multipliers n) (state : PairedSet n) (cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ)) := do
  let hold ← fairBit tape cursor
  let cursor ← successor cursor
  if hold then pure (some (state, cursor))
  else
    let selected ← boundedUniform tape drawTrials n cursor
    match selected.1 with
    | none => pure none
    | some aIndex =>
        let selectedOut ← boundedUniform tape drawTrials n selected.2
        match selectedOut.1 with
        | none => pure none
        | some bIndex =>
            let a ← selectPaired state true aIndex
            let b ← selectPaired state false bIndex
            match a, b with
            | some a, some b =>
                let reduced ← erasePaired state a
                let candidate ← insertPaired reduced b
                let newKind ← classifyState candidate
                match newKind with
                | .invalid => pure (some (state, selectedOut.2))
                | _ =>
                    let oldKind ← classifyState state
                    let oldWeight ← weightOfKind r o₁ o₂ q weights state oldKind
                    let newWeight ← weightOfKind r o₁ o₂ q weights candidate newKind
                    match oldWeight, newWeight with
                    | some oldWeight, some newWeight =>
                        let ratio ← ratDiv newWeight oldWeight
                        let needsDraw ← ratLess ratio 1
                        if needsDraw then
                          let denominator ← rationalDenominator ratio
                          let numerator ← rationalNumerator ratio
                          let acceptedDraw ← boundedUniform tape drawTrials
                            denominator selectedOut.2
                          match acceptedDraw.1 with
                          | none => pure none
                          | some value =>
                              let accepted ← lessThan value numerator
                              if accepted then pure (some (candidate, acceptedDraw.2))
                              else pure (some (state, acceptedDraw.2))
                        else pure (some (candidate, selectedOut.2))
                    | _, _ => pure none
            | _, _ => pure none

/-- Fresh n-bit uniform transversal for each phase restart. -/
def freshTransversal (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (PairedSet n × ℕ) :=
  Arlib.Computation.Charged.foldl (fun acc i => do
    let bit ← fairBit tape acc.2
    let state ← insertPaired acc.1 (i, bit)
    let next ← successor acc.2
    pure (state, next)) (List.finRange n) ((∅ : PairedSet n), cursor)

/-- The state and the global underlying-attempt counter of one phase restart. -/
structure RestartCursor (n : ℕ) where
  state : PairedSet n
  bitCursor : ℕ
  attempts : ℕ

/-- One positive-time return to Ω₀, with the phase-global attempt cap. The
guard is checked before any random bits for the next attempt are read. -/
def traceReturn {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : RestartCursor n) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n)) := do
  let scan ← Arlib.Computation.Charged.repeatWhile (fun _ acc => do
    if acc.2 then pure none
    else
      match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q weights
              current.state current.bitCursor
            let attempts ← successor current.attempts
            match attempted with
            | none => pure (some (none, true))
            | some (state, bitCursor) =>
                let kind ← classifyState state
                let returned ← match kind with
                  | .transversal => pure true
                  | _ => pure false
                pure (some (some ⟨state, bitCursor, attempts⟩, returned))
          else pure (some (none, true))) s.restartCap
    (some start, false)
  if scan.2 then pure scan.1 else pure none

/-- Restart phase j: start from fresh bits and cross the stored kernels at
phases a=1,…,j with τ trace transitions each. -/
def restartPhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ)) := do
  let (initial, cursor) ← freshTransversal n tape cursor
  let crossed ← Arlib.Computation.Charged.repeatFor (fun index current => do
    match current with
    | none => pure none
    | some current =>
        let a ← successor index
        let q ← ratPower s.ρ a
        let weights ← learnedWeightRead tables a s.L
        Arlib.Computation.Charged.repeatFor (fun _ current => do
          match current with
          | none => pure none
          | some current => traceReturn r o₁ o₂ tape s q weights current)
          s.τ (some current)) j (some ⟨initial, cursor, 0⟩)
  match crossed with
  | none => pure none
  | some result => pure (some (result.state, result.bitCursor))

/-- Mutable observation data for a single correlated chain trajectory. -/
structure ObservationCursor (n : ℕ) where
  state : PairedSet n
  bitCursor : ℕ
  counts : StateKind n → ℕ
  numeratorSum : ℚ

/-- Observe the current state and advance the count and `G_j` accumulator. -/
def recordObservation {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (rho : ℚ) (current : ObservationCursor n) :
    Arlib.Computation.Charged Op Cell (Option (ObservationCursor n)) := do
  let kind ← classifyState current.state
  match kind with
  | .invalid => pure none
  | .defect _ _ =>
      let counts ← countIncrement current.counts kind
      pure (some ⟨current.state, current.bitCursor, counts, current.numeratorSum⟩)
  | .transversal =>
      let counts ← countIncrement current.counts kind
      let rank ← pairedRank r o₁ o₂ current.state
      let deficiency ← natSub n rank
      let factor ← ratPower rho deficiency
      let numeratorSum ← ratAdd current.numeratorSum factor
      pure (some ⟨current.state, current.bitCursor, counts, numeratorSum⟩)

/-- N_av consecutive observations, including the restart endpoint. -/
def observePhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : PairedSet n × ℕ) :
    Arlib.Computation.Charged Op Cell (Option (ObservationCursor n)) := do
  let counts ← allocateCounts n
  let initial : ObservationCursor n := ⟨start.1, start.2, counts, 0⟩
  Arlib.Computation.Charged.repeatFor (fun index current => do
    match current with
    | none => pure none
    | some current =>
        let onStart ← natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ
                ⟨state, bitCursor, current.counts, current.numeratorSum⟩)
    s.observations (some initial)

/-- Reject zero type frequencies, form R̂_j = û/p̂₀, and update every
off-diagonal multiplier for the next phase when j+1<L. -/
def finishPhase {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n) :
    Arlib.Computation.Charged Op Cell (Option (ℚ × Multipliers n)) := do
  let countZero ← countRead observed.counts .transversal
  let absent ← natEqual countZero 0
  if absent then pure none
  else
    let observations ← ratOfNat s.observations
    let countZeroRat ← ratOfNat countZero
    let pZero ← ratDiv countZeroRat observations
    let uHat ← ratDiv observed.numeratorSum observations
    let ratio ← ratDiv uHat pZero
    let next ← successor j
    let update ← lessThan next s.L
    let scanned ← Arlib.Computation.Charged.foldl (fun current i =>
      Arlib.Computation.Charged.foldl (fun current k => do
        match current with
        | none => pure none
        | some current =>
            let diagonal ← indexEqual i k
            if diagonal then pure (some current)
            else
              if h : i ≠ k then
                let count ← countRead observed.counts (.defect i k)
                let zero ← natEqual count 0
                if zero then pure none
                else if update then
                  let pCount ← ratOfNat count
                  let pDefect ← ratDiv pCount observations
                  let old ← multiplierRead current ⟨i, k, h⟩
                  let numerator ← ratMul old pZero
                  let value ← ratDiv numerator pDefect
                  let newer ← multiplierWrite current ⟨i, k, h⟩ value
                  pure (some newer)
                else pure (some current)
              else pure none)
        (List.finRange n) current)
      (List.finRange n) (some weights)
    match scanned with
    | none => pure none
    | some updated => pure (some (ratio, updated))

/-- Data carried from one phase to the next in a single bounded run. -/
structure AnnealingCursor (n : ℕ) where
  tables : LearnedWeights n
  currentWeights : Multipliers n
  product : ℚ
  bitCursor : ℕ

/-- One bounded annealing run. Every abort branch returns zero; each phase
restarts afresh, observes one correlated trajectory, updates the weights, and
multiplies the ratio into the final estimate. -/
def boundedRun {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (ℚ × ℕ) := do
  let weights ← initialWeights n
  let tables ← allocateLearnedWeights n s.L weights
  let initial : AnnealingCursor n := ⟨tables, weights, 1, cursor⟩
  let phases ← Arlib.Computation.Charged.repeatFor (fun j current => do
    match current with
    | none => pure none
    | some current =>
        let q ← ratPower s.ρ j
        let started ← restartPhase r o₁ o₂ tape s current.tables j
          current.bitCursor
        match started with
        | none => pure none
        | some started =>
            let observed ← observePhase r o₁ o₂ tape s q
              current.currentWeights started
            match observed with
            | none => pure none
            | some observed =>
                let finished ← finishPhase s j current.currentWeights observed
                match finished with
                | none => pure none
                | some (ratio, nextWeights) =>
                    let product ← ratMul current.product ratio
                    let next ← successor j
                    let update ← lessThan next s.L
                    if update then
                      let tables ← learnedWeightWrite current.tables next s.L
                        nextWeights
                      pure (some ⟨tables, nextWeights, product,
                        observed.bitCursor⟩)
                    else pure (some ⟨current.tables, nextWeights, product,
                      observed.bitCursor⟩))
    s.L (some initial)
  match phases with
  | none => pure (0, cursor)
  | some result =>
      let powerOfTwo ← natPower 2 n
      let scale ← ratOfNat powerOfTwo
      let estimate ← ratMul scale result.product
      pure (estimate, result.bitCursor)

/-- Insert one rational into an already sorted list by a charged linear scan. -/
def sortedInsert (value : ℚ) (sorted : List ℚ) :
    Arlib.Computation.Charged Op Cell (List ℚ) := do
  let (reversed, inserted) ← Arlib.Computation.Charged.foldl
    (fun acc item => do
      if acc.2 then
        let reversed ← consRational item acc.1
        pure (reversed, true)
      else
        let before ← ratLess value item
        if before then
          let reversed ← consRational value acc.1
          let reversed ← consRational item reversed
          pure (reversed, true)
        else
          let reversed ← consRational item acc.1
          pure (reversed, false)) sorted (([] : List ℚ), false)
  let reversed ← if inserted then pure reversed
    else consRational value reversed
  reverseRationals reversed

/-- Median of an odd number of bounded-run rational outputs. -/
def medianRational (values : List ℚ) :
    Arlib.Computation.Charged Op Cell ℚ := do
  let sorted ← Arlib.Computation.Charged.foldl
    (fun acc value => sortedInsert value acc) values ([] : List ℚ)
  let middle ← halfNat values.length
  let result ← nthRational sorted middle
  pure (result.getD 0)

/-- Complete charged composition of the paper's pretest, bounded annealing
runs, and median. Each `tape j` is a separate fair-bit stream supplied by Run;
the finite block size and law still require a proof-side bound. -/
def estimate (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) : Arlib.Computation.Charged Op Cell ℚ := do
  let preliminary ← preprocess solver n r o₁ o₂
  match preliminary with
  | some answer => pure answer
  | none =>
      let s ← schedule n p
      let estimates ← Arlib.Computation.Charged.repeatFor (fun j acc => do
        let (value, _) ← boundedRun r o₁ o₂ (tape j) s 0
        consRational value acc) s.repetitions ([] : List ℚ)
      medianRational estimates

end CountingMatroid.Program





end


