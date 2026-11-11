-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_CONGEST
-- name    : DistributedMWC440_UpperBound_CONGEST
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:24:22.323217+00:00
-- url     : https://prove2.me/theorems/97f1f62d-0f05-4eb6-b329-6b5ae9a23cb9
-- title:
--   Local randomized CONGEST execution and cycle output
-- statement:
--   A uniform computable local protocol starts from its own ID and port-ordered incident weights, with optional task-local data empty for the MWC task. Every synchronous transition reads only its local memory, received messages and finitely many fresh private fair bits. Finite natural-number payloads have an explicit polynomial alphabet bound in the network size. The execution is a recursion over communication rounds. The output predicate checks a common actual cycle weight at every node and both endpoint edge marks; forests allow a common infeasibility answer. Resource predicates quantify protocol and uniform constants before inputs, include both real-k time bounds, and retain a measurable joint success event. These are task specifications, with algorithm existence asserted only by theorem items.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, §§1, 3–7, printed pp. 1–43 / PDF pp. 3–45.

import Definitions.Def_DistributedMWC440_UpperBound_Graph

open scoped ENNReal
open MeasureTheory
noncomputable section

namespace DistributedMWC440.UpperBound

/-- Natural-number states encode finite local memory. The same program is used at every node.
Initial data consists only of this node's ID and its port-ordered incident weights.
There is no n, topology, optimum, neighbor-ID or shared-randomness input. -/
structure Protocol where
  initial : (ℕ × List ℕ) × List ℕ → ℕ
  send : ℕ → List (Option ℕ)
  bitCount : ℕ × List (Option ℕ) → ℕ
  step : ℕ × List (Option ℕ) × List Bool → ℕ
  halt : ℕ → Bool
  value : ℕ → Option ℕ
  marks : ℕ → List Bool
  distance : ℕ → Option ℚ
  parentPort : ℕ → Option ℕ
  initial_computable : Computable initial
  send_computable : Computable send
  bitCount_computable : Computable bitCount
  step_computable : Computable step
  halt_computable : Computable halt
  value_computable : Computable value
  marks_computable : Computable marks
  distance_computable : Computable distance
  parentPort_computable : Computable parentPort

def degree {n q b} (I : Network n q b) (v : Fin n) : ℕ :=
  (I.W.graph.neighborSet v).ncard

def localWeights {n q b} (I : Network n q b) (v : Fin n) : List ℕ :=
  List.ofFn (fun p : Fin (degree I v) => I.weight v (I.ports v p).val)

def sent (A : Protocol) (state : ℕ) (p : ℕ) : Option ℕ :=
  (A.send state)[p]?.join

def incoming {n q b} (I : Network n q b) (A : Protocol)
    (state : Fin n → ℕ) (v : Fin n) : List (Option ℕ) :=
  List.ofFn fun p : Fin (degree I v) =>
    let u := I.ports v p
    let rev : I.W.graph.neighborSet u.val := ⟨v, u.property.symm⟩
    sent A (state u.val) ((I.ports u.val).symm rev).val

abbrev Tapes (n : ℕ) := (Fin n × ℕ × ℕ) → Bool

/-- One independent fair bit per node, round and within-round index. -/
def tapeLaw (n : ℕ) : Measure (Tapes n) :=
  Measure.infinitePi (fun _ : Fin n × ℕ × ℕ => (PMF.uniformOfFintype Bool).toMeasure)

def stateAtInput {n q b} (I : Network n q b) (A : Protocol)
    (input : Fin n → List ℕ) (ω : Tapes n) : ℕ → Fin n → ℕ
  | 0, v => A.initial ((I.id v, localWeights I v), input v)
  | t + 1, v =>
    let state := stateAtInput I A input ω t
    if A.halt (state v) then state v else
      let inbox := incoming I A state v
      let bits := List.ofFn (fun j : Fin (A.bitCount (state v, inbox)) => ω (v,t,j.val))
      A.step (state v, inbox, bits)

def stateAt {n q b} (I : Network n q b) (A : Protocol) (ω : Tapes n) :=
  stateAtInput I A (fun _ => []) ω

def Halted {n q b} (I : Network n q b) (A : Protocol) (ω : Tapes n) (t : ℕ) : Prop :=
  ∀ v, A.halt (stateAt I A ω t v) = true

/-- Silence is free. A natural-number payload below n^B takes at most B log₂ n bits.
A halted node sends no further messages. -/
def WidthBound {n q b} (I : Network n q b) (A : Protocol) (B : ℕ)
    (ω : Tapes n) (t : ℕ) : Prop :=
  ∀ r < t, ∀ v, ∀ p < degree I v, ∀ m,
    sent A (stateAt I A ω r v) p = some m →
      m < (max 2 n) ^ B ∧ A.halt (stateAt I A ω r v) = false

/-- Endpoint-local edge marks must describe the same one genuine simple cycle.
The forest case is totalized by a common infeasibility value and no marks. -/
def CorrectCycleOutput {n q b} (I : Network n q b) (A : Protocol)
    (ω : Tapes n) (t : ℕ) (ratio : ℝ) : Prop :=
  (∃ C : Cycle I.W, ENNReal.ofReal C.weight ≤ ENNReal.ofReal ratio * optimum I.W ∧
    ∀ v, (A.value (stateAt I A ω t v)).map (fun a => (a : ℝ)) = some C.weight ∧
      ∀ p : Fin (degree I v),
        ((A.marks (stateAt I A ω t v))[p.val]?.getD false = true ↔
          s(v, (I.ports v p).val) ∈ C.walk.edges)) ∨
  (IsEmpty (Cycle I.W) ∧ ∀ v,
    A.value (stateAt I A ω t v) = none ∧
    ∀ p < degree I v, (A.marks (stateAt I A ω t v))[p]?.getD false = false)

def MWCEvent {n q b} (I : Network n q b) (A : Protocol) (B : ℕ)
    (ratio budget : ℝ) : Set (Tapes n) :=
  {ω | ∃ t : ℕ, (t : ℝ) ≤ budget ∧ Halted I A ω t ∧
    WidthBound I A B ω t ∧ CorrectCycleOutput I A ω t ratio}

/-- All soft-O constants, program and message exponent precede the unknown network.
The optional promise is used only for short-hop/long-hop supporting statements. -/
def Solvable (ratio : ℝ) (q b : ℕ) (cost : ℕ → ℝ → ℝ)
    (promise : ∀ n, Network n q b → Prop) : Prop :=
  ∀ confidence : ℝ, 0 < confidence →
  ∃ (A : Protocol) (B p n₀ : ℕ) (C : ℝ), 0 < C ∧
    ∀ n ≥ max 2 n₀, ∀ I : Network n q b, promise n I →
      (∀ ω t, WidthBound I A B ω t) ∧
      MeasurableSet (MWCEvent I A B ratio (C * (Real.log n) ^ p * cost n (diameter I))) ∧
      ENNReal.ofReal (1 - (n : ℝ) ^ (-confidence)) ≤
        tapeLaw n (MWCEvent I A B ratio (C * (Real.log n) ^ p * cost n (diameter I)))

def generalCost (k : ℝ) (n : ℕ) (D : ℝ) :=
  (n : ℝ) ^ ((k+1)/(2*k+1)) + (n : ℝ) ^ (1/k) + D

def goldenCost (k : ℝ) (n : ℕ) (D : ℝ) :=
  (n : ℝ) ^ ((k+1)/(2*k+1)) + D

def shortCost (k : ℝ) (h : ℕ) (n : ℕ) (D : ℝ) :=
  (n : ℝ) ^ (1/k) + h + D

def shortPromise (h : ℕ) {q b n} (I : Network n q b) : Prop :=
  ∃ C : Cycle I.W, IsMinimum C ∧ C.walk.length ≤ h

def longCost (k : ℝ) (α : ℕ → ℝ) (n : ℕ) (D : ℝ) :=
  (α n) ^ (1+1/k) + n / α n + D

def longPromise (α : ℕ → ℝ) (c : ℝ) {q b n} (I : Network n q b) : Prop :=
  ∃ C : Cycle I.W, IsMinimum C ∧ c * (n * (Real.log n)^2 / α n) ≤ C.walk.length

/-- Uniform in real k, including choices of k depending on n. -/
def Tradeoff (q b : ℕ) : Prop :=
  ∀ confidence : ℝ, 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℝ, 1 ≤ k →
    ∃ A : Protocol, ∀ n ≥ max 2 n₀, ∀ I : Network n q b,
      (∀ ω t, WidthBound I A B ω t) ∧
      (let budget := C * (Real.log n)^p * generalCost k n (diameter I)
       MeasurableSet (MWCEvent I A B (k+1) budget) ∧
       ENNReal.ofReal (1 - (n : ℝ)^(-confidence)) ≤
         tapeLaw n (MWCEvent I A B (k+1) budget)) ∧
      ((1 + Real.sqrt 5)/2 ≤ k →
       let budget := C * (Real.log n)^p * goldenCost k n (diameter I)
       MeasurableSet (MWCEvent I A B (k+1) budget) ∧
       ENNReal.ofReal (1 - (n : ℝ)^(-confidence)) ≤
         tapeLaw n (MWCEvent I A B (k+1) budget))

end DistributedMWC440.UpperBound


