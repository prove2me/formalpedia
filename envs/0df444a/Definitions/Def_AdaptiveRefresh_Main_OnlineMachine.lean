-- Prove2me | Definitions.Def_AdaptiveRefresh_Main_OnlineMachine
-- name    : AdaptiveRefresh_Main_OnlineMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:42.572657+00:00
-- url     : https://prove2.me/theorems/a1719316-a3ac-472d-bfc9-dca0bf7ff5a3
-- title:
--   Costed causal randomized online programs and their success event
-- statement:
--   A program is a finite list extending the published arithmetic RAM with charged initial-input reads, reads of the current delivered update, independent uniform draws, and a yield. The RAM has natural and real registers, ordinary mutable memory, arithmetic and comparisons. It has no graph, sampling-subset, optimization or future-update oracle. Every executed instruction costs one unit. Input weights remain exact real values. Output is the edge array stored in ordinary memory, so changing it requires charged stores.
--
--   A causal measurable strategy sees the preceding output/update records and all previously used randomness. It chooses the next insertion or deletion only after a yield. Invalid input ends the input game after retaining every previous output in the success test. The tape law is the countable product of uniform distributions on $[0,1]$. Randomized adversaries are independent mixtures of these deterministic strategies, as in the source.
--
--   Write $M=\max(2,m)$ and $L=1+\log M$. Positive constants and natural exponents specify
--
--   $$|H|\le C_s nL^a\epsilon^{-b_s},\quad W_0\le C_0(n+m+1)L^e\epsilon^{-b_0},\quad W_j-W_0\le C_u(j+1)L^d\epsilon^{-b_u}.$$
--
--   The common success event requires termination of initialization and all delivered legal updates up to the external horizon, valid support, accuracy, size, and every work prefix. These are conclusions, never assumed state invariants. Initialization and work bounds have no dependence on the future horizon. This is the exact-real RAM convention for the source's unspecified bit model; natural addresses and identities have unit-cost arithmetic. The usual finite-list Borel structures make strategy measurability precise.
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Theorem 1.1 and footnote 2, printed p. 1 (PDF p. 2); randomness-adaptive model and amplification, printed p. 6 (PDF p. 7); §4.4 implementation, printed p. 13 (PDF p. 14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_Graph
import Definitions.Def_VehicleRoutingSurvey_Routing_ArithmeticMachine

set_option autoImplicit false
open scoped ENNReal

namespace AdaptiveRefresh.Main

/-- Finite histories carry the usual disjoint-union Borel structures. -/
noncomputable instance : MeasurableSpace (List ℝ) := borel _
noncomputable instance : MeasurableSpace (List ℕ) := borel _

/-- The general arithmetic RAM is reused. Extensions read only the initial input,
current delivered update, or the next independent real draw, and yield the stored output. -/
inductive OnlineInstruction where
  | core (instruction : VehicleRoutingSurvey.Routing.ArithmeticInstruction)
  | inputNat (dst address : ℕ)
  | inputReal (dst address : ℕ)
  | updateNat (dst address : ℕ)
  | updateReal (dst address : ℕ)
  | uniform (dst : ℕ)
  | yield

abbrev OnlineProgram := List OnlineInstruction
abbrev EncodedUpdate := List ℕ × List ℝ
/-- All previous output/update records and all past random draws, with timing included. -/
abbrev History := List ℕ × List ℝ × List ℝ
abbrev Strategy := History → EncodedUpdate

/-- Independent uniform draws; the program reads tape cells in increasing order only. -/
noncomputable def tapeLaw : MeasureTheory.Measure (ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi fun (_ : ℕ) => ProbabilityTheory.uniformOn (Set.Icc (0 : ℝ) 1)

/-- The initial graph is an edge array, read one field at a time and charged accordingly. -/
def initialNatInput (n m : ℕ) (G : Graph) : List ℕ :=
  [n, m, G.length] ++ G.flatMap (fun e => [e.id, e.u, e.v])

def initialRealInput (ε : ℝ) (G : Graph) : List ℝ := ε :: G.map Edge.weight

/-- Output memory: nm[0] is the number of edges; three natural cells per edge,
with its weight in the corresponding real cell. Every modification uses ordinary stores. -/
def readOutput (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Graph :=
  (List.range (s.nm 0)).map fun i =>
    ⟨s.nm (3 * i + 1), s.nm (3 * i + 2), s.nm (3 * i + 3), s.rm i⟩

/-- Encoding 0,id,u,v;w inserts a live positive weighted edge; 1,id deletes it.
Every other message ends the input game. This check imposes input promises only. -/
noncomputable def deliver (n m b : ℕ) (decremental : Bool) (G : Graph)
    (msg : EncodedUpdate) : Option Graph := by
  classical
  exact match msg with
    | (0 :: id :: u :: v :: [], [w]) =>
      let e : Edge := ⟨id, u, v, w⟩
      let G' := G ++ [e]
      if ¬decremental ∧ ValidGraph n G' ∧ G'.length ≤ m ∧ WeightBound b n G'
      then some G' else none
    | (1 :: id :: [], []) =>
      if ∃ e ∈ G, e.id = id then some (G.filter (fun e => e.id ≠ id)) else none
    | _ => none

structure Snapshot where
  G : Graph
  H : Graph
  work : ℕ

structure InteractionState where
  machine : VehicleRoutingSurvey.Routing.ArithmeticState := {}
  G : Graph
  message : EncodedUpdate := ([], [])
  history : History := ([], [], [])
  outputs : List Snapshot := []
  work : ℕ := 0
  done : Bool := false

/-- No oracle instructions: each core operation, input read, draw or yield costs one.
The environment delivers an update only after a yield and sees no future draw. -/
noncomputable def onlineStep (P : OnlineProgram) (n m b T : ℕ) (ε : ℝ)
    (G₀ : Graph) (decremental : Bool) (S : Strategy) (ω : ℕ → ℝ)
    (s : InteractionState) : InteractionState := by
  classical
  let q := s.machine
  let qnext := {q with pc := q.pc + 1}
  let next := {s with work := s.work + 1}
  exact if s.done ∨ q.halted then s else
    match P[q.pc]? with
    | none => {next with machine := {q with halted := true}}
    | some (.core _) =>
      let coreCode := P.map fun ins => match ins with
        | .core op => op
        | _ => .halt
      {next with machine := VehicleRoutingSurvey.Routing.arithmeticStep coreCode q}
    | some (.inputNat d a) =>
      {next with machine := {qnext with nr := (Function.update q.nr d
        ((initialNatInput n m G₀)[q.nr a]?.getD 0))}}
    | some (.inputReal d a) =>
      {next with machine := {qnext with rr := (Function.update q.rr d
        ((initialRealInput ε G₀)[q.nr a]?.getD 0))}}
    | some (.updateNat d a) =>
      {next with machine := {qnext with nr := (Function.update q.nr d
        (s.message.1[q.nr a]?.getD 0))}}
    | some (.updateReal d a) =>
      {next with machine := {qnext with rr := (Function.update q.rr d
        (s.message.2[q.nr a]?.getD 0))}}
    | some (.uniform d) =>
      let x := ω s.history.2.2.length
      {next with machine := {qnext with rr := Function.update q.rr d x}, history := (s.history.1, s.history.2.1, s.history.2.2 ++ [x])}
    | some .yield =>
      let H := readOutput q
      let outs := s.outputs ++ [⟨s.G, H, s.work + 1⟩]
      let hist : History :=
        (s.history.1 ++ [s.work + 1, H.length] ++ H.flatMap (fun e => [e.id, e.u, e.v]),
         s.history.2.1 ++ H.map Edge.weight, s.history.2.2)
      if T + 1 ≤ outs.length then
        {next with machine := qnext, history := hist, outputs := outs, done := true}
      else
        let msg := S hist
        match deliver n m b decremental s.G msg with
        | none => {next with machine := qnext, history := hist, outputs := outs, done := true}
        | some G' =>
          {next with machine := qnext, G := G', message := msg, outputs := outs, history := (hist.1 ++ msg.1, hist.2.1 ++ msg.2, hist.2.2)}

noncomputable def interaction (P : OnlineProgram) (n m b T : ℕ) (ε : ℝ)
    (G₀ : Graph) (decremental : Bool) (S : Strategy) (ω : ℕ → ℝ)
    (k : ℕ) : InteractionState :=
  (onlineStep P n m b T ε G₀ decremental S ω)^[k] {G := G₀}

/-- Uniform, positive constants with fixed natural exponents for all three resource bounds. -/
structure ResourceBounds where
  sizeConstant : ℝ
  initConstant : ℝ
  updateConstant : ℝ
  sizeLogExponent : ℕ
  sizeAccuracyExponent : ℕ
  initLogExponent : ℕ
  initAccuracyExponent : ℕ
  updateLogExponent : ℕ
  updateAccuracyExponent : ℕ

def PositiveBounds (B : ResourceBounds) : Prop :=
  0 < B.sizeConstant ∧ 0 < B.initConstant ∧ 0 < B.updateConstant

noncomputable def logCapacity (m : ℕ) : ℝ := 1 + Real.log (max 2 m : ℕ)

noncomputable def sizeBudget (B : ResourceBounds) (n m : ℕ) (ε : ℝ) : ℝ :=
  B.sizeConstant * n * logCapacity m ^ B.sizeLogExponent * ε⁻¹ ^ B.sizeAccuracyExponent

noncomputable def initBudget (B : ResourceBounds) (n m : ℕ) (ε : ℝ) : ℝ :=
  B.initConstant * (n + m + 1) * logCapacity m ^ B.initLogExponent * ε⁻¹ ^ B.initAccuracyExponent

noncomputable def updateBudget (B : ResourceBounds) (m j : ℕ) (ε : ℝ) : ℝ :=
  B.updateConstant * (j + 1) * logCapacity m ^ B.updateLogExponent * ε⁻¹ ^ B.updateAccuracyExponent

/-- One event includes termination, every completed output, and all cost prefixes.
Input rejection occurs after a yield; earlier outputs remain subject to all clauses. -/
noncomputable def Successful (P : OnlineProgram) (B : ResourceBounds) (n m b T : ℕ)
    (ε : ℝ) (G₀ : Graph) (decremental : Bool) (S : Strategy)
    (accuracy : Graph → Graph → Prop) (ω : ℕ → ℝ) : Prop :=
  ∃ k : ℕ,
    let s := interaction P n m b T ε G₀ decremental S ω k
    s.done = true ∧ ∃ first rest, s.outputs = first :: rest ∧
      (first.work : ℝ) ≤ initBudget B n m ε ∧
      ∀ j (o : Snapshot), s.outputs[j]? = some o →
        ReweightedSubgraph n o.G o.H ∧ accuracy o.G o.H ∧
        (o.H.length : ℝ) ≤ sizeBudget B n m ε ∧
        (o.work : ℝ) - first.work ≤ updateBudget B m j ε

noncomputable def successLowerBound (m : ℕ) (c : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - Real.rpow (max 2 m : ℕ) (-c))

end AdaptiveRefresh.Main


