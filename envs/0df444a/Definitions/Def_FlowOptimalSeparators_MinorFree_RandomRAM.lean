-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_RandomRAM
-- name    : FlowOptimalSeparators_MinorFree_RandomRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:05:28.457557+00:00
-- url     : https://prove2.me/theorems/2ceeeea3-7ef0-4716-8855-58c39c1221bb
-- title:
--   Finite randomized scalar programs and extended instruction-count semantics
-- statement:
--   A program consists of two finite instruction lists, for its main routine and its shortest-path subroutine. The base scalar arithmetic and array instructions reuse the published arithmetic machine. Integer multiplication and division, index-to-real conversion, and a uniform-index draw extend that syntax. Each executed scalar instruction, branch, array access, draw, call and return costs one step. A shortest-path call executes its fixed code block instruction by instruction; it is never an oracle.
--
--   Independent uniforms form an infinite product tape. If $\tau$ is the first halting time, define
--   $$\operatorname{work}(\omega)=\tau(\omega)\in[0,\infty],\qquad\mathbb E\operatorname{work}=\int\operatorname{work}\,d\mathbb P.$$
--   Nontermination has infinite work. Correctness predicates and budgets are stated in theorem conclusions, rather than stored in programs. Resource observations count calls and instructions outside calls. Entry/exit snapshots are ghost observations inaccessible to program code; they perform no input preprocessing. Empty inputs may immediately return at zero modeled work, as the chunk convention permits.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 8, 14–15, 24–27, Theorem 5; Algorithms 2–5, computational convention

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_ArithmeticMachine

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Scalar unit-cost RAM, extending the published arithmetic machine with integer arithmetic,
index-to-real conversion and a uniform-index draw. No graph, shortest-path, or minor oracle. -/
inductive Instruction where
  | scalar (i : VehicleRoutingSurvey.Routing.ArithmeticInstruction)
  | natMul (dst a b : ℕ)
  | natDiv (dst a b : ℕ)
  | ofNat (dst src : ℕ)
  | uniform (dst bound : ℕ)
  | callSSSP

/-- Two finite code blocks. SSSP calls execute the second block instruction by instruction. -/
structure Program where
  main : List Instruction
  shortest : List Instruction := []
abbrev Tape := ℕ → ℝ

structure RAMState where
  scalar : VehicleRoutingSurvey.Routing.ArithmeticState
  cursor : ℕ := 0
  returnPC : Option ℕ := none
  pending : Option VehicleRoutingSurvey.Routing.ArithmeticState := none
  calls : ℕ := 0
  additional : ℕ := 0
  /-- Ghost observations, not readable by instructions, for auditing actual subroutine calls. -/
  completed : List (VehicleRoutingSurvey.Routing.ArithmeticState ×
    VehicleRoutingSurvey.Routing.ArithmeticState) := []
  fault : Bool := false

/-- Unit-cost uniform-index primitive; a positive bound gives an index in [0,bound).
Its only randomness is the next independent uniform coordinate. Bound zero returns zero. -/
noncomputable def uniformIndex (u : ℝ) (bound : ℕ) : ℕ :=
  if bound = 0 then 0 else ⌊u * (bound : ℝ)⌋₊ % bound

/-- The empty-instance convention permits an immediate zero-work return. All nonempty inputs
start at pc 0 with only the supplied scalar input arrays and zeroed registers. -/
def ramInit (ns : List ℕ) (rs : List ℝ) : RAMState :=
  {scalar := {VehicleRoutingSurvey.Routing.arithmeticInput ns rs with
      halted := ns.head? = some 0}}

/-- A scalar instruction, including load, store, branch, halt and a draw, costs one step.
The published deterministic interpreter supplies exactly the scalar semantics. -/
noncomputable def ramStep (P : Program) (ω : Tape) (s : RAMState) : RAMState := by
  classical
  exact if s.scalar.halted then s else
    let c := s.scalar
    let z := {s with additional := s.additional + if s.returnPC.isNone then 1 else 0}
    let code := if s.returnPC.isNone then P.main else P.shortest
    let next := {c with pc := c.pc + 1}
    let finish := match s.returnPC, s.pending with
      | some pc, some old => {z with scalar := {c with pc := pc, halted := false}, returnPC := none, pending := none, completed := s.completed ++ [(old, c)]}
      | none, _ => {z with scalar := {c with halted := true}}
      | _, _ => {z with scalar := {c with halted := true}, fault := true}
    match code[c.pc]? with
    | none => finish
    | some (.scalar .halt) => finish
    | some (.scalar _) =>
      {z with scalar := (VehicleRoutingSurvey.Routing.arithmeticStep
        (code.map (fun ins => match ins with
          | .scalar i => i
          | _ => .halt)) c)}
    | some (.natMul d a b) =>
      {z with scalar := {next with nr := Function.update c.nr d (c.nr a * c.nr b)}}
    | some (.natDiv d a b) =>
      {z with scalar := {next with nr := Function.update c.nr d (c.nr a / c.nr b)}}
    | some (.ofNat d a) =>
      {z with scalar := {next with rr := Function.update c.rr d (c.nr a : ℝ)}}
    | some (.uniform d b) =>
      {z with scalar := {next with nr := Function.update c.nr d (uniformIndex (ω s.cursor) (c.nr b))}, cursor := s.cursor + 1}
    | some .callSSSP =>
      if s.returnPC.isSome then {z with scalar := {c with halted := true}, fault := true}
      else {z with scalar := {c with pc := 0}, returnPC := some (c.pc + 1), pending := some c, calls := s.calls + 1}

noncomputable def ramRun (P : Program) (ns : List ℕ) (rs : List ℝ) (ω : Tape) : ℕ → RAMState
  | 0 => ramInit ns rs
  | t + 1 => ramStep P ω (ramRun P ns rs ω t)

/-- The first halting time is the actual instruction count. Empty infima are +infinity. -/
noncomputable def work (P : Program) (ns : List ℕ) (rs : List ℝ) (ω : Tape) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : (ramRun P ns rs ω t).scalar.halted = true), (t : ℝ≥0∞)

noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩

noncomputable def tapeLaw : Measure Tape := Measure.infinitePi (fun _ => uniform01)

instance : IsProbabilityMeasure tapeLaw := by unfold tapeLaw; infer_instance

noncomputable def expectedWork (P : Program) (ns : List ℕ) (rs : List ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, work P ns rs ω ∂tapeLaw

/-- Every returned state is correct, almost-sure halting, and a non-vacuous extended expectation.
The bound B and correctness predicate are theorem conclusions, not fields of programs. -/
def RunsWith (P : Program) (ns : List ℕ) (rs : List ℝ)
    (Q : VehicleRoutingSurvey.Routing.ArithmeticState → Prop) (B : ℝ) : Prop :=
  (∀ ω t, (ramRun P ns rs ω t).scalar.halted = true →
    (ramRun P ns rs ω t).fault = false ∧ Q (ramRun P ns rs ω t).scalar) ∧
  (∀ᵐ ω ∂tapeLaw, ∃ t, (ramRun P ns rs ω t).scalar.halted = true) ∧
  AEMeasurable (work P ns rs) tapeLaw ∧
  expectedWork P ns rs ≠ ⊤ ∧ expectedWork P ns rs ≤ ENNReal.ofReal B

/-- Costs counted outside and across actual calls; diverging executions cost infinity. -/
noncomputable def resource (f : RAMState → ℕ) (P : Program) (ns : List ℕ) (rs : List ℝ)
    (ω : Tape) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : (ramRun P ns rs ω t).scalar.halted = true),
    (f (ramRun P ns rs ω t) : ℝ≥0∞)

def ExpectedResource (f : RAMState → ℕ) (P : Program) (ns : List ℕ) (rs : List ℝ)
    (B : ℝ) : Prop :=
  AEMeasurable (resource f P ns rs) tapeLaw ∧
    (∫⁻ ω, resource f P ns rs ω ∂tapeLaw) ≠ ⊤ ∧
    (∫⁻ ω, resource f P ns rs ω ∂tapeLaw) ≤ ENNReal.ofReal B

/-- Call correctness is checked against the actual entry and exit memories, on every tape. -/
def CallsSatisfy (P : Program) (ns : List ℕ) (rs : List ℝ)
    (R : VehicleRoutingSurvey.Routing.ArithmeticState →
      VehicleRoutingSurvey.Routing.ArithmeticState → Prop) : Prop :=
  ∀ ω t a b, (a,b) ∈ (ramRun P ns rs ω t).completed → R a b

end FlowOptimalSeparators.MinorFree


