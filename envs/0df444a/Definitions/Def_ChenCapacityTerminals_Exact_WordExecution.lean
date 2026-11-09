-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_WordExecution
-- name    : ChenCapacityTerminals_Exact_WordExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:42.797388+00:00
-- url     : https://prove2.me/theorems/d3bbb826-8847-4af9-8c9c-9f91f4474043
-- title:
--   Bounded-word arc-list I/O, flow-call traces and ordinary execution
-- statement:
--   Integer input graphs retain all raw records, including loops, repeated ordered pairs and zero capacities. Their vertex labels are $0,\ldots,n-1$. A mode word selects either a prescribed root or the global cut problem. Ordinary execution uses the published finite scalar instruction list and its bounded-word semantics.
--
--   A separate finite instruction language adds one fixed-pair flow call. Each call reads its own network and endpoints from explicit memory records and returns an integral arc-flow list and a vertex-shore vector. Its trace contains the actual submitted networks, and its charged input and output work is linear in their records. In particular,
--   $$\operatorname{volume}(\mathcal T)=\sum_{Q\in\mathcal T}(|V(Q)|+|E(Q)|).$$
--   Every sort, scan, contraction implementation, comparison and output operation outside these calls must use scalar instructions. A lawful oracle returns a feasible flow and a matching cut; it has no access to the original input except through its explicit request.
--
--   The layer supplies finite-output correctness and the logarithmic factor used in resource specifications. It includes no successful-run or runtime assumption as part of an input instance.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 1, 9–10, PDF p. 2, 10–11, §1 machine model; §4 and §4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=2, 10–11

import Definitions.Def_ChenCapacityTerminals_Exact_Network
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

structure IntegerArc where
  tail : ℕ
  head : ℕ
  capacity : ℕ
  deriving Inhabited

structure IntegerInput where
  n : ℕ
  arcs : List IntegerArc

def IntegerInput.Valid (G : IntegerInput) : Prop :=
  2 ≤ G.n ∧ ∀ e ∈ G.arcs, e.tail < G.n ∧ e.head < G.n

def IntegerInput.network (G : IntegerInput) : Network :=
  ⟨Finset.range G.n, G.arcs.map fun e => ⟨e.tail, e.head, e.capacity⟩⟩

def IntegerInput.polynomial (G : IntegerInput) (p q : ℕ) : Prop :=
  G.arcs.length ≤ G.n ^ p ∧ ∀ e ∈ G.arcs, e.capacity ≤ G.n ^ q

def arcWords (xs : List IntegerArc) : List ℤ :=
  xs.flatMap fun e => [(e.tail : ℤ), (e.head : ℤ), (e.capacity : ℤ)]

/-- Mode zero is global; mode r+1 prescribes root r. Raw loops, parallel and zero arcs stay encoded. -/
def inputWords (G : IntegerInput) (mode : Option ℕ) : List ℤ :=
  [(G.n : ℤ), (G.arcs.length : ℤ),
    (match mode with | none => 0 | some r => r + 1 : ℕ)] ++ arcWords G.arcs

def ValidMode (G : IntegerInput) (mode : Option ℕ) : Prop :=
  match mode with | none => True | some r => r < G.n

def CorrectShore (G : IntegerInput) (mode : Option ℕ) (X : Finset ℕ) : Prop :=
  match mode with
  | none => OptimalGlobal G.network X
  | some r => OptimalRoot G.network r X

def wordShore {W : ℕ} (m : ℤ → BitVec W) (base n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun v => (m (base + v : ℕ)).toNat = 1

def WordOutput {W : ℕ} (G : IntegerInput) (mode : Option ℕ) (m : ℤ → BitVec W) : Prop :=
  let base := (inputWords G mode).length
  (∀ v < G.n, (m (base + v : ℕ)).toNat ≤ 1) ∧
  CorrectShore G mode (wordShore m base G.n)

/-- Ordinary bounded-word execution, with no mathematical-function instructions or flow oracle. -/
def PlainRun (P : List TrulySubcubicAPSP.Instr) (W time : ℕ)
    (G : IntegerInput) (mode : Option ℕ) : Prop :=
  ∃ ticks m, TrulySubcubicAPSP.exec P ticks 0
    (TrulySubcubicAPSP.loadWords W (inputWords G mode)) = some (true, m) ∧
    WordOutput G mode m ∧ time = ticks + (inputWords G mode).length + G.n

structure IntegerQuery where
  graph : IntegerInput
  source : ℕ
  sink : ℕ

def IntegerQuery.Valid (Q : IntegerQuery) : Prop :=
  Q.graph.Valid ∧ Q.source < Q.graph.n ∧ Q.sink < Q.graph.n ∧ Q.source ≠ Q.sink

structure IntegerAnswer where
  flow : List ℕ
  shore : Finset ℕ

def IntegerAnswer.Correct (Q : IntegerQuery) (A : IntegerAnswer) : Prop :=
  A.flow.length = Q.graph.arcs.length ∧
  FlowCutAnswer Q.graph.network Q.source Q.sink
    (fun i => (A.flow.getD i 0 : ℝ)) A.shore

def LawfulWordOracle (O : IntegerQuery → IntegerAnswer) : Prop :=
  ∀ Q, Q.Valid → (O Q).Correct Q

/-- A finite extension of the published scalar instruction set. A call reads a charged
arc-list request and writes a charged arc-flow list and vertex shore. -/
inductive WordInstruction where
  | scalar (instruction : TrulySubcubicAPSP.Instr)
  | flow (requestPointer responsePointer : ℤ)

abbrev WordProgram := List WordInstruction

def readQuery {W : ℕ} (m : ℤ → BitVec W) (pointer : ℤ) : IntegerQuery :=
  let base := (m pointer).toInt
  let n := (m base).toNat
  let count := (m (base + 1)).toNat
  ⟨⟨n, (List.range count).map fun i =>
    ⟨(m (base + 4 + 3 * i)).toNat, (m (base + 5 + 3 * i)).toNat,
      (m (base + 6 + 3 * i)).toNat⟩⟩,
    (m (base + 2)).toNat, (m (base + 3)).toNat⟩

def writeAnswer {W : ℕ} (m : ℤ → BitVec W) (base : ℤ)
    (Q : IntegerQuery) (A : IntegerAnswer) : ℤ → BitVec W :=
  fun a => if base ≤ a ∧ a < base + Q.graph.arcs.length then
      BitVec.ofNat W (A.flow.getD (a - base).toNat 0)
    else if base + Q.graph.arcs.length ≤ a ∧
        a < base + Q.graph.arcs.length + Q.graph.n then
      BitVec.ofNat W (if (a - base - Q.graph.arcs.length).toNat ∈ A.shore then 1 else 0)
    else m a

/-- Scalar transitions are exactly the published bounded-word operations. Halt is handled by
WordRun below. Every scan, sort and arithmetic computation must be a sequence of these steps. -/
def scalarNext {W : ℕ} (i : TrulySubcubicAPSP.Instr) (pc : ℕ) (m : ℤ → BitVec W) :
    Option (ℕ × (ℤ → BitVec W)) :=
  let write (a : ℤ) (v : BitVec W) := some (pc + 1, fun x => if x = a then v else m x)
  match i with
  | .one a => write a 1
  | .add a b c => write a (m b + m c)
  | .sub a b c => write a (m b - m c)
  | .mul a b c => write a (m b * m c)
  | .load a b => write a (m (m b).toInt)
  | .store a b => write (m a).toInt (m b)
  | .bltz a target => some (if (m a).toInt < 0 then target else pc + 1, m)
  | .accept => none
  | .reject => none

/-- time is OUTSIDE-oracle work; the trace holds actual submitted networks. Calls charge
their arc-list I/O. The oracle itself may inspect only its request, never the original graph. -/
inductive WordRun (P : WordProgram) (O : IntegerQuery → IntegerAnswer) {W : ℕ} :
    ℕ → (ℤ → BitVec W) → ℕ → List IntegerQuery → (ℤ → BitVec W) → Prop where
  | halt (pc m) (h : P[pc]? = some (.scalar .accept)) : WordRun P O pc m 1 [] m
  | scalar (pc pc' m m' out time trace i)
      (h : P[pc]? = some (.scalar i)) (step : scalarNext i pc m = some (pc', m'))
      (rest : WordRun P O pc' m' time trace out) :
      WordRun P O pc m (time + 1) trace out
  | flow (pc m out time trace request response)
      (h : P[pc]? = some (.flow request response))
      (valid : (readQuery m request).Valid)
      (rest : WordRun P O (pc + 1)
        (writeAnswer m (m response).toInt (readQuery m request) (O (readQuery m request)))
        time trace out) :
      WordRun P O pc m (time + 4 + 4 * (readQuery m request).graph.arcs.length +
        2 * (readQuery m request).graph.n)
        (readQuery m request :: trace) out

def flowVolume (trace : List IntegerQuery) : ℕ :=
  (trace.map fun Q => Q.graph.n + Q.graph.arcs.length).sum

noncomputable def polylog (n m k : ℕ) : ℝ := (Real.log (2 + (n : ℝ) + m)) ^ k

end ChenCapacityTerminals.Exact


