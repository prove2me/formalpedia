-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution
-- name    : ChenCapacityTerminals_Exact_ExactExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:58.2315+00:00
-- url     : https://prove2.me/theorems/0f57d7dc-05ae-4254-a181-c182f0c29e68
-- title:
--   Exact-capacity flow-oracle execution for unrestricted terminal thresholds
-- statement:
--   Section 3 permits arbitrary positive real thresholds and conditioning rates. This interface therefore has a finite instruction language with exact capacity arithmetic and comparisons, plus the same explicit fixed-pair request and response records. Integer control and addresses remain bounded by a specified logarithmic word width on every state.
--
--   An execution records its actual flow networks and outside work:
--   $$\operatorname{volume}(\mathcal T)=\sum_{Q\in\mathcal T}(|V(Q)|+|E(Q)|).$$
--   Exact arithmetic has charged operations; division by zero has no transition. A lawful oracle returns a feasible arc-indexed real flow and a matching shore. The input consists of the network, root, terminal labels and threshold; masses and the rate are analytical parameters, not information supplied to the algorithm.
--
--   The output reports an exact value for every queried terminal below the threshold and a lower-threshold certification for each other terminal. If any queried value is below threshold, one additional shore vector attains the least queried value.
--
--   **Formalization Note** This exact-capacity interface is confined to Section 3. The headline algorithm uses ordinary bounded-word integer programs and denominator-cleared rational flow requests.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 6–7, PDF p. 7–8, §3, Lemma 3.1 and Theorem 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7–8

import Definitions.Def_ChenCapacityTerminals_Exact_WordExecution

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- Exact capacity arithmetic is used only for Section 3's unrestricted real U and η.
The headline theorem separately uses actual bounded-word scalar execution. -/
inductive ExactInstruction where
  | scalar (instruction : TrulySubcubicAPSP.Instr)
  | capacityLoad (dst pointer : ℤ)
  | capacityStore (pointer src : ℤ)
  | capacityOne (dst : ℤ)
  | capacityAdd (dst left right : ℤ)
  | capacitySub (dst left right : ℤ)
  | capacityMul (dst left right : ℤ)
  | capacityDiv (dst left right : ℤ)
  | capacityBltz (src : ℤ) (target : ℕ)
  | flow (requestPointer responsePointer : ℤ)

structure ExactMemory where
  integer : ℤ → ℤ
  capacity : ℤ → ℝ

abbrev ExactProgram := List ExactInstruction

structure ExactQuery where
  graph : Network
  source : ℕ
  sink : ℕ

def ExactQuery.Valid (Q : ExactQuery) : Prop :=
  Q.graph.Valid ∧ Q.source ∈ Q.graph.vertices ∧ Q.sink ∈ Q.graph.vertices ∧ Q.source ≠ Q.sink

structure ExactAnswer where
  flow : List ℝ
  shore : Finset ℕ

def ExactAnswer.Correct (Q : ExactQuery) (A : ExactAnswer) : Prop :=
  A.flow.length = Q.graph.arcs.length ∧ FlowCutAnswer Q.graph Q.source Q.sink
    (fun i => A.flow.getD i 0) A.shore

def LawfulExactOracle (O : ExactQuery → ExactAnswer) : Prop :=
  ∀ Q, Q.Valid → (O Q).Correct Q

/-- Canonical local labels are 0,...,n-1; the algorithm itself maintains original-label maps. -/
def readExactQuery (m : ExactMemory) (pointer : ℤ) : ExactQuery :=
  let base := m.integer pointer
  let n := (m.integer base).toNat
  let count := (m.integer (base + 1)).toNat
  ⟨⟨Finset.range n, (List.range count).map fun i =>
    ⟨(m.integer (base + 4 + 3 * i)).toNat,
      (m.integer (base + 5 + 3 * i)).toNat, m.capacity (base + 6 + 3 * i)⟩⟩,
    (m.integer (base + 2)).toNat, (m.integer (base + 3)).toNat⟩

def writeExactAnswer (m : ExactMemory) (base : ℤ) (Q : ExactQuery) (A : ExactAnswer) : ExactMemory :=
  ⟨fun a => if base ≤ a ∧ a < base + Q.graph.vertices.card then
      if (a - base).toNat ∈ A.shore then 1 else 0 else m.integer a,
   fun a => if base ≤ a ∧ a < base + Q.graph.arcs.length then
      A.flow.getD (a - base).toNat 0 else m.capacity a⟩

def exactScalarNext (i : TrulySubcubicAPSP.Instr) (pc : ℕ) (m : ExactMemory) :
    Option (ℕ × ExactMemory) :=
  let write (a v : ℤ) := some (pc + 1, { m with integer := fun x => if x = a then v else m.integer x })
  match i with
  | .one a => write a 1
  | .add a b c => write a (m.integer b + m.integer c)
  | .sub a b c => write a (m.integer b - m.integer c)
  | .mul a b c => write a (m.integer b * m.integer c)
  | .load a b => write a (m.integer (m.integer b))
  | .store a b => write (m.integer a) (m.integer b)
  | .bltz a target => some (if m.integer a < 0 then target else pc + 1, m)
  | .accept => none
  | .reject => none

noncomputable def exactNext (i : ExactInstruction) (pc : ℕ) (m : ExactMemory) :
    Option (ℕ × ExactMemory) :=
  let write (a : ℤ) (v : ℝ) := some (pc + 1, { m with capacity := fun x => if x = a then v else m.capacity x })
  match i with
  | .scalar s => exactScalarNext s pc m
  | .capacityLoad a p => write a (m.capacity (m.integer p))
  | .capacityStore p a => write (m.integer p) (m.capacity a)
  | .capacityOne a => write a 1
  | .capacityAdd a b c => write a (m.capacity b + m.capacity c)
  | .capacitySub a b c => write a (m.capacity b - m.capacity c)
  | .capacityMul a b c => write a (m.capacity b * m.capacity c)
  | .capacityDiv a b c => if m.capacity c = 0 then none else write a (m.capacity b / m.capacity c)
  | .capacityBltz a target => some (if m.capacity a < 0 then target else pc + 1, m)
  | .flow _ _ => none

def IntegerBounded (W : ℕ) (m : ExactMemory) : Prop :=
  ∀ a, |m.integer a| < (2 : ℤ) ^ W

inductive ExactRun (P : ExactProgram) (O : ExactQuery → ExactAnswer) (W : ℕ) :
    ℕ → ExactMemory → ℕ → List ExactQuery → ExactMemory → Prop where
  | halt (pc m) (h : P[pc]? = some (.scalar .accept)) (bounded : IntegerBounded W m) : ExactRun P O W pc m 1 [] m
  | scalar (pc pc' m m' out time trace i)
      (h : P[pc]? = some i) (step : exactNext i pc m = some (pc', m'))
      (bounded : IntegerBounded W m) (boundedNext : IntegerBounded W m')
      (rest : ExactRun P O W pc' m' time trace out) :
      ExactRun P O W pc m (time + 1) trace out
  | flow (pc m out time trace request response)
      (h : P[pc]? = some (.flow request response)) (valid : (readExactQuery m request).Valid)
      (bounded : IntegerBounded W m)
      (rest : ExactRun P O W (pc + 1)
        (writeExactAnswer m (m.integer response) (readExactQuery m request) (O (readExactQuery m request)))
        time trace out) :
      ExactRun P O W pc m (time + 4 + 4 * (readExactQuery m request).graph.arcs.length +
        2 * (readExactQuery m request).graph.vertices.card)
        (readExactQuery m request :: trace) out

def exactVolume (trace : List ExactQuery) : ℕ := (trace.map fun Q => Q.graph.size).sum

/-- Charged arc-list input. Capacity cells carry actual real values, including U.
The root, masses and terminal labels occupy only integer cells. -/
noncomputable def batchingInput (G : Network) (r : ℕ)
    (J : Finset ℕ) (U : ℝ) : ExactMemory :=
  let words : List ℤ := [(G.vertices.card : ℤ), (G.arcs.length : ℤ), (r : ℤ), (J.card : ℤ)] ++
    (G.arcs.flatMap fun e => [(e.tail : ℤ), (e.head : ℤ), 0]) ++
    J.toList.map (fun v => (v : ℤ))
  ⟨fun a => if a < 0 then 0 else words.getD a.toNat 0,
    fun a => if a = 0 then U else
      if 4 ≤ a ∧ (a - 4) % 3 = 2 ∧ (a - 4).toNat / 3 < G.arcs.length
      then G.arcs[(a - 4).toNat / 3]!.capacity else 0⟩

def batchingOutput (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ) (out : ExactMemory) : Prop :=
  (∀ t ∈ J,
    (out.integer (t : ℕ) = 1 ∧ ∃ X, OptimalPair G r t X ∧
      cut G X = out.capacity (t : ℕ) ∧ cut G X < U) ∨
    (out.integer (t : ℕ) = 0 ∧ ∀ X, PairSide G r t X → U ≤ cut G X)) ∧
  ((∃ t ∈ J, ∃ X, PairSide G r t X ∧ cut G X < U) →
    let X := (Finset.range G.vertices.card).filter fun v =>
      out.integer (G.vertices.card + v : ℕ) = 1
    RootSide G r X ∧ cut G X < U ∧
    (∃ t ∈ J, t ∈ X) ∧ ∀ t ∈ J, ∀ Y, PairSide G r t Y → cut G X ≤ cut G Y)

end ChenCapacityTerminals.Exact


