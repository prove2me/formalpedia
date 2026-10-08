-- Prove2me | Definitions.Def_ThreeMachine
-- name    : ThreeMachine
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:30.958801+00:00
-- url     : https://prove2.me/theorems/0a8ea5e1-e57a-4788-b4b1-1a950bc98171
-- statement:
--   An Instance on n vertices (Fin n) is a list of directed edges, and it is acyclic when no vertex lies on a directed cycle (no transitive-closure path from v to v). A schedule τ with horizon T is Feasible when every vertex gets a time slot between 1 and T, at most three vertices share any one time slot, and every edge u→v has τ(u)<τ(v). Inputs are encoded as bit strings: encodeNat writes a natural number as a unary block of 1s of the length of its standard binary encoding, then a 0, then that binary encoding; encodeList writes the length followed by the concatenated item encodings; encodeInput(G,deadline) starts with a 0 if there is no deadline or a 1 followed by the encoded deadline T, then lists the numbers 1..n, then lists the edges as pairs of 1-based vertex indices. An answer is encoded as a single 0 for none, or a 1 followed by the encoded list of slots. CorrectOutput(G,deadline,out) says: with no deadline, out encodes some feasible schedule whose horizon T is minimal among all feasible (T',τ'); with deadline T, out either encodes none and no feasible schedule with horizon T exists, or encodes some feasible schedule with horizon T. A Machine with k+1 tapes, q+1 states and tape alphabet Fin(g+3) is a partial transition function that, from a state and the tuple of symbols under the heads, either halts or gives a new state and, for each tape, a symbol to write and an optional head move. A configuration is a state plus the tapes; the initial configuration has state 0, the input on tape 0 using symbols 1 for false and 2 for true, and the other tapes empty. Each step applies the transition, run(t) iterates steps (staying put once halted), and Produces(input,out,timeBound) means that at some time t at most timeBound the machine has halted and tape 0, read from the head rightward, holds out in this symbol encoding. ReleaseTheorem is a defined proposition, not an established theorem: there exist k,q,g, a machine M and a constant C>0 such that for every n≥1 and every acyclic instance G on n vertices, and every optional deadline that, if present, lies between 1 and n, some correct output exists that M produces on encodeInput(G,deadline) within C·(length of that encoding+2)^150020 steps.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeMachine.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeMachine.lean; bytes 16..3530
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ThreeMachine

structure Instance (n : ℕ) where
  edges : List (Fin n × Fin n)

def Instance.edge {n : ℕ} (G : Instance n) (u v : Fin n) : Prop :=
  (u, v) ∈ G.edges

def Instance.acyclic {n : ℕ} (G : Instance n) : Prop :=
  ∀ v, ¬Relation.TransGen G.edge v v

def Feasible {n : ℕ} (G : Instance n) (T : ℕ) (τ : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ τ v ∧ τ v ≤ T) ∧
  (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun v => τ v = t)).card ≤ 3) ∧
  ∀ u v, G.edge u v → τ u < τ v

def encodeNat (n : ℕ) : List Bool :=
  let b := Computability.encodeNat n
  List.replicate b.length true ++ false :: b

def encodeList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  encodeNat xs.length ++ xs.flatMap f

def encodeInput {n : ℕ} (G : Instance n) (deadline : Option ℕ) : List Bool :=
  (match deadline with
    | none => [false]
    | some T => true :: encodeNat T) ++
  encodeList encodeNat ((List.range n).map (· + 1)) ++
  encodeList (fun (e : Fin n × Fin n) => encodeNat (e.1.val + 1) ++
    encodeNat (e.2.val + 1)) G.edges

def encodeAnswer : Option (List ℕ) → List Bool
  | none => [false]
  | some slots => true :: encodeList encodeNat slots

def slots {n : ℕ} (τ : Fin n → ℕ) : List ℕ := List.ofFn τ

def CorrectOutput {n : ℕ} (G : Instance n) (deadline : Option ℕ)
    (out : List Bool) : Prop :=
  match deadline with
  | none => ∃ T τ, Feasible G T τ ∧
      (∀ T' τ', Feasible G T' τ' → T ≤ T') ∧
      out = encodeAnswer (some (slots τ))
  | some T =>
      (out = encodeAnswer none ∧ ¬∃ τ, Feasible G T τ) ∨
      ∃ τ, Feasible G T τ ∧ out = encodeAnswer (some (slots τ))

structure Machine (k q g : ℕ) where
  transition : Fin (q + 1) → (Fin (k + 1) → Fin (g + 3)) →
    Option (Fin (q + 1) × (Fin (k + 1) → Fin (g + 3) × Option Turing.Dir))

structure Configuration (k q g : ℕ) where
  state : Fin (q + 1)
  tapes : Fin (k + 1) → Turing.Tape (Fin (g + 3))

def bitSymbol {g : ℕ} (b : Bool) : Fin (g + 3) :=
  if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

def Machine.step {k q g : ℕ} (M : Machine k q g)
    (c : Configuration k q g) : Option (Configuration k q g) := do
  let (state, action) ← M.transition c.state (fun i => (c.tapes i).head)
  return { state := state, tapes := fun i =>
    let tape := (c.tapes i).write (action i).1
    match (action i).2 with
    | none => tape
    | some d => tape.move d }

def Machine.initial {k q g : ℕ} (_M : Machine k q g)
    (input : List Bool) : Configuration k q g :=
  { state := 0, tapes := fun i =>
      Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) }

def Machine.run {k q g : ℕ} (M : Machine k q g) (input : List Bool)
    (t : ℕ) : Configuration k q g :=
  (fun c => (M.step c).getD c)^[t] (M.initial input)

def Machine.Produces {k q g : ℕ} (M : Machine k q g)
    (input out : List Bool) (timeBound : ℕ) : Prop :=
  ∃ t ≤ timeBound, M.step (M.run input t) = none ∧
    ((M.run input t).tapes 0).right₀ = Turing.ListBlank.mk (out.map bitSymbol)

def ReleaseTheorem : Prop :=
  ∃ (k q g : ℕ) (M : Machine k q g) (C : ℕ), 0 < C ∧
    ∀ n (G : Instance n), 1 ≤ n → G.acyclic →
      ∀ deadline : Option ℕ,
        (∀ T ∈ deadline, 1 ≤ T ∧ T ≤ n) →
        ∃ out, CorrectOutput G deadline out ∧
          M.Produces (encodeInput G deadline) out
            (C * ((encodeInput G deadline).length + 2) ^ 150020)



end ThreeMachine
end OAI


