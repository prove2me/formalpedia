-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Basic
-- name    : LeanPool_CircuitComplexity_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:34.341074+00:00
-- url     : https://prove2.me/theorems/719b873c-7275-46d8-bba1-b795b9d938fe
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean

module
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
abbrev BitString n := Fin n → Bool
abbrev BoolFunFamily := (N : Nat) → BitString N → Bool
inductive Arity where
  | unbounded
  | exactly (k : Nat)
  | upto (k : Nat)
  deriving Repr, DecidableEq
def Arity.satisfiedBy : Arity → Nat → Prop
  | .unbounded, _ => True
  | .exactly k, n => n = k
  | .upto k, n => n ≤ k
instance (a : Arity) (n : Nat) : Decidable (a.satisfiedBy n) := by
  cases a <;> simp only [Arity.satisfiedBy] <;> exact inferInstance
structure Basis where
  /-- The type of operations (e.g., AND, OR, NOT). -/
  Op : Type
  /-- The arity constraint for each operation. -/
  arity : Op → Arity
  /-- Evaluate an operation on `n` input bits, given that `n` satisfies the arity. -/
  eval : (op : Op) → (n : Nat) → (arity op).satisfiedBy n → BitString n → Bool
structure Gate (B : Basis) (W : Nat) where
  /-- The operation computed by this gate. -/
  op : B.Op
  /-- The number of inputs (fan-in) of this gate. -/
  fanIn : Nat
  /-- Proof that the fan-in satisfies the operation's arity constraint. -/
  arityOk : (B.arity op).satisfiedBy fanIn
  /-- Wiring: each gate input is connected to one of the `W` available wires. -/
  inputs : Fin fanIn → Fin W
  /-- Per-input negation flag. Negations are free in circuit complexity. -/
  negated : Fin fanIn → Bool
def Gate.eval (g : Gate B W) (wireVal : BitString W) : Bool :=
  B.eval g.op g.fanIn g.arityOk (fun i => (g.negated i).xor (wireVal (g.inputs i)))
structure Circuit (B : Basis) (N M G : Nat) [NeZero N] [NeZero M] where
  /-- The `G` internal gates of the circuit. -/
  gates : Fin G → Gate B (N + G)
  /-- The `M` output gates of the circuit. -/
  outputs : Fin M → Gate B (N + G)
  /-- Acyclicity: internal gate `i` only reads wires `0, …, N + i − 1`. -/
  acyclic : ∀ (i : Fin G) (k : Fin (gates i).fanIn),
    ((gates i).inputs k).val < N + i.val
namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
def wireValue (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun k => (gate.negated k).xor (c.wireValue input (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  simp_all
def wireDepth (c : Circuit B N M G) (w : Fin (N + G)) : Nat :=
  if h : w.val < N then
    0
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    1 + Fin.foldl gate.fanIn (fun acc k => max acc (c.wireDepth (gate.inputs k))) 0
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  simp_all
def outputDepth (c : Circuit B N M G) (j : Fin M) : Nat :=
  let outGate := c.outputs j
  1 + Fin.foldl outGate.fanIn (fun acc k => max acc (c.wireDepth (outGate.inputs k))) 0
def depth (c : Circuit B N M G) : Nat :=
  Fin.foldl M (fun acc j => max acc (c.outputDepth j)) 0
def eval (c : Circuit B N M G) (input : BitString N) : BitString M :=
  fun j => (c.outputs j).eval (c.wireValue input)
def size (c : Circuit B N M G) : Nat :=
  G + M + (c.outputs 0).fanIn * 0
end Circuit
class CompleteBasis (B : Basis) : Prop where
  complete : ∀ {N M} [NeZero N] [NeZero M] (f : BitString N → BitString M),
    ∃ G, ∃ c : Circuit B N M G, c.eval = f
namespace Circuit
variable {B : Basis} {N : Nat} [NeZero N]
noncomputable def sizeComplexity
    (B : Basis) (f : BitString N → Bool) : Nat :=
  sInf {s | ∃ G, ∃ c : Circuit B N 1 G, c.size = s ∧ (fun x => (c.eval x) 0) = f}
end Circuit
end CircuitComplexity


