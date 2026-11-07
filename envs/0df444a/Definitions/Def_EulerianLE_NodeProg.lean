-- Prove2me | Definitions.Def_EulerianLE_NodeProg
-- name    : EulerianLE_NodeProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:29.874056+00:00
-- url     : https://prove2.me/theorems/a02dafed-9b24-42b4-8992-cae40cdd490d
-- title:
--   Node programs, queue tests, composition of programs and algorithms
-- statement:
--   A **node program** for a node of degree $\deg$ is a deterministic automaton: a state space, an initial state and, for each state, the next instruction, one of
--
--   1. *send* a pulse through a port $i$;
--   2. a *local step* (local computation, which takes no time);
--   3. a *queue test* listing guards: a guard asks for at least $k\ge1$ pulses waiting at some port of a set and *selects the smallest such port*; the first guard of the list that succeeds fires, and a *take* guard also consumes the first pulse at the selected port (a consumption at one of several ports); if no guard succeeds, the test either blocks or continues;
--   4. *complete*, with an output.
--
--   Pulses carry no content, so a program sees the network only through the outcomes of its tests. An **operation on port $i$** is a send through $i$, a consumption at $i$ or an inspection of the queue of $i$; a test inspects every port of its guards.
--
--   The **composition** of programs runs the first program and, as soon as it completes with output $o$, the second program on input $o$. An **algorithm** assigns a program to every node, depending on the node's input; the composition $(A,B)$ of algorithms composes them node by node, with the output of $A$ as the input of $B$.
--
--   **Formalization Note** Several guards in one test model several blocked concurrent branches; the completion of the first program becomes a local step into the second.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, pp.7–8 (PDF pp.9–10): programs, instructions, operations on a port, observation; §3.1, p.8 (composition)

import Mathlib

namespace EulerianLE

/-- A queue test on a set of ports (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission (manuscript
sha256 90954a93…), §2, pp.7–8): it succeeds when at least `max need 1` pulses wait at some port of
`ports`, and then "selects the smallest port of the set at which at least k pulses are waiting".
With `take = true` it is a consumption of a pulse at one of several ports: the first pulse queued
at the selected port is also removed ("consumes the first pulse queued at one such port"). -/
structure Guard (deg : ℕ) where
  need : ℕ
  ports : Finset (Fin deg)
  take : Bool

/-- The port a guard selects, given the queue lengths `len`: the smallest port of the guard's set at
which at least `max need 1` pulses are waiting. -/
def Guard.select {deg : ℕ} (g : Guard deg) (len : Fin deg → ℕ) : Option (Fin deg) :=
  (List.finRange deg).find? fun p => decide (p ∈ g.ports) && decide (max g.need 1 ≤ len p)

/-- The first guard of a list that succeeds, counting indices from `n`: its index, the guard and its
selected port. -/
def fireFrom {deg : ℕ} (len : Fin deg → ℕ) : List (Guard deg) → ℕ → Option (ℕ × Guard deg × Fin deg)
  | [], _ => none
  | g :: gs, n =>
    match g.select len with
    | some p => some (n, g, p)
    | none => fireFrom len gs (n + 1)

/-- One step of a node program with local states `σ` and outputs `Out` (§2, p.7).

* `send i next`: send one pulse through port `i`.
* `tau next`: local computation, which takes no time.
* `test guards onFail onSucc`: the first guard of `guards` that succeeds fires (and, for a `take`
  guard, consumes), and the program continues at `onSucc index port`. If no guard succeeds,
  `onFail = none` blocks (a `wait until`, a `BlockingRecv`, a consumption at several ports, or several
  blocked concurrent branches at once), and `onFail = some s` continues at `s` (a queue test that
  does not block).
* `complete out`: the program returns or executes `terminate`, with output `out`.

**Formalization Note.** A program sees the network only through the outcomes of its tests, that is,
through queue lengths: pulses carry no content. -/
inductive Instr (deg : ℕ) (σ Out : Type) : Type
  | send (i : Fin deg) (next : σ)
  | tau (next : σ)
  | test (guards : List (Guard deg)) (onFail : Option σ) (onSucc : ℕ → Fin deg → σ)
  | complete (out : Out)

/-- A node's program, "the node-level list of instructions" (§2, p.7), as a deterministic automaton
with initial state `init` and next instruction `step s` in state `s`. -/
structure NodeProg (deg : ℕ) (Out : Type) where
  State : Type
  init : State
  step : State → Instr deg State Out

/-- The instruction is an operation on port `p`: "An operation on port i is a send through it, a
consumption at it, or an inspection of its input queue. A queue test inspects the input queue of
every port in its set, and so does a consumption of a pulse at one of several ports" (§2, p.7). -/
def Instr.Touches {deg : ℕ} {σ Out : Type} (ins : Instr deg σ Out) (p : Fin deg) : Prop :=
  match ins with
  | .send i _ => i = p
  | .test gs _ _ => ∃ g ∈ gs, p ∈ g.ports
  | _ => False

/-- Rename the continuation states of an instruction. -/
def Instr.map {deg : ℕ} {σ τ Out : Type} (f : σ → τ) : Instr deg σ Out → Instr deg τ Out
  | .send i n => .send i (f n)
  | .tau n => .tau (f n)
  | .test gs fl sc => .test gs (fl.map f) fun n p => f (sc n p)
  | .complete o => .complete o

/-- The composition of two node programs (§3.1, p.8): the node "first executes A and, as soon as it
completes A, starts executing B"; A's output is B's input. The completion of `a` becomes a local
step into the initial state of `b o`. -/
def NodeProg.comp {deg : ℕ} {O₁ O₂ : Type} (a : NodeProg deg O₁) (b : O₁ → NodeProg deg O₂) :
    NodeProg deg O₂ where
  State := a.State ⊕ Σ o : O₁, (b o).State
  init := .inl a.init
  step
    | .inl s =>
      match a.step s with
      | .send i n => .send i (.inl n)
      | .tau n => .tau (.inl n)
      | .test gs fl sc => .test gs (fl.map .inl) fun n p => .inl (sc n p)
      | .complete o => .tau (.inr ⟨o, (b o).init⟩)
    | .inr ⟨o, s⟩ => ((b o).step s).map fun n => .inr ⟨o, n⟩

/-- A (distributed) algorithm "assigns a program to every node, not necessarily the same one" (§2,
p.7); the program of `u` may depend on `u`'s input, of type `In u`, and produces an output of type
`Out u`. -/
def Algorithm (V : Type) (deg : V → ℕ) (In Out : V → Type) : Type 1 :=
  ∀ u, In u → NodeProg (deg u) (Out u)

/-- The composition `(A, B)` of two algorithms (§3.1, p.8): every node runs its program of `A` and
then, on `A`'s output, its program of `B`. -/
def Algorithm.comp {V : Type} {deg : V → ℕ} {In O₁ O₂ : V → Type} (A : Algorithm V deg In O₁)
    (B : Algorithm V deg O₁ O₂) : Algorithm V deg In O₂ :=
  fun u x => (A u x).comp (B u)

end EulerianLE


