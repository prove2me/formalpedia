-- Prove2me | Definitions.Def_EulerianLE_IsComposable
-- name    : EulerianLE_IsComposable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:58.53173+00:00
-- url     : https://prove2.me/theorems/62a1b64e-1d18-48e9-9197-0ff449d0dd35
-- title:
--   Termination, quiescent termination and composability
-- statement:
--   For an algorithm $A$ and a class $I$ of input tuples:
--
--   1. $A$ **terminates on $I$** if every node completes in every standalone execution (fair run) on every input of $I$;
--   2. $A$ **terminates quiescently** if moreover every pulse sent to a node is consumed before that node completes;
--   3. (Definition 1) $A$ is **composable on $I$** if it terminates on $I$ and, for every algorithm $B$ whose input is $A$'s output and every standalone execution of $(A,B)$ on an input of $I$, no node observes an $A$-pulse while it executes $B$, and no node observes a $B$-pulse while it executes $A$. Pulses sent from a state of $A$ are $A$-pulses, those sent from a state of $B$ are $B$-pulses.
--
--   The module also defines the traces of phase $A$ and of phase $B$ of a node in an execution of $(A,B)$, which Lemma 6 compares with standalone executions of $A$ and of $B$.
--
--   Composability is the property that lets the phases of a composition be analysed separately, although pulses of different phases are indistinguishable to the nodes.
--
--   **Formalization Note** $B$ ranges over every algorithm with any output types.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.8 (termination, quiescent termination); §3.1, pp.8–9 (PDF pp.10–11), Definition 1

import Mathlib
import Definitions.Def_EulerianLE_Run

namespace EulerianLE

variable {G : Network} {In O₁ O₂ : G.V → Type}

/-- The node programs of an algorithm on the input tuple `x`. -/
def Algorithm.progs (A : Algorithm G.V G.deg In O₁) (x : ∀ v, In v) :
    ∀ v, NodeProg (G.deg v) (O₁ v) :=
  fun v => A v (x v)

/-- `A` terminates on the class of inputs `I`: "every node eventually completes it in every standalone
execution on that input" (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission (manuscript sha256
90954a93…), §2, p.8). A standalone execution under a scheduler is a fair run from the start. -/
def TerminatesOn (A : Algorithm G.V G.deg In O₁) (I : Set (∀ v, In v)) : Prop :=
  ∀ x ∈ I, ∀ ρ : Run (A.progs x) (stdTag _), IsFair ρ → ∀ v, ∃ o, ρ.CompletesWith v o

/-- `A` terminates quiescently on `I` (§2, p.8): it terminates, and in every standalone execution every
pulse sent to a node is consumed before that node completes. -/
def QuiescentOn (A : Algorithm G.V G.deg In O₁) (I : Set (∀ v, In v)) : Prop :=
  TerminatesOn A I ∧ ∀ x ∈ I, ∀ ρ : Run (A.progs x) (stdTag _), IsFair ρ → ρ.Quiescent

/-- The phase labels of a composition `(A, B)`: a pulse sent from a state of `A` is an A-pulse
(`first`), one sent from a state of `B` a B-pulse (`second`) (§3.1, p.8). -/
def compTag (A : Algorithm G.V G.deg In O₁) (B : Algorithm G.V G.deg O₁ O₂) (x : ∀ v, In v) :
    Tag ((A.comp B).progs x) :=
  fun _ s =>
    match s with
    | .inl _ => .first
    | .inr _ => .second

/-- Definition 1 (Composability), p.9: `A` terminates on every input in `I`, and for every algorithm
`B` and every standalone execution of `(A, B)` on an input in `I`, (1) no node observes an A-pulse
while it executes B, and (2) no node observes a B-pulse while it executes A.

**Formalization Note.** `B` ranges over every algorithm whose input at each node is `A`'s output
type there ("assuming correct output-input relations", p.9), with any output types `O₂`. A node
executes A while its state of the composition is a state of `A` (`inl`) and B while it is a state
of `B` (`inr`). -/
def IsComposable (A : Algorithm G.V G.deg In O₁) (I : Set (∀ v, In v)) : Prop :=
  TerminatesOn A I ∧
  ∀ (O₂ : G.V → Type) (B : Algorithm G.V G.deg O₁ O₂), ∀ x ∈ I,
    ∀ ρ : Run ((A.comp B).progs x) (compTag A B x), IsFair ρ →
      ∀ t v, ρ.ev t = some (.op v) →
        (∀ s, (ρ.cfg t).status v = .running (.inr s) → Phase.first ∉ (ρ.cfg t).observed v) ∧
        (∀ s, (ρ.cfg t).status v = .running (.inl s) → Phase.second ∉ (ρ.cfg t).observed v)

/-- The status in `A` corresponding to a status in the composition `(A, B)`, for a node that is still
in phase A or has just left it: a state of `B` means that `A` has completed with the output stored
there. -/
def projA {σ : Type} {O₁' : Type} {τ : O₁' → Type} {Out : Type} :
    Status (σ ⊕ Σ o : O₁', τ o) Out → Status σ O₁'
  | .running (.inl s) => .running s
  | .running (.inr ⟨o, _⟩) => .completed o
  | _ => .asleep

/-- The status in `B` corresponding to a status in the composition `(A, B)`, recording `B`'s input
next to its state. -/
def projB {σ : Type} {O₁' : Type} {τ : O₁' → Type} {Out : Type} :
    Status (σ ⊕ Σ o : O₁', τ o) Out → Status (Σ o : O₁', τ o) Out
  | .running (.inr s) => .running s
  | .completed o => .completed o
  | _ => .asleep

/-- The status of a standalone execution of `B` on input `o`, with the input recorded next to the
state. -/
def liftB {O₁' : Type} {τ : O₁' → Type} {Out : Type} (o : O₁') :
    Status (τ o) Out → Status (Σ o : O₁', τ o) Out
  | .running s => .running ⟨o, s⟩
  | .completed z => .completed z
  | .asleep => .asleep

/-- The trace of phase A of node `v` in an execution of `(A, B)`, up to time `t`: the wake-up of `v` and
each operation of `v` performed in a state of `A`, with its visible operation and the resulting status
of `A`. The operation that leaves A for B is `A`'s completion. -/
def Run.phaseATrace {A : Algorithm G.V G.deg In O₁} {B : Algorithm G.V G.deg O₁ O₂} {x : ∀ v, In v}
    {tag : Tag ((A.comp B).progs x)} (ρ : Run ((A.comp B).progs x) tag) (v : G.V) (t : ℕ) :
    List (Option (Act (G.deg v)) × Status (A v (x v)).State (O₁ v)) :=
  (List.range t).filterMap fun k =>
    match ρ.ev k with
    | some (.wake w) => if w = v then some (none, projA ((ρ.cfg (k + 1)).status v)) else none
    | some (.op w) =>
      if w = v then
        match (ρ.cfg k).status v, (ρ.cfg (k + 1)).status v with
        | .running (.inl _), .running (.inr ⟨o, _⟩) => some (some .complete, .completed o)
        | .running (.inl _), st => some ((ρ.cfg k).act v, projA st)
        | _, _ => none
      else none
    | _ => none

/-- The trace of phase B of node `v` in an execution of `(A, B)`, up to time `t`: the entry of `v` into
B (as a wake-up) and each operation of `v` performed in a state of `B`, with its visible operation and
the resulting status of `B`. -/
def Run.phaseBTrace {A : Algorithm G.V G.deg In O₁} {B : Algorithm G.V G.deg O₁ O₂} {x : ∀ v, In v}
    {tag : Tag ((A.comp B).progs x)} (ρ : Run ((A.comp B).progs x) tag) (v : G.V) (t : ℕ) :
    List (Option (Act (G.deg v)) × Status (Σ o : O₁ v, (B v o).State) (O₂ v)) :=
  (List.range t).filterMap fun k =>
    match ρ.ev k with
    | some (.op w) =>
      if w = v then
        match (ρ.cfg k).status v, (ρ.cfg (k + 1)).status v with
        | .running (.inl _), .running (.inr s) => some (none, .running s)
        | .running (.inr _), st => some ((ρ.cfg k).act v, projB st)
        | _, _ => none
      else none
    | _ => none

end EulerianLE


