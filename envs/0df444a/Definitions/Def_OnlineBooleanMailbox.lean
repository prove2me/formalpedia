-- Prove2me | Definitions.Def_OnlineBooleanMailbox
-- name    : OnlineBooleanMailbox
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T04:12:01.930924+00:00
-- url     : https://prove2.me/theorems/9e5d455b-5399-5bc8-96e8-2dd125a97ff1
-- title:
--   A one-bit mailbox for interleaving one-way stream machines
-- statement:
--   A generator reads its raw input from left to right and emits at most one bit per step. The consumer may advance or retain its current virtual input position. The mailbox schedules the generator while empty and caches each output bit or end of input for the consumer.
-- source:
--   Operational semantics for a deterministic stream transducer and an online consumer.

import Mathlib

set_option autoImplicit false

namespace PvsNP.OnlineMailbox

/-- The producer has no access to future physical bits. Each tick requests
one physical bit, emits one virtual bit, or performs internal work. -/
inductive Action (S : Type)
  | read (next : Option Bool → S)
  | emit (bit : Bool) (next : S)
  | internal (next : S)
  | halt

abbrev Producer (G : Type) := G → Action G
abbrev Consumer (C : Type) := C → Option Bool → Option (C × Bool)
abbrev Source (G : Type) := G × List Bool
abbrev Virtual (C : Type) := C × List Bool

variable {G C : Type}

/-- A raw input request reads the current symbol and advances the one-way input.
At EOF, advancing the empty input leaves it empty. -/
def produce (p : Producer G) (x : Source G) : Option (Source G × Option Bool) :=
  match p x.1 with
  | .read k => some ((k x.2.head?, x.2.tail), none)
  | .emit bit next => some ((next, x.2), some bit)
  | .internal next => some ((next, x.2), none)
  | .halt => none

/-- The Boolean result of a consumer step indicates whether to advance. -/
def consume (c : Consumer C) (v : Virtual C) : Option (Virtual C) := do
  let (next, advance) ← c v.1 v.2.head?
  return (next, if advance then v.2.tail else v.2)

inductive Steps {S : Type} (tick : S → Option S) : ℕ → S → S → Prop
  | zero (x : S) : Steps tick 0 x x
  | next {n : ℕ} {x y z : S} :
      tick x = some y → Steps tick n y z → Steps tick (n + 1) x z

/-- A terminating standalone producer emits the specified word in exactly the
given number of successful transitions. The final halt is a separate observation. -/
inductive Produces (p : Producer G) : Source G → List Bool → ℕ → Prop
  | halt {x : Source G} : produce p x = none → Produces p x [] 0
  | next {x y : Source G} {bit : Option Bool} {tail : List Bool} {n : ℕ} :
      produce p x = some (y, bit) → Produces p y tail n →
      Produces p x (bit.toList ++ tail) (n + 1)

inductive Mailbox
  | waiting
  | ready (symbol : Option Bool)
  deriving DecidableEq, Fintype

structure Combined (G C : Type) where
  source : Source G
  consumer : C
  mailbox : Mailbox

/-- Advancing a cached bit empties the mailbox. EOF remains cached. -/
def afterConsumer (symbol : Option Bool) (advance : Bool) : Mailbox :=
  if advance && symbol.isSome then .waiting else .ready symbol

/-- Only the producer runs while the mailbox is empty. Only the consumer
runs once a bit or EOF is visible. -/
def step (p : Producer G) (c : Consumer C) (a : Combined G C) :
    Option (Combined G C) :=
  match a.mailbox with
  | .waiting =>
    match produce p a.source with
    | none => some ⟨a.source, a.consumer, .ready none⟩
    | some (source, bit) => some ⟨source, a.consumer,
        match bit with
        | none => .waiting
        | some b => .ready (some b)⟩
  | .ready symbol => do
    let (next, advance) ← c a.consumer symbol
    return ⟨a.source, next, afterConsumer symbol advance⟩

/-- The pending budget counts the remaining successful producer transitions
and one possible EOF observation. Cached EOF has no pending cost. -/
inductive Pending (p : Producer G) : Mailbox → Source G → List Bool → ℕ → Prop
  | waiting {x : Source G} {word : List Bool} {n : ℕ} :
      Produces p x word n → Pending p .waiting x word (n + 1)
  | bit {x : Source G} {b : Bool} {word : List Bool} {n : ℕ} :
      Produces p x word n → Pending p (.ready (some b)) x (b :: word) (n + 1)
  | eof (x : Source G) : Pending p (.ready none) x [] 0

end PvsNP.OnlineMailbox


