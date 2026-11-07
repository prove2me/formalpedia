-- Prove2me | Definitions.Def_BeyondDS_Prog
-- name    : BeyondDS_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:55.317198+00:00
-- url     : https://prove2.me/theorems/1543c33a-9c20-4faf-96d5-483e5adf5ce2
-- title:
--   Programs in direct style and the protocol of a program
-- statement:
--   A program of an honest player is a finite tree of operations: either it returns, or it performs an operation and continues with a program depending on the model's answer, or it publishes a value as the readable part of its local state (a bookkeeping step that is not an operation of the model). Programs compose sequentially, and sign, verify, sample, send, yield (returning the delivered messages and the election output), decide and halt are programs. A program yields a protocol: the local state is the rest of the program as a function of the next answer, together with the readable part, and a finished program halts. A corruption reveals both.
--
--   This is how the protocols of §§5, 7 and 8 are written: "Descriptions prescribe honest behavior".
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.1, p.14 (PDF p.15); §7.4, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_BeyondDS_Protocol

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- An honest player's program in direct style: a finite tree of operations, with the continuation of each
operation depending on the model's answer. `note v` publishes `v` as the readable part of the local state; it
is not an operation of the model and takes no time. This is how the protocols of §§5, 7, 8 are written. -/
inductive Prog (Msg V α : Type) where
  | ret (a : α)
  | op (o : Op Msg) (k : Resp Msg → Prog Msg V α)
  | note (v : V) (k : Prog Msg V α)

namespace Prog

variable {Msg V α β : Type}

/-- Sequential composition of programs. -/
def bind : Prog Msg V α → (α → Prog Msg V β) → Prog Msg V β
  | ret a, f => f a
  | op o k, f => op o fun r => (k r).bind f
  | note v k, f => note v (k.bind f)

instance : Monad (Prog Msg V) where
  pure := ret
  bind := bind

/-- Sign a batch; the answer is one signature per message. -/
def signAll (ms : List Str) : Prog Msg V (List Str) :=
  op (Op.signAll ms) fun r =>
    match r with
    | Resp.signatures ss => ret ss
    | _ => ret []

/-- Verify a batch; the answer is one verdict per query. -/
def verifyAll (qs : List (ℕ × Str × Str)) : Prog Msg V (List Bool) :=
  op (Op.verifyAll qs) fun r =>
    match r with
    | Resp.verdicts vs => ret vs
    | _ => ret []

/-- A fresh value uniform on `{0, …, N}`. -/
def sample (N : ℕ) : Prog Msg V ℕ :=
  op (Op.sample N) fun r =>
    match r with
    | Resp.sampled k => ret k
    | _ => ret 0

/-- One transmission. -/
def send (j : ℕ) (m : Msg) : Prog Msg V Unit :=
  op (Op.send j m) fun _ => ret ()

/-- End the round; the answer is what the boundary delivered, and the election output if any. -/
def yield : Prog Msg V (List (ℕ × Msg) × Option ℕ) :=
  op Op.yield fun r =>
    match r with
    | Resp.boundary i e => ret (i, e)
    | _ => ret ([], none)

/-- Decide. -/
def decide (b : Bool) : Prog Msg V Unit :=
  op (Op.decide b) fun _ => ret ()

/-- Halt. -/
def halt : Prog Msg V Unit :=
  op Op.halt fun _ => ret ()

/-- Publish the readable part of the local state. -/
def save (v : V) : Prog Msg V Unit :=
  note v (ret ())

end Prog

/-- The local state of a player running a `Prog`: what remains of the program, as a function of the next answer,
and the readable part. A corruption reveals both. -/
structure ProgState (Msg V : Type) where
  k : Resp Msg → Prog Msg V Unit
  view : V

/-- The next operation of a program. A finished program halts. -/
def stepProg {Msg V : Type} : Prog Msg V Unit → V → Op Msg × ProgState Msg V
  | Prog.ret _, v => (Op.halt, ⟨fun _ => Prog.ret (), v⟩)
  | Prog.op o k, v => (o, ⟨k, v⟩)
  | Prog.note v' k, _ => stepProg k v'

/-- A protocol from a program, with the public caps given. -/
def Protocol.ofProg {Msg V : Type} (v₀ : V) (main : (P : Params) → Fin P.n → Option Bool → Prog Msg V Unit)
    (roundCap opCap : Params → ℕ) (electAt : Params → ℕ → Bool) : Protocol Msg (ProgState Msg V) where
  init := fun P i x => ⟨fun _ => main P i x, v₀⟩
  next := fun _ s r => stepProg (s.k r) s.view
  roundCap := roundCap
  opCap := opCap
  electAt := electAt

end BeyondDS


