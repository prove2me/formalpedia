-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_RAM
-- name    : DOPriorityQueue_Construction_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:17.017585+00:00
-- url     : https://prove2.me/theorems/78901a1e-5b93-4651-b5a3-bede0c201a28
-- title:
--   §2.1 and Appendix B — charged instructions and opaque cells
-- statement:
--   A machine cell stores one fixed-width word or one indivisible opaque payload. Arithmetic, bit operations, shifts, comparisons, and most-significant-bit queries apply only to words. Payloads can only be copied, stored, read or discarded. Programs are finite instruction lists, with sixteen charged data registers, addressed private cells, and a passive addressed server.
--
--   Every instruction costs one unit. Each server read or write produces one address/direction probe; private accesses, contents, and elapsed time produce no probes. Reading an uninitialized addressed cell is stuck. A uniform random-word instruction consumes the next word of an external random tape.
--
--   Private and server footprints are computed from the actual initialized cells, with all sixteen data registers and the program counter included privately. The interpreter computes cumulative work, chronological probes and maximum footprints; programs do not supply these quantities. A call ends only at an explicit yield instruction.
--
--   This is a foundational instruction semantics. No implementation of Algorithms 1–4 or integer-set primitive is included here.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 3, §2.1; pp. 36–37, Appendix B

import Mathlib

set_option autoImplicit false

namespace DOPriorityQueue.Construction
namespace RAM

/-- Balls cannot be inspected or constructed by any arithmetic instruction. -/
inductive Cell (w : ℕ) (Ball : Type) where
  | word (value : BitVec w)
  | ball (value : Ball)
  deriving DecidableEq

/-- Address/operation only: contents, private accesses and time are absent. -/
structure Probe (w : ℕ) where
  address : BitVec w
  write : Bool
  deriving DecidableEq

abbrev Trace (w : ℕ) := List (List (Probe w))
abbrev Register := Fin 16

/-- No division, sorting, set operation, or uncharged host-language callback. -/
inductive Binary where
  | add | sub | mul | band | bor | bxor | shl | shr
  deriving DecidableEq

def Binary.eval {w : ℕ} : Binary → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .band, a, b => a &&& b
  | .bor, a, b => a ||| b
  | .bxor, a, b => a ^^^ b
  | .shl, a, b => a <<< b.toNat
  | .shr, a, b => a >>> b.toNat

/-- Fixed finite code; branch targets are instruction positions. -/
inductive Instruction where
  | constant (dst : Register) (value : ℕ)
  | copy (dst src : Register)
  | binary (op : Binary) (dst left right : Register)
  | bitNot (dst src : Register)
  | msb (dst src : Register)
  | privateLoad (dst address : Register)
  | privateStore (address src : Register)
  | privateErase (address : Register)
  | serverRead (dst address : Register)
  | serverWrite (address src : Register)
  | randomWord (dst : Register)
  | branchLT (left right : Register) (yes no : ℕ)
  | jump (next : ℕ)
  | yield
  deriving DecidableEq

/-- The PC and every data register are included in private space. -/
structure State (w : ℕ) (Ball : Type) where
  pc : ℕ
  registers : Register → Cell w Ball
  privateMemory : BitVec w → Option (Cell w Ball)
  serverMemory : BitVec w → Option (Cell w Ball)

/-- Sixteen data registers and the PC are always allocated, even at zero. -/
def privateWords {w : ℕ} {Ball : Type} (s : State w Ball) : ℕ :=
  17 + (Finset.univ.filter (fun a => (s.privateMemory a).isSome)).card

def serverWords {w : ℕ} {Ball : Type} (s : State w Ball) : ℕ :=
  (Finset.univ.filter (fun a => (s.serverMemory a).isSome)).card

def putRegister {w : ℕ} {Ball : Type} (s : State w Ball)
    (r : Register) (value : Cell w Ball) : State w Ball :=
  { s with registers := Function.update s.registers r value }

def getWord {w : ℕ} {Ball : Type} (s : State w Ball) (r : Register) : Option (BitVec w) :=
  match s.registers r with
  | .word x => some x
  | .ball _ => none

/-- One executed instruction, not a claimed cost supplied by an implementation. -/
structure Transition (w : ℕ) (Ball : Type) where
  state : State w Ball
  remainingCoins : List (BitVec w)
  probe : Option (Probe w)
  returned : Bool

/-- Missing private/server words are uninitialized: a read is stuck until written.
The finite coin list is an external semantic device, never client storage. -/
def step {w : ℕ} {Ball : Type} (program : List Instruction)
    (s : State w Ball) (coins : List (BitVec w)) : Option (Transition w Ball) := do
  let instruction ← program[s.pc]?
  let next := { s with pc := s.pc + 1 }
  let finish (s' : State w Ball) (coins' : List (BitVec w) := coins)
      (probe : Option (Probe w) := none) (returned : Bool := false) :=
    some (Transition.mk s' coins' probe returned)
  match instruction with
  | .constant dst n => finish (putRegister next dst (.word (BitVec.ofNat w n)))
  | .copy dst src => finish (putRegister next dst (s.registers src))
  | .binary op dst left right =>
    let a ← getWord s left
    let b ← getWord s right
    finish (putRegister next dst (.word (op.eval a b)))
  | .bitNot dst src =>
    let a ← getWord s src
    finish (putRegister next dst (.word (~~~a)))
  | .msb dst src =>
    let a ← getWord s src
    finish (putRegister next dst (.word (BitVec.ofNat w (Nat.log2 a.toNat))))
  | .privateLoad dst address =>
    let a ← getWord s address
    let value ← s.privateMemory a
    finish (putRegister next dst value)
  | .privateStore address src =>
    let a ← getWord s address
    finish { next with privateMemory := Function.update s.privateMemory a (some (s.registers src)) }
  | .privateErase address =>
    let a ← getWord s address
    finish { next with privateMemory := Function.update s.privateMemory a none }
  | .serverRead dst address =>
    let a ← getWord s address
    let value ← s.serverMemory a
    finish (putRegister next dst value) coins (some ⟨a, false⟩)
  | .serverWrite address src =>
    let a ← getWord s address
    finish { next with serverMemory := Function.update s.serverMemory a (some (s.registers src)) }
      coins (some ⟨a, true⟩)
  | .randomWord dst => match coins with
    | [] => none
    | x :: rest => finish (putRegister next dst (.word x)) rest
  | .branchLT left right yes no =>
    let a ← getWord s left
    let b ← getWord s right
    finish { next with pc := if a.toNat < b.toNat then yes else no }
  | .jump target => finish { next with pc := target }
  | .yield => finish next coins none true

/-- These are derived metrics, accumulated by the interpreter. They cannot be
chosen by a queue to certify its own resource bound. -/
structure CallResult (w : ℕ) (Ball : Type) where
  state : State w Ball
  remainingCoins : List (BitVec w)
  probes : List (Probe w)
  work : ℕ
  peakPrivate : ℕ
  peakServer : ℕ

/-- Fuel only limits this interpreter invocation. Termination is a separate
claim that some finite invocation returns, for each random tape. -/
def runCall {w : ℕ} {Ball : Type} (program : List Instruction) :
    ℕ → State w Ball → List (BitVec w) → Option (CallResult w Ball)
  | 0, _, _ => none
  | fuel + 1, s, coins => do
    let transition ← step program s coins
    if transition.returned then
      return ⟨transition.state, transition.remainingCoins, transition.probe.toList, 1,
        max (privateWords s) (privateWords transition.state),
        max (serverWords s) (serverWords transition.state)⟩
    else
      let rest ← runCall program fuel transition.state transition.remainingCoins
      return ⟨rest.state, rest.remainingCoins, transition.probe.toList ++ rest.probes,
        1 + rest.work, max (privateWords s) rest.peakPrivate,
        max (serverWords s) rest.peakServer⟩

/-- Independent uniform words give this exact mass to a consumed finite prefix.
A law of completed runs still needs to be constructed and normalized. -/
noncomputable def coinPrefixMass (w : ℕ) (coins : List (BitVec w)) : ENNReal :=
  (1 / (2 : ENNReal) ^ w) ^ coins.length

end RAM
end DOPriorityQueue.Construction


