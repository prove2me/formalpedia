-- Prove2me | Definitions.Def_bsv_merkle_width
-- name    : bsv_merkle_width
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T14:30:45.960394+00:00
-- url     : https://prove2.me/theorems/ca63e2ad-d1cc-498d-8ee4-647ed6bd5911
-- title:
--   Merkle computation with a W-bit leaf counter
-- statement:
--   The array-and-counter Merkle computation with a counter of width $W$. The counter is reduced modulo $2^W$ after each addition, and evaluating $1 \ll \mathrm{level}$ with $\mathrm{level} \ge W$ is reported as a fault; every array access is at a level that has just passed such a test.
--
--   `Fault.shift` marks an out-of-range level and `Fault.fuel` an exhausted step budget. `rootW` computes the root (`none` for an empty list) or a fault; `mutatedW` computes the duplicate-subtree flag or a fault.
--
--   **Formalization Note** This is a Lean model written for reasoning; nothing is claimed about any particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_literal
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle

section

variable {α : Type} (H : α → α → α)

inductive Fault
  | shift      -- `1 << level` with `level ≥ W`
  | fuel       -- the step budget ran out
  deriving DecidableEq, Repr

/-- `!(count & (1 << level))`, refusing a shift by `W` or more. Every array
access in the computation is at a level that has just passed this test. -/
def bitClearW (W count level : Nat) : Except Fault Bool :=
  if level < W then .ok (bitClear count level) else .error .shift

section

variable [DecidableEq α]

def leafCarryW (W : Nat) (inner : Nat → α) (count : Nat) :
    Nat → Nat → α → Bool → Except Fault (Nat × α × Bool)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, level, h, m =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true =>
      leafCarryW W inner count fuel (level + 1) (H (inner level) h) (m || inner level == h)
    | .ok false => .ok (level, h, m)

def addLeafW (W : Nat) (s : Lit α) (leaf : α) : Except Fault (Lit α) :=
  let c := (s.count + 1) % 2 ^ W
  match leafCarryW H W s.inner c (s.count + 1) 0 leaf s.mutated with
  | .error e => .error e
  | .ok r => .ok { inner := upd s.inner r.1 r.2.1, count := c, mutated := r.2.2 }

def runLeavesW (W : Nat) : Lit α → List α → Except Fault (Lit α)
  | s, [] => .ok s
  | s, a :: t =>
    match addLeafW H W s a with
    | .error e => .error e
    | .ok s' => runLeavesW W s' t

end

def skipLowW (W count : Nat) : Nat → Nat → Except Fault Nat
  | 0, _ => .error .fuel
  | fuel + 1, level =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true => skipLowW W count fuel (level + 1)
    | .ok false => .ok level

def sweepInnerW (W : Nat) (inner : Nat → α) (count : Nat) :
    Nat → Nat → α → Except Fault (Nat × α)
  | 0, _, _ => .error .fuel
  | fuel + 1, level, h =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true => sweepInnerW W inner count fuel (level + 1) (H (inner level) h)
    | .ok false => .ok (level, h)

def sweepOuterW (W : Nat) (inner : Nat → α) (F : Nat) : Nat → Nat → Nat → α → Except Fault α
  | 0, _, _, _ => .error .fuel
  | fuel + 1, count, level, h =>
    if level < W then
      if count != 1 <<< level then
        (sweepInnerW H W inner ((count + 1 <<< level) % 2 ^ W) F (level + 1) (H h h)).bind
          fun r => sweepOuterW W inner F fuel ((count + 1 <<< level) % 2 ^ W) r.1 r.2
      else .ok h
    else .error .shift

/-- Find the lowest occupied level, then sweep. -/
def finishW (W : Nat) (inner : Nat → α) (F fo count fs lvl : Nat) : Except Fault (Option α) :=
  (skipLowW W count fs lvl).bind fun level =>
    (sweepOuterW H W inner F fo count level (inner level)).bind fun h => .ok (some h)

section

variable [DecidableEq α] [Inhabited α]

/-- The root with a `W`-bit counter. -/
def rootW (W : Nat) (l : List α) : Except Fault (Option α) :=
  match l with
  | [] => .ok none
  | _ =>
    (runLeavesW H W start l).bind fun s =>
      finishW H W s.inner (s.count + 1) (s.count + 1) s.count (s.count + 1) 0

end

section

variable [DecidableEq α] [Inhabited α]

/-- The mutation flag with a `W`-bit counter. It is settled in the leaf phase,
before the sweep raises the counter. -/
def mutatedW (W : Nat) (l : List α) : Except Fault Bool :=
  (runLeavesW H W start l).map (·.mutated)

end

end

end Bsv.Merkle


