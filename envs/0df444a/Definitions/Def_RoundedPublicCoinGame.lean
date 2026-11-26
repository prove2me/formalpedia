-- Prove2me | Definitions.Def_RoundedPublicCoinGame
-- name    : RoundedPublicCoinGame
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T17:34:55.401828+00:00
-- url     : https://prove2.me/theorems/f4040c76-f17f-40b5-b4f1-503090a9daed
-- title:
--   Finite-horizon public-coin games with integer labels
-- statement:
--   A game with an observable state and a finite move budget. At each position the game stops, allows the prover to choose a successor, or chooses a successor by a fair coin. The module defines the exact optimal score numerator, a local check for a scaled integer label, and the condition that checked positions are closed under successors.
-- source:
--   Direct finite-horizon game recurrence and integer rounding. Original standalone formalization.

import Mathlib.Data.Nat.Size


set_option autoImplicit false

namespace PvsNP.PublicGame

variable {S : Type}

/-- A bit-level game. A deterministic move is `pick s s`. Control and
both successors must be recoverable from the prover-observable state. -/
inductive Move (S : Type)
  | stop (accept : Bool)
  | pick (zero one : S)
  | toss (zero one : S)

/-- `r` is remaining fuel; expiry is acceptance only in an accepting
terminal state. Both successors use one unit of fuel. -/
structure Game (S : Type) where
  move : ℕ → S → Move S

def finish (G : Game S) (s : S) : ℕ :=
  match G.move 0 s with
  | .stop true => 1
  | _ => 0

/-- Optimal number of accepting fresh-coin strings of length `r`.
Unused coin bits are freely padded at a terminal or prover move. -/
def value (G : Game S) : ℕ → S → ℕ
  | 0,s => finish G s
  | r+1,s =>
    match G.move (r+1) s with
    | .stop b => if b then 2^(r+1) else 0
    | .pick s₀ s₁ => 2*max (value G r s₀) (value G r s₁)
    | .toss s₀ s₁ => value G r s₀ + value G r s₁

/-- The right-hand side of the update equation for twice a scaled probability. -/
def doubleUpdate (G : Game S) (M : ℕ) (u : ℕ → S → ℕ) : ℕ → S → ℕ
  | 0, s => 2 * (M * finish G s)
  | r+1, s =>
    match G.move (r+1) s with
    | .stop b => if b then 2*M else 0
    | .pick s₀ s₁ => 2 * max (u r s₀) (u r s₁)
    | .toss s₀ s₁ => u r s₀ + u r s₁

/-- A terminal does not require any more labels. -/
def children : Move S → List S
  | .stop _ => []
  | .pick a b | .toss a b => [a,b]

/-- Local integer labels use a common scale and allow one unit of doubled
rounding error. The checker only inspects a state and its successors. -/
def LabelValid (G : Game S) (M : ℕ) (u : ℕ → S → ℕ) (r : ℕ) (s : S) : Prop :=
  u r s ≤ M ∧
  2 * u r s ≤ doubleUpdate G M u r s + 1 ∧
  doubleUpdate G M u r s ≤ 2 * u r s + 1

def LocallyRounded (G : Game S) (M H : ℕ) (u : ℕ → S → ℕ) : Prop :=
  ∀ r ≤ H, ∀ s, LabelValid G M u r s

/-- Labels only need to be checked on a successor-closed set that
contains the starting state. -/
def LocallyRoundedOn (G : Game S) (M H : ℕ) (u : ℕ → S → ℕ)
    (active : ℕ → S → Prop) : Prop :=
  (∀ r ≤ H, ∀ s, active r s → LabelValid G M u r s) ∧
  (∀ r < H, ∀ s, active (r+1) s →
    ∀ q ∈ children (G.move (r+1) s), active r q)

/-- Rounding the true value down always gives an admissible label function. -/
def floorValue (G : Game S) (M : ℕ) (r : ℕ) (s : S) : ℕ :=
  M * value G r s / 2^r

end PvsNP.PublicGame


