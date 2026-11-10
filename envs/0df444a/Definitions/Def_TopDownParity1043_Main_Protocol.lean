-- Prove2me | Definitions.Def_TopDownParity1043_Main_Protocol
-- name    : TopDownParity1043_Main_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:18:04.78671+00:00
-- url     : https://prove2.me/theorems/44572320-6e25-49a0-8c15-9913cb43f7f4
-- title:
--   §1.1 — deterministic protocols with rounds and per-message cost
-- statement:
--   A deterministic protocol is a finite tree for Alice's input $x\in A$, Bob's input $y\in B$, and public outputs in a set $O$. Each internal node fixes the speaker, a number $k$ of message choices, a function of that speaker's input into those choices, and a continuation for each message. Different transcripts may choose different speakers. Leaves contain an output or no output.
--
--   The resource bounds are
--   $$\operatorname{rounds}(P)\le d,\qquad k\le2^m\text{ at every internal node}.$$
--
--   The function $\operatorname{run}(P,x,y)$ follows the indicated messages to the leaf. Rounds count messages; $m$ bounds the number of bits in each message. This operational interface supports search problems and separates the two resources used by the paper. The subsequent KW correctness condition forbids a missing output on every actual input pair.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), §1.1, deterministic protocol model, p. 2

import Mathlib

set_option autoImplicit false

namespace TopDownParity1043.Main

/-- §1.1, pp.2–3: finite deterministic protocols. The transcript fixes the speaker.
`none` is a no-output leaf, permitted by correctness only on an empty reached rectangle. -/
inductive Protocol (A B O : Type) where
  | leaf (output : Option O)
  | alice (k : ℕ) (message : A → Fin k) (next : Fin k → Protocol A B O)
  | bob (k : ℕ) (message : B → Fin k) (next : Fin k → Protocol A B O)

namespace Protocol

variable {A B O : Type}

/-- Number of messages on the longest branch; leaves have height zero. -/
def rounds : Protocol A B O → ℕ
  | .leaf _ => 0
  | .alice k _ next => 1 + Finset.univ.sup (fun j : Fin k => (next j).rounds)
  | .bob k _ next => 1 + Finset.univ.sup (fun j : Fin k => (next j).rounds)

/-- Every message has at most `2^m` possibilities, independently of the number of rounds. -/
def CostBounded (m : ℕ) : Protocol A B O → Prop
  | .leaf _ => True
  | .alice k _ next => k ≤ 2 ^ m ∧ ∀ j, (next j).CostBounded m
  | .bob k _ next => k ≤ 2 ^ m ∧ ∀ j, (next j).CostBounded m

/-- The public leaf output reached on an actual pair of inputs. -/
def run : Protocol A B O → A → B → Option O
  | .leaf o, _, _ => o
  | .alice _ msg next, x, y => (next (msg x)).run x y
  | .bob _ msg next, x, y => (next (msg y)).run x y

end Protocol

end TopDownParity1043.Main


