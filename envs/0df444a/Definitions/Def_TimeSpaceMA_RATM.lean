-- Prove2me | Definitions.Def_TimeSpaceMA_RATM
-- name    : TimeSpaceMA_RATM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:07.205487+00:00
-- url     : https://prove2.me/theorems/5eb038e7-8c4d-4892-9c9e-5260d76a9be8
-- title:
--   Deterministic Turing machine with random-access input
-- statement:
--   A **random-access Turing machine** has finitely many states, a finite tape alphabet with a blank symbol, $k$ two-way infinite work tapes, distinct accepting and rejecting states, and an address register holding a natural number $a$.
--
--   On an input $x$ of length $n$, one step reads the state, the $k$ scanned work symbols and the input symbol $x_a$ (or "out of range" when $a = n$). It then writes one symbol and moves one head per tape, and either keeps the register, clears it, or pushes a bit $b$, which sets $a := \min(2a + b, n)$. Accepting and rejecting states are fixed points of the step.
--
--   Space is the number of distinct (tape, position) cells scanned, the start cells included. Because the register saturates at $n$, it holds $O(\log n)$ bits and is not free storage; the paper's $S = s + O(\log nt)$ pays for it.
--
--   **Formalization Note** The paper names this model on p.6 and fixes no further details. The Lean structure leaves the alphabet and $k$ free.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §2, p.6

import Mathlib

namespace TimeSpaceMA

/-- Head movement of a work tape. -/
inductive Move
  | left
  | stay
  | right

/-- Displacement of a head under a move. -/
def Move.delta : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Operation on the address register of a random-access input. -/
inductive AddrOp
  | keep
  | clear
  | push (b : Bool)

/-- Deterministic Turing machine with random-access input (Williams, Xi, Short Non-Interactive
Proofs for Time-Space Computations, STOC 2027 submission, manuscript sha256 184c2f95…, §2, p.6:
"deterministic Turing machine with random-access input").

Finite states and alphabet, `k` two-way infinite work tapes, and an address register. A step sees
the state, the `k` scanned work symbols and the input symbol at the register (`none` when the
register is out of range), and returns a new state, a symbol and a move per tape, and a register
operation.

**Formalization Note** The page names the model without fixing its details; `paper.md`, decision 3.
The alphabet, `k` and the `Option Bool` read are more general than the bit reads of the proof; they
change the costs by constant factors. -/
structure RATM where
  Q : Type
  [fintypeQ : Fintype Q]
  Γ : Type
  [fintypeΓ : Fintype Γ]
  blank : Γ
  k : ℕ
  q₀ : Q
  qaccept : Q
  qreject : Q
  accept_ne_reject : qaccept ≠ qreject
  δ : Q → (Fin k → Γ) → Option Bool → Q × (Fin k → Γ × Move) × AddrOp

namespace RATM

/-- A configuration on an input: state, tape contents, head positions, address register. -/
structure Config (M : RATM) where
  state : M.Q
  tape : Fin M.k → ℤ → M.Γ
  head : Fin M.k → ℤ
  addr : ℕ

/-- The start configuration: blank tapes, heads at `0`, register `0`. -/
def initial (M : RATM) : M.Config :=
  ⟨M.q₀, fun _ _ => M.blank, fun _ => 0, 0⟩

/-- Register update on an input of length `n`. `push b` is `a ↦ min (2a + b) n`: the register holds
`O(log n)` bits and cannot serve as free storage. -/
def applyAddr (n : ℕ) : AddrOp → ℕ → ℕ
  | .keep, a => a
  | .clear, _ => 0
  | .push b, a => min (2 * a + b.toNat) n

open Classical in
/-- One step on input `x`. Accepting and rejecting states stutter. -/
noncomputable def step (M : RATM) (x : List Bool) (c : M.Config) : M.Config :=
  if c.state = M.qaccept ∨ c.state = M.qreject then c
  else
    let out := M.δ c.state (fun i => c.tape i (c.head i)) x[c.addr]?
    { state := out.1
      tape := fun i => Function.update (c.tape i) (c.head i) (out.2.1 i).1
      head := fun i => c.head i + (out.2.1 i).2.delta
      addr := applyAddr x.length out.2.2 c.addr }

/-- The configuration after `T` steps on `x`. -/
noncomputable def run (M : RATM) (x : List Bool) (T : ℕ) : M.Config :=
  (M.step x)^[T] M.initial

/-- The (tape, position) cells scanned during the first `T` steps on `x`, the start cells included. -/
noncomputable def scanned (M : RATM) (x : List Bool) (T : ℕ) : Finset (Fin M.k × ℤ) :=
  (Finset.range (T + 1)).biUnion fun τ =>
    Finset.univ.image fun i => (i, (M.run x τ).head i)

end RATM

end TimeSpaceMA


