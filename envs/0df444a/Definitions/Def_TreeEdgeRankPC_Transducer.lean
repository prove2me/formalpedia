-- Prove2me | Definitions.Def_TreeEdgeRankPC_Transducer
-- name    : TreeEdgeRankPC_Transducer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:29.738575+00:00
-- url     : https://prove2.me/theorems/ba800708-c691-439b-b7cd-96754f06d14c
-- title:
--   Deterministic transducers with a read-only input, one work tape and a write-only output
-- statement:
--   A **transducer** is a deterministic machine with finitely many states, a read-only input tape with end markers, one work tape over a finite alphabet, and a write-only output: each step may print one bit. It computes on an input word $x$ by repeatedly applying its transition function, halts on entering a halting state, and its output is the string it has printed. Its **workspace** on $x$ is the largest number of work cells held by a configuration of the run.
--
--   The paper uses this machine for one purpose: a circuit family is logspace-uniform if a deterministic transducer outputs $C_n$ from $1^n$ using $O(\log n)$ workspace.
--
--   **Formalization Note** The paper does not fix the model further. This is the standard one, with the work tape in the configuration style of the published `CookPvsNP.TM` (infinite in both directions, blank `none`), plus a "stay" move. Machines with several work tapes use the same space up to a constant factor. `ComputesWithin x y s` says that the machine halts on $x$ with output $y$ and that every configuration of the run has at most $s$ work cells.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.12 (logspace-uniform)

import Mathlib

namespace TreeEdgeRankPC

/-- A symbol read on the input tape: an end marker or a bit. -/
inductive InSym where
  | leftEnd
  | bit (b : Bool)
  | rightEnd

/-- A head movement of a transducer. -/
inductive Dir where
  | left
  | stay
  | right

/-- A deterministic **transducer**, for the sentence of §3.2, p.12 (arXiv:2610.12438, held version of
2026-11-02, sha256 9e04ca7b…): "A circuit family (C_n)_{n≥1} is logspace-uniform if a deterministic
transducer outputs C_n from 1^n using O(log n) workspace [GHR95]."

**Formalization Note.** The paper does not fix the machine model further. This is the standard model:
finitely many states, a read-only input tape with end markers, one work tape over a finite alphabet
(blank = `none`, the same convention as the published `CookPvsNP.TM`), and a write-only output: each
step may print one bit. Machines with several work tapes use the same space up to a constant factor. -/
structure Transducer where
  /-- The finite set of states. -/
  Q : Type
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  /-- The finite work alphabet (without the blank). -/
  Γ : Type
  [finΓ : Fintype Γ]
  /-- The initial state. -/
  start : Q
  /-- The halting states. -/
  halting : Q → Bool
  /-- `δ q a s = (q', s', dw, di, o)`: in state `q`, reading `a` on the input tape and `s` on the work
  tape, enter `q'`, write `s'`, move the work head by `dw` and the input head by `di`, and print `o`. -/
  δ : Q → InSym → Option Γ → Q × Option Γ × Dir × Dir × Option Bool

namespace Transducer

variable (M : Transducer)

/-- A configuration: state, input head position (`0` is the left end marker, `|x| + 1` the right one),
the work tape to the left of the head (nearest square first), the scanned work square, the work tape to
the right of the head, and the bits printed so far. -/
structure Cfg where
  state : M.Q
  inPos : ℕ
  left : List (Option M.Γ)
  head : Option M.Γ
  right : List (Option M.Γ)
  out : List Bool

variable {M}

/-- The workspace of a configuration: the number of work cells stored in it. Cells enter a
configuration only when the head visits them. -/
def Cfg.space (c : M.Cfg) : ℕ := c.left.length + 1 + c.right.length

/-- The symbol at position `p` of the input tape for the word `x`. -/
def readInput (x : List Bool) (p : ℕ) : InSym :=
  if p = 0 then InSym.leftEnd else
    match x[p - 1]? with
    | some b => InSym.bit b
    | none => InSym.rightEnd

/-- One work-tape update: write `s` on the scanned square, then move by `d`. The tape is infinite in
both directions, as in the published `CookPvsNP.TM`. -/
def moveWork (s : Option M.Γ) (l : List (Option M.Γ)) (r : List (Option M.Γ)) :
    Dir → List (Option M.Γ) × Option M.Γ × List (Option M.Γ)
  | .stay => (l, s, r)
  | .right => (s :: l, r.headD none, r.tail)
  | .left => (l.tail, l.headD none, s :: r)

/-- One input-head update, confined to the tape `[0, |x| + 1]`. -/
def moveInput (x : List Bool) (p : ℕ) : Dir → ℕ
  | .stay => p
  | .left => p - 1
  | .right => min (p + 1) (x.length + 1)

variable (M)

/-- One computation step on input `x`; halting configurations do not change. -/
def step (x : List Bool) (c : M.Cfg) : M.Cfg :=
  if M.halting c.state then c else
    let t := M.δ c.state (readInput x c.inPos) c.head
    let w := moveWork t.2.1 c.left c.right t.2.2.1
    { state := t.1
      inPos := moveInput x c.inPos t.2.2.2.1
      left := w.1
      head := w.2.1
      right := w.2.2
      out := c.out ++ t.2.2.2.2.toList }

/-- The initial configuration: blank work tape, input head on the left end marker, nothing printed. -/
def init : M.Cfg :=
  { state := M.start, inPos := 0, left := [], head := none, right := [], out := [] }

/-- The configuration after `t` steps on input `x`. -/
def run (x : List Bool) (t : ℕ) : M.Cfg := (M.step x)^[t] M.init

/-- On input `x` the transducer halts with the printed output `y`, and every configuration of its run
uses at most `s` work cells. -/
def ComputesWithin (x y : List Bool) (s : ℕ) : Prop :=
  (∃ t, M.halting (M.run x t).state = true ∧ (M.run x t).out = y) ∧
    ∀ t, (M.run x t).space ≤ s

end Transducer

end TreeEdgeRankPC


