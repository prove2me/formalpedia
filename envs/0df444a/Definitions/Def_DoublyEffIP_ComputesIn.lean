-- Prove2me | Definitions.Def_DoublyEffIP_ComputesIn
-- name    : DoublyEffIP_ComputesIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:11.604999+00:00
-- url     : https://prove2.me/theorems/73ae5d89-8cbd-4e05-bda3-b3265f647a7f
-- title:
--   Computing an output word in exactly $t$ steps
-- statement:
--   A machine $M$ **computes** the word $y$ from the input $w$ **in $t$ steps**, on its output tape $o$, if it halts at step $t$ on $w$ and at that moment tape $o$ holds exactly $y$, with the head on its first cell and blanks everywhere else.
--
--   This is how the parameter machine outputs the round count and message length, and how the prover's next-message machine outputs its answers.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11 (next-message function, running time)

import Mathlib
import Definitions.Def_DoublyEffIP_HaltsAt

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP

/-- **Computing an output in exactly `t` steps** — the reading of "a message … determined by the
prescribed next-message function" and of a deterministic machine that "runs in time" a bound, in
Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of
2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11.

Started on `input`, the machine `M` halts after exactly `t` steps, and its tape `out` then holds
exactly the word `y` (head on its first cell, blanks elsewhere).

**Formalization Note.** Output on a designated tape, read as `Turing.Tape.mk₁ (y.map some)`;
distinct words give distinct tapes, so the output is well defined. -/
def ComputesIn (M : PrimitiveMachine) (out : Fin M.tapeCount) (input y : List Bool) (t : ℕ) :
    Prop :=
  ∃ final, HaltsAt M input t final ∧ final.config.tapes out = Turing.Tape.mk₁ (y.map some)

end DoublyEffIP


