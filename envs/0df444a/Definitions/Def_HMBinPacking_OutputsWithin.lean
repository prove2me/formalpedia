-- Prove2me | Definitions.Def_HMBinPacking_OutputsWithin
-- name    : HMBinPacking_OutputsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:26.491705+00:00
-- url     : https://prove2.me/theorems/08690990-7760-4e6e-bd19-06224414dde2
-- title:
--   A Turing machine outputs a word within $t$ steps
-- statement:
--   For a bundled multi-stack Turing machine $M$ with Boolean input and output alphabets, an input word $w$, an output word $w'$ and a number $t$, **$M$ outputs $w'$ on $w$ within $t$ steps** if the run of $M$ started on $w$ halts after at most $t$ steps with $w'$ on its output stack (and every other stack empty).
--
--   This is the time measure of every machine statement of the mission: the paper counts bit operations, and one step of a fixed finite program is a constant number of bit operations.
--
--   **Formalization Note** The machine is Mathlib's `Turing.TM2ComputableAux Bool Bool` and the run is `Turing.TM2OutputsInTime`, the same notion as in Mathlib's `Turing.TM2ComputableInTime`. A Turing machine simulates a bit-operation algorithm with polynomial overhead, and the time bounds used here are classes closed under polynomials, so the choice of model does not change a statement.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, footnote 1, p.1 ('Running times count bit operations')

import Mathlib

namespace HMBinPacking

/-- **A machine outputs a word within a number of steps.**
Koana, Kumabe, arXiv:2609.16923v2, footnote 1, p.1: "Running times count bit operations".

`OutputsWithin M input output t` says that the bundled multi-stack Turing machine `M`
(Mathlib's `Turing.TM2ComputableAux Bool Bool`), started on `input`, halts with `output` on its
output stack (all other stacks empty) after at most `t` steps.

**Formalization Note.** This is Mathlib's `Turing.TM2OutputsInTime`, the run notion of
`Turing.TM2ComputableInTime`, with Boolean input and output alphabets. The paper fixes no machine
model and counts bit operations; a step of a `FinTM2` runs one statement of a fixed finite program,
and a Turing machine simulates a bit-operation algorithm (and conversely) with polynomial overhead.
The time bounds of this mission (`2^(d^(c·d))·L^c`, `2^(c·d³)·(L+ℓ)^c`) form classes closed under
polynomials, so the choice of model does not change any statement. -/
def OutputsWithin (M : Turing.TM2ComputableAux Bool Bool) (input output : List Bool) (t : ℕ) :
    Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) t)

end HMBinPacking


