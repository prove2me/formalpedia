-- Prove2me | Definitions.Def_CFLOutliers_OutputsWithin
-- name    : CFLOutliers_OutputsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:09.522954+00:00
-- url     : https://prove2.me/theorems/0ef9cdad-1989-4951-8b8c-157d20428eb1
-- title:
--   A Turing machine outputs a word within $t$ steps
-- statement:
--   For a bundled multi-stack Turing machine $\mathcal M$ over the four-symbol alphabet and words $x$, $y$, $\mathcal M$ **outputs $y$ on $x$ within $t$ steps** if, started with $x$ on its input stack, it halts after at most $t$ steps with $y$ on its output stack.
--
--   This is the meaning of "polynomial time" in Theorem 1.1 and Lemma 2.2.
--
--   **Formalization Note** It is Mathlib's `Turing.TM2OutputsInTime`, the run notion of `Turing.TM2ComputableInTime`. The paper names no machine model; polynomial time is invariant under the polynomial simulations between models.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Theorem 1.1, p.2; Lemma 2.2, p.5

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace CFLOutliers

open OnlineCRS.Combine (Sym)

/-- **A machine outputs a word within `t` steps.**
Dabas, arXiv:2611.04094, Theorem 1.1, p.2 ("The running time is polynomial in the binary input
length and 1/ε") and Lemma 2.2, p.5 ("In polynomial time, one can construct").

`OutputsWithin M input output t`: the bundled multi-stack Turing machine `M` (Mathlib's
`Turing.TM2ComputableAux Sym Sym`), started on `input`, halts with `output` on its output stack
after at most `t` steps.

**Formalization Note.** This is Mathlib's `Turing.TM2OutputsInTime`, the run notion of
`Turing.TM2ComputableInTime`, over the alphabet `Sym = Fin 4`. The paper names no machine model;
polynomial time is a class closed under the polynomial simulations between models. -/
def OutputsWithin (M : Turing.TM2ComputableAux Sym Sym) (input output : List Sym) (t : ℕ) :
    Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) t)

end CFLOutliers


