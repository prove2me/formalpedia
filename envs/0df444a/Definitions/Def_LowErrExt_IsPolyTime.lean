-- Prove2me | Definitions.Def_LowErrExt_IsPolyTime
-- name    : LowErrExt_IsPolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:48.856199+00:00
-- url     : https://prove2.me/theorems/77ae02ab-a3b0-4227-bc48-dd0359fbdc9c
-- title:
--   Explicit functions: one polynomial-time machine on tuples of bit strings
-- statement:
--   A function $F$ from tuples of bit strings to bit strings is **explicit** if a single deterministic Turing machine computes $F$ on every input in time polynomial in the input length. Tuples are written over the alphabet $\{0,1,2\}$, each string followed by the separator $2$; outputs are bit strings. The module also defines how an output string is read as an element of $\{0,1\}^m$ (its first $m$ bits).
--
--   **Formalization Note** The paper uses "explicit" without a definition; this is the standard meaning in the area (one uniform algorithm, polynomial time). Mathlib's `Turing.TM2ComputableInPolyTime` is the machine model. Because one machine serves all input lengths, a per-length lookup table does not qualify.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), used throughout, e.g. Theorem 1.1, p.5 (not defined in the paper)

import Mathlib

namespace LowErrExt

/-- **Encoding of a tuple of bit strings.** Each word is written over `{0, 1}` (`false ↦ 0`,
`true ↦ 1`) and terminated by the separator symbol `2`. -/
def encWords (ws : List (List Bool)) : List (Fin 3) :=
  ws.flatMap fun w => w.map (fun b => if b then (1 : Fin 3) else 0) ++ [2]

/-- **Explicit (polynomial-time computable) function on tuples of bit strings.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…):
"explicit", used throughout (e.g. Theorem 1.1, p.5) and not defined in the paper.

`IsPolyTime F`: one Turing machine (Mathlib's `Turing.TM2ComputableInPolyTime`) computes `F` on every
input, in time polynomial in the input length, with inputs encoded by `encWords` and outputs as
lists of bits.

**Formalization Note.** This is the standard meaning in the area: computable in time polynomial in
the input length by one uniform deterministic algorithm. A single `F` serves all input lengths, so
"explicit" cannot be met by a per-length lookup table. `encWords` is injective (separator after every
word). -/
def IsPolyTime (F : List (List Bool) → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encWords (fun l : List Bool => l) F)

/-- **Reading an output list as `m` bits.** `listOut m l i` is the `i`-th entry of `l` (`false`
past its end). Statements using it also assert that the list has length exactly `m`. -/
def listOut (m : ℕ) (l : List Bool) : Fin m → Bool :=
  fun i => l.getD i false

end LowErrExt


