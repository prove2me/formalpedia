-- Prove2me | Definitions.Def_CNFEncComplexity_encWords
-- name    : CNFEncComplexity_encWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:10.291872+00:00
-- url     : https://prove2.me/theorems/7ebda0e9-20bc-4f32-9819-41352605a4dc
-- title:
--   Word encoding of construction inputs
-- statement:
--   Inputs of the deterministic constructions are written as a sequence of bit strings (words) over the alphabet $\{0,1,2\}$: each word is written in $0$/$1$ and terminated by the separator $2$. Numbers are written in unary ($n$ ones) or in binary, and a program is written as three words per instruction (the opcode in unary and two operands in binary).
--
--   The polynomial-time clauses of Theorems 2 and 10 and Lemmas 11, 13 and 14 measure time in the length of these encodings.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`. No word contains the separator, so the encoding is injective; this and the injectivity of every per-item encoder are proved in the mission's verification files.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), construction clauses of Theorem 2 (p.2), Theorem 10 (p.10), Lemmas 11, 13, 14 (pp.11–14)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr

namespace CNFEncComplexity

/-- A bit as a tape symbol: `false ↦ 0`, `true ↦ 1`. -/
def bitSym (x : Bool) : Fin 3 := if x then 1 else 0

/-- A number in unary: `n` ones. -/
def unaryWord (n : ℕ) : List Bool := List.replicate n true

/-- A number in binary (Mathlib's `Computability.encodeNat`, least significant bit first). -/
def binWord (n : ℕ) : List Bool := Computability.encodeNat n

/-- The opcode of an instruction, `0, …, 11`. -/
def instrTag : Instr → ℕ
  | .loadc _ => 0 | .load _ => 1 | .loadi _ => 2 | .store _ => 3 | .storei _ => 4
  | .add _ => 5 | .sub _ => 6 | .read => 7 | .jump _ => 8 | .jzero _ => 9
  | .njump _ _ => 10 | .halt => 11

/-- The operands of an instruction, padded with `0` to a pair. -/
def instrArgs : Instr → ℕ × ℕ
  | .loadc c => (c, 0) | .load j => (j, 0) | .loadi j => (j, 0) | .store j => (j, 0)
  | .storei j => (j, 0) | .add j => (j, 0) | .sub j => (j, 0) | .read => (0, 0)
  | .jump l => (l, 0) | .jzero l => (l, 0) | .njump l₁ l₂ => (l₁, l₂) | .halt => (0, 0)

/-- An instruction as three words: its opcode in unary and its two (padded) operands in binary. -/
def instrWords (i : Instr) : List (List Bool) :=
  [unaryWord (instrTag i), binWord (instrArgs i).1, binWord (instrArgs i).2]

/-- A program as words: three words per instruction, in order. -/
def progWords (prog : List Instr) : List (List Bool) :=
  prog.flatMap instrWords

/-- **Word encoding of construction inputs.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…); used for the deterministic polynomial-time
construction clauses of Theorems 2 and 10 and Lemmas 11, 13 and 14.

`encWords ws` writes each bit string of `ws` over the alphabet `{0, 1, 2}` and terminates it with
the separator `2`.

**Formalization Note.** Polynomial time in these clauses is Mathlib's
`Turing.TM2ComputableInPolyTime`, i.e. time polynomial in the length of this encoding. No word
contains `2`, so `encWords` is injective; the per-item encoders built on it fix how many words each
component occupies (`Solutions/verification/CNFEncComplexity_sanity.lean`). -/
def encWords (ws : List (List Bool)) : List (Fin 3) :=
  ws.flatMap fun w => w.map bitSym ++ [2]

end CNFEncComplexity


