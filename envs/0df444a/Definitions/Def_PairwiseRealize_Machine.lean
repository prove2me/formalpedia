-- Prove2me | Definitions.Def_PairwiseRealize_Machine
-- name    : PairwiseRealize_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:39.566856+00:00
-- url     : https://prove2.me/theorems/144a18ff-f02f-40fc-8686-324991d71921
-- title:
--   Theorems 2.1, C.1 — input and output encodings on the published randomized Post–Turing machine
-- statement:
--   Theorem 2.1 takes the explicit membership table of a forbidden set $D\subseteq V$ and an integer target $b$; Theorem C.1 takes a $0/1$ matrix $A\in\{0,1\}^{m\times s}$ and a rational vector $p$. This definition fixes how these are written on the tape of the published randomized Post–Turing machine `OAI.MatchingFPRAS.RandomMachine` (definition `ContingencyTables`), a finite transition table performing one tape operation and reading one fair bit per step.
--
--   A membership table lists the $N=2^n$ rows in the order $k\mapsto(i\mapsto\text{bit }i\text{ of }k)$, with symbol $2$ for a member and $1$ for a non-member, followed by the delimiter $3$. The input of Theorem 2.1 is $n$ in binary, the table of $D$, and the coordinates of $b$ as signed binary numerals. Its output is the table of the realization $S$, read from the head rightwards on the halted tape. The input of Theorem C.1 is $m$, $s$, the entries of $A$ in row-major order, a delimiter, and $p$ as reduced numerators and denominators; its output is $q\in\{0,1\}^s$ as $s$ symbols and a delimiter. A machine is **deterministic** when its transition ignores the random bit.
--
--   **Formalization Note** Prefixing $n$ changes no instance, since $n$ is the binary logarithm of the table length.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Theorem 2.1, p.4 (PDF p.5); Theorem C.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_ContingencyTables
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-!
# Input and output encodings for the algorithms of Theorem 2.1 and Theorem C.1

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), Theorem 2.1, printed p.4 (PDF p.5): "Given D by its explicit
membership table and the target b, a Las Vegas algorithm finds such a realization in expected
polynomial bit time in N." "The input consists of the integer target and the explicit membership
table of D." Theorem C.1, printed p.15 (PDF p.16): "a deterministic algorithm returns q ∈ {0,1}^s
… Its bit cost is polynomial in m and the encoding length of p."

The machine model is the published randomized Post–Turing machine
`OAI.MatchingFPRAS.RandomMachine` (definition `ContingencyTables`): one finite transition table, one
tape operation and one fair random bit per step, halted configurations absorbing. "Bit time" is its
number of steps.

**Formalization Note** A membership table lists the `N = 2ⁿ` rows in the order `k ↦ rowOf n k`
(bit `i` of `k` is coordinate `i`), with symbol `2` for a member and `1` for a non-member, followed by
the delimiter `3`. The input of Theorem 2.1 is `n` in binary, the table of `D`, and the coordinates
of `b` as signed binary numerals in the order `featList n`. The output is the membership table of
the realization `S`, read from the head rightwards on the halted tape (as `OutputsTable` of
`ContingencyTables` does). Prefixing `n` changes no instance: `n` is the binary logarithm of the
table length.
-/

open OAI.MatchingFPRAS

/-- The `k`-th row of the cube in the table order: bit `i` of `k` is coordinate `i`. -/
def rowOf (n : ℕ) (k : Fin (2 ^ n)) : Row n := fun i => k.val.testBit i.val

/-- The membership table of `S ⊆ V`: `N` symbols (`2` = member, `1` = not), then the delimiter `3`. -/
def tableCode (n : ℕ) (S : Finset (Row n)) : List Symbol :=
  List.ofFn (fun k : Fin (2 ^ n) => if rowOf n k ∈ S then (2 : Symbol) else 1) ++ [3]

/-- The input of Theorem 2.1: `n`, the explicit membership table of the forbidden set `D`, and the
integer target `b` coordinate by coordinate in the order `featList n`. -/
def inputCode (n : ℕ) (D : Finset (Row n)) (b : Feat n → ℤ) : List Symbol :=
  encodeNat n ++ tableCode n D ++ ((featList n).map fun f => encodeInt (b f)).flatten

/-- The tape alphabet `Fin 8` is inhabited (by the blank `0`). -/
theorem symbol_neZero : NeZero (8 : ℕ) := inferInstance

/-- The run on the bit prefix `bits` has halted, and the tape from the head rightwards holds the
membership table of `S`. -/
def OutputsSet (M : RandomMachine) (input : List Symbol) {t : ℕ} (bits : Fin t → Bool) (n : ℕ)
    (S : Finset (Row n)) : Prop :=
  (run M input bits).state = none ∧
    @Turing.Tape.right₀ Symbol (@Fin.instInhabited 8 symbol_neZero) (run M input bits).tape =
      @Turing.ListBlank.mk Symbol (@Fin.instInhabited 8 symbol_neZero) (tableCode n S)

/-- A machine is deterministic when its transition ignores the random bit. -/
def Deterministic (M : RandomMachine) : Prop :=
  ∀ q a, M.transition q a false = M.transition q a true

/-- The input of Theorem C.1: `m`, `s`, the `0/1` matrix `A` in row-major order (symbol `2` for `1`,
`1` for `0`) followed by the delimiter `3`, then the rational vector `p` coordinate by coordinate
(reduced numerator and denominator). -/
def c1Input (m s : ℕ) (A : Fin m → Fin s → Bool) (p : Fin s → ℚ) : List Symbol :=
  encodeNat m ++ encodeNat s ++
    (List.ofFn fun r => List.ofFn fun j => if A r j then (2 : Symbol) else 1).flatten ++ [3] ++
    (List.ofFn fun j => encodeRat (p j)).flatten

/-- The encoding of the rational vector `p` alone; its length is "the encoding length of p". -/
def ratVecCode {s : ℕ} (p : Fin s → ℚ) : List Symbol := (List.ofFn fun j => encodeRat (p j)).flatten

/-- The output of Theorem C.1: `q ∈ {0,1}^s` as `s` symbols (`2` for `1`, `1` for `0`) and `3`. -/
def bitVecCode {s : ℕ} (q : Fin s → Bool) : List Symbol :=
  List.ofFn (fun j => if q j then (2 : Symbol) else 1) ++ [3]

/-- The run on `bits` has halted with the vector `q` on the tape from the head rightwards. -/
def OutputsBits (M : RandomMachine) (input : List Symbol) {t : ℕ} (bits : Fin t → Bool) {s : ℕ}
    (q : Fin s → Bool) : Prop :=
  (run M input bits).state = none ∧
    @Turing.Tape.right₀ Symbol (@Fin.instInhabited 8 symbol_neZero) (run M input bits).tape =
      @Turing.ListBlank.mk Symbol (@Fin.instInhabited 8 symbol_neZero) (bitVecCode q)

end PairwiseRealize


