-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_Encoding
-- name    : InfoLossLAR_WorstCase_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:02:20.102456+00:00
-- url     : https://prove2.me/theorems/e797c84f-be4c-45a8-8a7d-65d3c56e645e
-- title:
--   Binary encodings of the classical inputs $(1^\lambda,\mathrm{pp},\text{table})$
-- statement:
--   Distinguishers and lattice algorithms receive classical inputs as binary strings. This item fixes one self-delimiting binary encoding, decodable in polynomial time:
--
--   - a natural number $n$ is written by its binary digits (least significant first), each preceded by a marker bit $1$, followed by a stop bit $0$;
--   - an integer is a sign bit followed by the code of $|z|$; a rational number is its reduced numerator followed by its denominator; a residue $x\in\mathbb F_q=\mathbb Z/q\mathbb Z$ is the code of its canonical representative in $\{0,\dots,q-1\}$;
--   - a binary string, a list, a vector $v\in\alpha^n$ and a matrix (row by row) are length-prefixed concatenations of the codes of their entries; a pair of strings is the concatenation of the two length-prefixed strings;
--   - the input $(1^\lambda,\mathrm{pp},\text{table})$ of a distinguisher (§3.1) is the concatenation of the length-prefixed strings $1^\lambda$, $\mathrm{pp}$ and the table code.
--
--   $$\mathrm{encInput}(\lambda,\mathrm{pp},\mathrm{tbl})=\mathrm{encS}(1^\lambda)\,\Vert\,\mathrm{encS}(\mathrm{pp})\,\Vert\,\mathrm{encS}(\mathrm{tbl}).$$
--
--   **Formalization Note.** The paper fixes no encoding ("the binary encoding length of pp is polynomially bounded"); any two polynomial-time inter-convertible encodings give the same polynomial-time notions. Binary strings are `QAlgorithms.Complexity.Str = List Bool`.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 20, §3.1 and Definition 3.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-!
# Binary encodings of classical inputs

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), §3.1, p. 20: distinguishers receive
`(1^λ, pp, table)` as classical input, and "the binary encoding length of pp" is polynomially
bounded. The paper fixes no particular encoding; this file fixes one self-delimiting binary
encoding of natural numbers, integers, rationals, residues, vectors, matrices and tables. It is
computable and decodable in polynomial time, so the choice changes no polynomial-time notion.

* `encB n`: the binary digits of `n` (least significant first), each preceded by a `true`
  marker bit, followed by a single `false` stop bit (length `2·(bit length) + 1`).
* `encI z`: a sign bit (`true` for `z < 0`) followed by `encB |z|`.
* `encQ x`: `encI` of the reduced numerator followed by `encB` of the denominator.
* `encZM x`: the residue `x ∈ ℤ/qℤ` by its canonical representative in `{0, …, q − 1}`.
* `encS s`: a binary string, prefixed by `encB` of its length.
* Lists, vectors (`Fin n → α`) and matrices (rows in order) are length-prefixed concatenations of
  the codes of their entries.
-/

/-- Self-delimiting binary code of a natural number: each bit of `Nat.bits n` (least significant
first) is preceded by the marker `true`; a final `false` ends the code. -/
def encB (n : ℕ) : Str := (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Binary code of an integer: sign bit, then the binary code of its absolute value. -/
def encI (z : ℤ) : Str := decide (z < 0) :: encB z.natAbs

/-- Binary code of a rational number: reduced numerator, then denominator. -/
def encQ (x : ℚ) : Str := encI x.num ++ encB x.den

/-- Binary code of a residue modulo `q` by its canonical representative in `{0, …, q − 1}`. -/
def encZM {q : ℕ} (x : ZMod q) : Str := encB x.val

/-- A binary string, prefixed by the binary code of its length (so that it is self-delimiting). -/
def encS (s : Str) : Str := encB s.length ++ s

/-- A list, as its length followed by the concatenated codes of its entries. -/
def encL {α : Type*} (f : α → Str) (l : List α) : Str := encB l.length ++ l.flatMap f

/-- A vector `v : Fin n → α`, as the list of its entries. -/
def encVec {α : Type*} {n : ℕ} (f : α → Str) (v : Fin n → α) : Str := encL f (List.ofFn v)

/-- A matrix, as the list of its rows (each row a vector). -/
def encMat {α : Type*} {m n : ℕ} (f : α → Str) (M : Matrix (Fin m) (Fin n) α) : Str :=
  encL (encVec f) (List.ofFn fun i => M i)

/-- A pair of binary strings. -/
def encPair (a b : Str) : Str := encS a ++ encS b

/-- The classical input `(1^λ, pp, table)` of a distinguisher (§3.1, p. 20; Definition 3.7):
the unary string `1^λ`, the binary code `pp` of the public parameters and the binary code `tbl`
of the sample table, each length-prefixed. -/
def encInput (lam : ℕ) (pp tbl : Str) : Str := encS (unary lam) ++ encS pp ++ encS tbl

end InfoLossLAR.WorstCase


