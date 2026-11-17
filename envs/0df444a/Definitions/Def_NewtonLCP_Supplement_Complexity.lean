-- Prove2me | Definitions.Def_NewtonLCP_Supplement_Complexity
-- name    : NewtonLCP_Supplement_Complexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:15:59.520384+00:00
-- url     : https://prove2.me/theorems/f75d766f-28c5-4911-a72b-3614d11c6809
-- title:
--   Binary codes of rational matrices, matrix-class languages, coNP-hardness and coNP-completeness
-- statement:
--   The decision problem "given $M\in\mathbb Q^{n\times n}$, is $M\in\tilde P$?" for a matrix class $\tilde P=(\tilde P_n)_{n\ge0}$ is the language of binary codes of the matrices of $\tilde P$.
--
--   1. A natural number is written in binary, least significant digit first, each digit $b$ as the pair $1b$, followed by the terminator $0$ (a self-delimiting code).
--   2. An integer is a sign bit followed by the code of its absolute value; a rational is the code of its numerator followed by that of its denominator, in lowest terms.
--   3. A matrix $M\in\mathbb Q^{n\times n}$ is the code of $n$ followed by the codes of its entries in row-major order.
--
--   The **language of $\tilde P$** is the set of codes of the matrices in $\tilde P$; strings that encode no matrix are not in it. The code is injective and its length is polynomial in $n^2+\mathrm{length}(M)$.
--
--   A language $L$ is **coNP-hard** if every language in coNP over every finite nonempty alphabet reduces to $L$ by a polynomial-time many-one reduction; it is **coNP-complete** if moreover $L\in$ coNP.
--
--   These notions state Theorem 1.3.
--
--   **Formalization Note** coNP, polynomial-time computability and many-one reductions are those of the published `CookPvsNP_defs` (Cook's one-tape Turing machines, running time $|x|^k+k$).
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorems 1.3 and 1.4, p.4; §2.1 length(A), p.6; §7.1, pp.24–26

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace NewtonLCP.Supplement

/-!
# Binary encodings of rational matrices, matrix-class languages, coNP-hardness

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8),
Theorems 1.3 and 1.4, p.4; §2.1 "length(A)", p.6; §7.1, pp.24–26.

The paper's decision problem "given `M ∈ ℚⁿˣⁿ`, is `M ∈ P̃`?" is the language of binary codes of
the matrices of the class. Complexity classes, polynomial-time computability and polynomial-time
many-one reductions are those of the published `CookPvsNP_defs` (Cook's one-tape Turing machines,
time `|x|^k + k`).

**Formalization Note.**
* `encNat n` writes the binary digits of `n` (least significant first, `Nat.bits`), each digit
  `b` as the pair `true, b`, followed by the terminator `false`. It is injective and
  self-delimiting, of length `2·⌈log₂(n+1)⌉ + 1`.
* `encInt z` is a sign bit followed by `encNat |z|`; `encQ q` is `encInt` of the numerator and
  `encNat` of the denominator of the reduced form (Mathlib's `ℚ` is always reduced). Its length is
  within a constant factor of the published `bitSize q`.
* `encMat M` for `M : Matrix (Fin n) (Fin n) ℚ` is `encNat n` followed by the codes of the
  entries in row-major order. It is injective over all `n` together, and its length is
  polynomially related to `n² + length(M)` (the paper's `length(M)`, §2.1).
* `matLang P̃` is the set of codes of matrices of `P̃`; strings that encode no matrix are not in
  it.
* A language `L` is **coNP-hard** if every language in `coNP` over every finite nonempty alphabet
  poly-time many-one reduces to it (the coNP analogue of the second clause of
  `CookPvsNP.NPComplete`); it is **coNP-complete** if it is in `coNP` and coNP-hard.
-/

/-- Self-delimiting binary code of a natural number. -/
def encNat (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Code of an integer: sign bit (`true` for negative), then `encNat |z|`. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- Code of a rational number: numerator then denominator of the reduced form. -/
def encQ (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- Code of a rational `n × n` matrix: `n`, then the entries in row-major order. -/
def encMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  encNat n ++ (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j => encQ (M i j)))

/-- The language of a matrix class `P̃ = (P̃ₙ)ₙ`: the codes of the rational matrices in `P̃`. -/
def matLang (Pt : (n : ℕ) → Set (Matrix (Fin n) (Fin n) ℚ)) : CookPvsNP.Lang Bool :=
  {w | ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ), M ∈ Pt n ∧ w = encMat M}

/-- `L` is coNP-hard: every coNP language over every finite nonempty alphabet poly-time
many-one reduces to `L`. -/
def CoNPHard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.coNP Sym' → CookPvsNP.PolyReducible L' L

/-- `L` is coNP-complete: `L ∈ coNP` and `L` is coNP-hard. -/
def CoNPComplete {Sym : Type} [Fintype Sym] (L : CookPvsNP.Lang Sym) : Prop :=
  L ∈ CookPvsNP.coNP Sym ∧ CoNPHard L

end NewtonLCP.Supplement


