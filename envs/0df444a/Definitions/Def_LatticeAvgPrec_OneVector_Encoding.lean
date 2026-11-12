-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_Encoding
-- name    : LatticeAvgPrec_OneVector_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:05.957056+00:00
-- url     : https://prove2.me/theorems/cfb88a7a-4cbe-4089-903f-826f97baae4e
-- title:
--   Bitwise codes of integers, vectors, matrices and dyadic numbers on the RAM
-- statement:
--   Inputs and outputs of the algorithms in this mission are binary (p.4: "Costs include binary input and output"). A natural number $x$ is coded one bit per memory cell: its binary digits, least significant first, each preceded by a continuation cell $1$, followed by a terminating cell $0$ (so $0$ is the single cell $0$). An integer $z$ is coded by a sign cell ($1$ if $z<0$, else $0$) followed by the code of $|z|$. A vector $v\in\mathbb Z^n$ is coded by the code of $n$ followed by its entries; a matrix $M\in\mathbb Z^{a\times b}$ by the codes of $a$ and $b$ followed by its entries row by row. A list of naturals is coded by its length and its entries. A vector of dyadic numbers $\mathrm{num}_i/2^{\mathrm{ex}_i}$ is coded by its length and the pairs (numerator, exponent).
--
--   A memory $\mathrm{mem}:\mathbb N\to\mathbb N$ *holds* a list $\ell$ if $\mathrm{mem}(i)=\ell_i$ for every $i<|\ell|$. All codes above are prefix-free, so at most one value of a given type is held at cell $0$: this is the strict output reading used by every theorem.
--
--   The file also fixes two conversions: the real matrix $\mathrm{rmat}(M)$ of an integer matrix, and the dyadic matrix $N/2^e$ with integer numerators $N$ and common denominator $2^e$ (App. A, p.27: "integer numerators and a common power-of-two denominator").
--
--   **Formalization Note** One bit per cell matters on the logarithmic-cost RAM: storing a whole $h$-bit integer in one cell and splitting it costs $\Theta(h^2)$, which for one long row would exceed the paper's bounds for a reason unrelated to the mathematics.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), §1.1.1 p.4 (binary input and output); App. A p.27 (dyadic numbers)

import Mathlib
open Matrix

namespace LatticeAvgPrec.OneVector

/-- Bitwise self-delimiting code of a natural number, one bit per memory cell: the binary digits of
`x`, least significant first, each preceded by a continuation cell `1`, and a final cell `0`.
Zero is the single cell `[0]`. Every cell holds `0` or `1`, so reading an `h`-bit number costs `Θ(h)`
on the logarithmic-cost RAM. -/
def natCode (x : ℕ) : List ℕ :=
  (Nat.bits x).flatMap (fun b => [1, b.toNat]) ++ [0]

/-- Bitwise code of an integer: a sign cell (`1` for negative, `0` otherwise) followed by the code
of its absolute value. -/
def intCode (z : ℤ) : List ℕ :=
  (if z < 0 then 1 else 0) :: natCode z.natAbs

/-- Code of an integer vector of length `n`: the code of `n`, then the entries in order. -/
def vecCode {n : ℕ} (v : Fin n → ℤ) : List ℕ :=
  natCode n ++ (List.finRange n).flatMap (fun i => intCode (v i))

/-- Code of an integer `a × b` matrix: the codes of `a` and `b`, then the entries row by row. -/
def matCode {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) : List ℕ :=
  natCode a ++ natCode b ++
    (List.finRange a).flatMap (fun i => (List.finRange b).flatMap (fun j => intCode (M i j)))

/-- Code of a list of natural numbers: its length, then the code of every entry. -/
def listCode (l : List ℕ) : List ℕ :=
  natCode l.length ++ l.flatMap natCode

/-- Code of a vector of dyadic numbers `num i / 2 ^ ex i`: for each `i`, the integer numerator and
the natural exponent, preceded by the length. -/
def dyVecCode {n : ℕ} (num : Fin n → ℤ) (ex : Fin n → ℕ) : List ℕ :=
  natCode n ++ (List.finRange n).flatMap (fun i => intCode (num i) ++ natCode (ex i))

/-- Memory `mem` holds the list `l` from cell `0` on. This is the strict output reading: the codes
above are prefix-free, so at most one value of a given code type is held at cell `0`. -/
def memHolds (mem : ℕ → ℕ) (l : List ℕ) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), mem i = l[i]

/-- The real matrix of an integer matrix. -/
def rmat {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) : Matrix (Fin a) (Fin b) ℝ :=
  M.map (fun z : ℤ => (z : ℝ))

/-- The dyadic real matrix `N / 2^e` with integer numerators `N` and common denominator `2^e`. -/
noncomputable def dyMat {a b : ℕ} (N : Matrix (Fin a) (Fin b) ℤ) (e : ℕ) : Matrix (Fin a) (Fin b) ℝ :=
  fun i j => (N i j : ℝ) / (2 : ℝ) ^ e

/-- The dyadic number `num / 2^e`. -/
noncomputable def dyVal (num : ℤ) (e : ℕ) : ℝ := (num : ℝ) / (2 : ℝ) ^ e

end LatticeAvgPrec.OneVector


