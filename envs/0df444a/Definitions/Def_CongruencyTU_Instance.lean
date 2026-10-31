-- Prove2me | Definitions.Def_CongruencyTU_Instance
-- name    : CongruencyTU_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:59.593957+00:00
-- url     : https://prove2.me/theorems/c86a0d4b-36c3-4033-94e2-853ab4d4cd4a
-- title:
--   R-CCTUF, CCTUF and CCTU problems and their encodings
-- statement:
--   For a totally unimodular $T\in\{-1,0,1\}^{k\times n}$, $b\in\mathbb Z^k$, $m\in\mathbb Z_{>0}$ and $\gamma\in\mathbb Z^n$:
--
--   1. **R-CCTUF** with target residues $R\subseteq\{0,\dots,m-1\}$: find $x\in\mathbb Z^n$ with $Tx\le b$ and $\gamma^\top x\equiv r\pmod m$ for some $r\in R$, or show that none exists.
--   2. **CCTUF** with $r\in\mathbb Z$: find $x\in\mathbb Z^n$ with $Tx\le b$ and $\gamma^\top x\equiv r\pmod m$, or show infeasibility.
--   3. **CCTU** with $c\in\mathbb Z^n$: $\min\{c^\top x : Tx\le b,\ \gamma^\top x\equiv r \pmod m,\ x\in\mathbb Z^n\}$; the task is to show infeasibility, unboundedness (arbitrarily small objective values over feasible points, footnote 5), or find a minimizer.
--
--   The **relaxation** of an R-CCTUF problem drops the congruency constraint and keeps $x\in\mathbb Z^n$.
--
--   Each problem is encoded as a list of integers: the dimensions and the modulus, the entries of $T$ row by row, then $b$, $\gamma$ and $r$ (or $|R|$ followed by the elements of $R$ in increasing order), and for CCTU the objective $c$. Answers are $[0]$ (infeasible), $1::x$ (a solution) for the feasibility problems, and $[0]$, $[1]$ (unbounded) or $2::x$ (a minimizer) for CCTU.
--
--   **Formalization Note** Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular`; it forces entries in $\{-1,0,1\}$. `‖c‖_∞` (`cNorm`) is added to the input size when the objective is unary encoded.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, CCTU, p.1 (PDF p.2); CCTUF and R-CCTUF, p.2 (PDF p.3); footnote 5, p.2

import Mathlib

open Classical Matrix

namespace CongruencyTU

/-! # R-CCTUF, CCTUF and CCTU problems and their encodings

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint): CCTU, p.1 (PDF p.2); CCTUF and R-CCTUF,
p.2 (PDF p.3); unboundedness, footnote 5, p.2.

**Formalization Note.** Matrices are `Matrix (Fin k) (Fin n) ℤ`, vectors `Fin n → ℤ`, the order on
vectors is componentwise. Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` (every
square submatrix has determinant in `{−1, 0, 1}`); it forces every entry into `{−1, 0, 1}`, so the
paper's `T ∈ {−1, 0, 1}^{k×n}` adds nothing. The set of target residues is a `Finset ℕ` whose
elements are `< m`. A congruence `γ⊤x ≡ r (mod m)` is `Int.ModEq m`. The encodings list the data
row-major after the dimensions; `R` is listed in increasing order. -/

/-- Row-major list of the entries of a matrix. -/
def encMat {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) : List ℤ :=
  (List.ofFn fun i => List.ofFn fun j => T i j).flatten

/-- The list of entries of a vector. -/
def encVec {n : ℕ} (v : Fin n → ℤ) : List ℤ := List.ofFn v

/-- A finite set of residues as the list `|R|, r₁ < r₂ < ⋯`. -/
def encRes (R : Finset ℕ) : List ℤ :=
  (R.card : ℤ) :: (R.sort (· ≤ ·)).map (fun r : ℕ => (r : ℤ))

/-- **R-CCTUF instance** (p.2): `Tx ≤ b, γ⊤x ∈ R (mod m), x ∈ ℤⁿ`. -/
structure RInst where
  k : ℕ
  n : ℕ
  T : Matrix (Fin k) (Fin n) ℤ
  b : Fin k → ℤ
  m : ℕ
  γ : Fin n → ℤ
  R : Finset ℕ

namespace RInst

/-- The data of an R-CCTUF problem as the paper requires them: `T` totally unimodular, `m ∈ ℤ_{>0}`,
`R ⊆ {0, …, m − 1}`. -/
def Valid (P : RInst) : Prop :=
  P.T.IsTotallyUnimodular ∧ 0 < P.m ∧ ∀ r ∈ P.R, r < P.m

/-- `x` solves the relaxation `Tx ≤ b, x ∈ ℤⁿ` (the congruency constraint dropped, p.3). -/
def Relaxed (P : RInst) (x : Fin P.n → ℤ) : Prop := P.T *ᵥ x ≤ P.b

/-- `x` is a feasible solution: `Tx ≤ b` and `γ⊤x ≡ r (mod m)` for some `r ∈ R`. -/
def IsSol (P : RInst) (x : Fin P.n → ℤ) : Prop :=
  P.Relaxed x ∧ ∃ r ∈ P.R, P.γ ⬝ᵥ x ≡ (r : ℤ) [ZMOD (P.m : ℤ)]

/-- The R-CCTUF problem is feasible. -/
def Feasible (P : RInst) : Prop := ∃ x, P.IsSol x

/-- Encoding `[k, n, m] ++ T ++ b ++ γ ++ [|R|] ++ R`. -/
def enc (P : RInst) : List ℤ :=
  [(P.k : ℤ), (P.n : ℤ), (P.m : ℤ)] ++ encMat P.T ++ encVec P.b ++ encVec P.γ ++ encRes P.R

/-- An output reporting a feasible solution: `1 :: x` with `x` a solution. -/
def SolOut (P : RInst) (out : List ℤ) : Prop := ∃ x, P.IsSol x ∧ out = 1 :: encVec x

end RInst

/-- **CCTUF instance** (p.2): `Tx ≤ b, γ⊤x ≡ r (mod m), x ∈ ℤⁿ`, with `r ∈ ℤ`. -/
structure CInst where
  k : ℕ
  n : ℕ
  T : Matrix (Fin k) (Fin n) ℤ
  b : Fin k → ℤ
  m : ℕ
  γ : Fin n → ℤ
  r : ℤ

namespace CInst

/-- `T` totally unimodular and `m ∈ ℤ_{>0}`. -/
def Valid (P : CInst) : Prop := P.T.IsTotallyUnimodular ∧ 0 < P.m

/-- `x` is a feasible solution: `Tx ≤ b` and `γ⊤x ≡ r (mod m)`. -/
def IsSol (P : CInst) (x : Fin P.n → ℤ) : Prop :=
  P.T *ᵥ x ≤ P.b ∧ P.γ ⬝ᵥ x ≡ P.r [ZMOD (P.m : ℤ)]

/-- The CCTUF problem is feasible. -/
def Feasible (P : CInst) : Prop := ∃ x, P.IsSol x

/-- Encoding `[k, n, m] ++ T ++ b ++ γ ++ [r]`. -/
def enc (P : CInst) : List ℤ :=
  [(P.k : ℤ), (P.n : ℤ), (P.m : ℤ)] ++ encMat P.T ++ encVec P.b ++ encVec P.γ ++ [P.r]

/-- An output reporting a feasible solution: `1 :: x` with `x` a solution. -/
def SolOut (P : CInst) (out : List ℤ) : Prop := ∃ x, P.IsSol x ∧ out = 1 :: encVec x

end CInst

/-- **CCTU instance** (p.1): `min {c⊤x : Tx ≤ b, γ⊤x ≡ r (mod m), x ∈ ℤⁿ}`. -/
structure OInst extends CInst where
  c : Fin n → ℤ

namespace OInst

/-- Unbounded (footnote 5): arbitrarily good (small) objective values are attained by feasible
solutions. -/
def Unbounded (P : OInst) : Prop := ∀ M : ℤ, ∃ x, P.IsSol x ∧ P.c ⬝ᵥ x < M

/-- `x` is a minimizer: feasible, and no feasible solution has smaller objective value. -/
def IsMin (P : OInst) (x : Fin P.n → ℤ) : Prop :=
  P.IsSol x ∧ ∀ y, P.IsSol y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y

/-- Encoding: the CCTUF encoding followed by `c`. -/
def enc (P : OInst) : List ℤ := P.toCInst.enc ++ encVec P.c

/-- `‖c‖_∞`, added to the input size when the objective is unary encoded. -/
def cNorm (P : OInst) : ℕ := Finset.univ.sup fun i => (P.c i).natAbs

/-- A correct answer of a feasible CCTU problem: `[1]` if it is unbounded, or `2 :: x` with `x` a
minimizer. -/
def SolvedOut (P : OInst) (out : List ℤ) : Prop :=
  (P.Unbounded ∧ out = [1]) ∨ ∃ x, P.IsMin x ∧ out = 2 :: encVec x

/-- A correct answer of a CCTU problem: `[0]` if it is infeasible, `[1]` if it is unbounded, or
`2 :: x` with `x` a minimizer. -/
def CorrectOut (P : OInst) (out : List ℤ) : Prop :=
  (¬ P.Feasible ∧ out = [0]) ∨ P.SolvedOut out

end OInst

end CongruencyTU


