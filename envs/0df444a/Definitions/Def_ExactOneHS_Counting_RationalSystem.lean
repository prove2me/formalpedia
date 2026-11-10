-- Prove2me | Definitions.Def_ExactOneHS_Counting_RationalSystem
-- name    : ExactOneHS_Counting_RationalSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:36.084167+00:00
-- url     : https://prove2.me/theorems/0d8da812-75a9-40b2-b2bd-ee3a2df3edc0
-- title:
--   Explicitly represented rational linear systems $Ax = b$, their solutions, and their binary codes
-- statement:
--   An **explicitly represented rational system** $Ax = b$ consists of $m$ equations in $r$ variables: a matrix $A \in \mathbb{Q}^{m \times r}$ and a right-hand side $b \in \mathbb{Q}^m$. A **rational solution** is $x \in \mathbb{Q}^r$ with $Ax = b$; the system is **consistent** if it has one. For a set $s$ of equation indices, $x$ **satisfies the rows** $s$ if $\sum_{k} A_{ik} x_k = b_i$ for every $i \in s$.
--
--   The system is coded as a bit string by writing $r$ in unary and then the $m$ equations in order, equation $i$ as the list $(A_{i1}, \dots, A_{ir}, b_i)$ of rationals, each rational in binary (`encRat`: sign bit, numerator and denominator in self-delimiting binary). A set of equation indices is coded as the increasing list of the indices, each in unary.
--
--   **Formalization Note.** Equations are indexed by `Fin m` and variables by `Fin r`, both 0-based.
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 10, Lemma 3.1 ("explicitly represented rational system Ax = b in r variables", "deterministic polynomial bit time")

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- An explicitly represented rational linear system `A x = b`: `m` equations in `r`
variables. -/
structure RationalSystem where
  /-- the number of equations -/
  m : ℕ
  /-- the number of variables -/
  r : ℕ
  /-- the coefficient matrix -/
  A : Matrix (Fin m) (Fin r) ℚ
  /-- the right-hand side -/
  b : Fin m → ℚ

namespace RationalSystem

variable (S : RationalSystem)

/-- `x ∈ ℚ^r` is a rational solution of `A x = b`. -/
def IsSolution (x : Fin S.r → ℚ) : Prop := Matrix.mulVec S.A x = S.b

/-- `x ∈ ℚ^r` satisfies the equations with indices in `s`. -/
def SatisfiesRows (s : Finset (Fin S.m)) (x : Fin S.r → ℚ) : Prop :=
  ∀ i ∈ s, ∑ j, S.A i j * x j = S.b i

/-- The system has a rational solution. -/
def IsConsistent : Prop := ∃ x : Fin S.r → ℚ, S.IsSolution x

end RationalSystem

/-- Code of a rational system: `r` in unary, then the `m` equations in order, each as the list
`(a_{i1}, …, a_{ir}, b_i)` of rationals in binary (`encRat`: sign, numerator, denominator). -/
def encodeSystem (S : RationalSystem) : List Bool :=
  QAlgorithms.Complexity.encNat S.r ++
    Encoding.encodeList
      (fun i : Fin S.m =>
        Encoding.encodeList QAlgorithms.LocalHamiltonian.encRat
          (List.ofFn (fun j => S.A i j) ++ [S.b i]))
      (List.finRange S.m)

/-- Code of a set of row indices: the indices in increasing order, each in unary. -/
def encodeRowSet {m : ℕ} (s : Finset (Fin m)) : List Bool :=
  Encoding.encodeList Encoding.encodeNat ((s.image Fin.val).sort (· ≤ ·))

end ExactOneHS.Counting


