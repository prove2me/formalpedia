-- Prove2me | Definitions.Def_CongruencyTU_Sums
-- name    : CongruencyTU_Sums
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:42.726996+00:00
-- url     : https://prove2.me/theorems/e0feb941-8e43-4ce9-b810-5497b27f680b
-- title:
--   1-, 2-, 3-sums, pivoting, and sum decompositions
-- statement:
--   Let $A\in\mathbb Z^{k_A\times n_A}$, $B\in\mathbb Z^{k_B\times n_B}$, $e\in\mathbb Z^{k_A}$, $f\in\mathbb Z^{n_B}$, $g\in\mathbb Z^{k_B}$, $h\in\mathbb Z^{n_A}$.
--
--   1. The **1-sum** is $A\oplus_1 B=\begin{pmatrix}A&0\\0&B\end{pmatrix}$.
--   2. The **2-sum** of $(A\ \ e)$ and $\begin{pmatrix}f^\top\\B\end{pmatrix}$ is $\begin{pmatrix}A&ef^\top\\0&B\end{pmatrix}$.
--   3. The **3-sum** of $\begin{pmatrix}A&e&e\\h^\top&0&1\end{pmatrix}$ and $\begin{pmatrix}0&1&f^\top\\g&g&B\end{pmatrix}$ is $\begin{pmatrix}A&ef^\top\\gh^\top&B\end{pmatrix}$.
--   4. **Pivoting** on $\varepsilon\in\{-1,1\}$ in $T=\begin{pmatrix}\varepsilon&p^\top\\q&C\end{pmatrix}$ gives $\begin{pmatrix}-\varepsilon&\varepsilon p^\top\\\varepsilon q&C-\varepsilon qp^\top\end{pmatrix}$; $\mathrm{pivot}_{ij}(T)$ performs this on the entry $T_{ij}$.
--
--   A **sum decomposition** of a $k\times n$ matrix $T$ records the kind of sum, bijections placing the rows and columns of $T$ into the two blocks (row and column permutations), and the blocks; it is valid when $T$ equals the sum entrywise, the two summands are totally unimodular, and $n_A,n_B\ge 2$. Its encoding lists all these data.
--
--   **Formalization Note** Block matrices use `Matrix.fromBlocks` with index types `Fin kA ⊕ Fin kB`; pivoting is written entrywise.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, Definitions 12 and 13, p.8 (PDF p.9); Theorem 14 (iii), p.8

import Mathlib
import Definitions.Def_CongruencyTU_Instance

open Matrix

namespace CongruencyTU

/-! # 1-, 2-, 3-sums and pivoting

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint), Definition 12 (1-, 2-, and 3-sums) and
Definition 13 (Pivoting), p.8 (PDF p.9). With `A ∈ ℤ^{kA×nA}`, `B ∈ ℤ^{kB×nB}`, `e ∈ ℤ^{kA}`,
`f ∈ ℤ^{nB}`, `g ∈ ℤ^{kB}`, `h ∈ ℤ^{nA}`:
* `A ⊕₁ B := (A 0; 0 B)`;
* `(A e) ⊕₂ (f⊤; B) := (A ef⊤; 0 B)`;
* `(A e e; h⊤ 0 1) ⊕₃ (0 1 f⊤; g g B) := (A ef⊤; gh⊤ B)`;
* `pivot₁₁((ε p⊤; q C)) := (−ε εp⊤; εq C − εqp⊤)` for `ε ∈ {−1, 1}`, and `pivot_ij` the same operation
  on the entry `T_ij`.

**Formalization Note.** Block matrices are `Matrix.fromBlocks` with rows `Fin kA ⊕ Fin kB` and
columns `Fin nA ⊕ Fin nB`; the summands' extra row and columns are indexed by `Fin 1` and `Fin 2`.
`pivot T i j` is written entrywise; it is the paper's "permute `T_ij` to position `(1,1)`, pivot,
permute back". A `Decomp k n` packages a decomposition of a `k × n` matrix as a 1-, 2- or 3-sum
after row and column permutations (Theorem 14 (iii)/(iv), p.8): the bijections `rows`, `cols`
place the original rows and columns in the blocks. -/

variable {kA nA kB nB : ℕ}

/-- The 1-sum `A ⊕₁ B = (A 0; 0 B)` (Definition 12 (i)). -/
def sum1 (A : Matrix (Fin kA) (Fin nA) ℤ) (B : Matrix (Fin kB) (Fin nB) ℤ) :
    Matrix (Fin kA ⊕ Fin kB) (Fin nA ⊕ Fin nB) ℤ :=
  fromBlocks A 0 0 B

/-- The left summand `(A e)` of a 2-sum. -/
def sum2Left (A : Matrix (Fin kA) (Fin nA) ℤ) (e : Fin kA → ℤ) :
    Matrix (Fin kA) (Fin nA ⊕ Fin 1) ℤ :=
  fromCols A (replicateCol (Fin 1) e)

/-- The right summand `(f⊤; B)` of a 2-sum. -/
def sum2Right (f : Fin nB → ℤ) (B : Matrix (Fin kB) (Fin nB) ℤ) :
    Matrix (Fin 1 ⊕ Fin kB) (Fin nB) ℤ :=
  fromRows (replicateRow (Fin 1) f) B

/-- The 2-sum `(A e) ⊕₂ (f⊤; B) = (A ef⊤; 0 B)` (Definition 12 (ii)). -/
def sum2 (A : Matrix (Fin kA) (Fin nA) ℤ) (e : Fin kA → ℤ) (f : Fin nB → ℤ)
    (B : Matrix (Fin kB) (Fin nB) ℤ) : Matrix (Fin kA ⊕ Fin kB) (Fin nA ⊕ Fin nB) ℤ :=
  fromBlocks A (vecMulVec e f) 0 B

/-- The left summand `(A e e; h⊤ 0 1)` of a 3-sum. -/
def sum3Left (A : Matrix (Fin kA) (Fin nA) ℤ) (e : Fin kA → ℤ) (h : Fin nA → ℤ) :
    Matrix (Fin kA ⊕ Fin 1) (Fin nA ⊕ Fin 2) ℤ :=
  fromBlocks A (of fun i _ => e i) (replicateRow (Fin 1) h) !![0, 1]

/-- The right summand `(0 1 f⊤; g g B)` of a 3-sum. -/
def sum3Right (f : Fin nB → ℤ) (g : Fin kB → ℤ) (B : Matrix (Fin kB) (Fin nB) ℤ) :
    Matrix (Fin 1 ⊕ Fin kB) (Fin 2 ⊕ Fin nB) ℤ :=
  fromBlocks !![0, 1] (replicateRow (Fin 1) f) (of fun i _ => g i) B

/-- The 3-sum `(A e e; h⊤ 0 1) ⊕₃ (0 1 f⊤; g g B) = (A ef⊤; gh⊤ B)` (Definition 12 (iii)). -/
def sum3 (A : Matrix (Fin kA) (Fin nA) ℤ) (e : Fin kA → ℤ) (f : Fin nB → ℤ) (g : Fin kB → ℤ)
    (h : Fin nA → ℤ) (B : Matrix (Fin kB) (Fin nB) ℤ) :
    Matrix (Fin kA ⊕ Fin kB) (Fin nA ⊕ Fin nB) ℤ :=
  fromBlocks A (vecMulVec e f) (vecMulVec g h) B

/-- **Pivoting** on the entry `T_ij` (Definition 13): with `ε = T_ij`, the entry becomes `−ε`, the
rest of row `i` is multiplied by `ε`, the rest of column `j` is multiplied by `ε`, and every other
entry `T_{i'j'}` becomes `T_{i'j'} − ε T_{i'j} T_{ij'}`. Meaningful when `T_ij ∈ {−1, 1}`. -/
def pivot {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) (i : Fin k) (j : Fin n) :
    Matrix (Fin k) (Fin n) ℤ :=
  of fun i' j' =>
    if i' = i ∧ j' = j then -T i j
    else if i' = i then T i j * T i j'
    else if j' = j then T i j * T i' j
    else T i' j' - T i j * T i' j * T i j'

/-- A candidate decomposition of a `k × n` matrix as a 1-, 2- or 3-sum (`kind = 1, 2, 3`) after
row and column permutations `rows`, `cols`. -/
structure Decomp (k n : ℕ) where
  kind : ℕ
  kA : ℕ
  nA : ℕ
  kB : ℕ
  nB : ℕ
  rows : Fin k → Fin kA ⊕ Fin kB
  cols : Fin n → Fin nA ⊕ Fin nB
  A : Matrix (Fin kA) (Fin nA) ℤ
  B : Matrix (Fin kB) (Fin nB) ℤ
  e : Fin kA → ℤ
  f : Fin nB → ℤ
  g : Fin kB → ℤ
  h : Fin nA → ℤ

namespace Decomp

/-- `d` decomposes `T`, possibly after row and column permutations, into a 1-, 2- or 3-sum (as
`d.kind` says) of **totally unimodular** summands with `nA, nB ≥ 2` (Theorem 14 (iii), p.8). Vectors
that a sum of the given kind does not use are ignored. -/
def IsSumOf {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) (d : Decomp k n) : Prop :=
  Function.Bijective d.rows ∧ Function.Bijective d.cols ∧ 2 ≤ d.nA ∧ 2 ≤ d.nB ∧
  ((d.kind = 1 ∧ d.A.IsTotallyUnimodular ∧ d.B.IsTotallyUnimodular ∧
      ∀ i j, T i j = sum1 d.A d.B (d.rows i) (d.cols j)) ∨
   (d.kind = 2 ∧ (sum2Left d.A d.e).IsTotallyUnimodular ∧
      (sum2Right d.f d.B).IsTotallyUnimodular ∧
      ∀ i j, T i j = sum2 d.A d.e d.f d.B (d.rows i) (d.cols j)) ∨
   (d.kind = 3 ∧ (sum3Left d.A d.e d.h).IsTotallyUnimodular ∧
      (sum3Right d.f d.g d.B).IsTotallyUnimodular ∧
      ∀ i j, T i j = sum3 d.A d.e d.f d.g d.h d.B (d.rows i) (d.cols j)))

/-- Encoding `[kind, kA, nA, kB, nB] ++ rows ++ cols ++ A ++ B ++ e ++ f ++ g ++ h`, where a row
placed in block `A` at index `a` is written `a`, and one placed in block `B` at index `b` is written
`kA + b` (columns likewise with `nA`). -/
def enc {k n : ℕ} (d : Decomp k n) : List ℤ :=
  [(d.kind : ℤ), (d.kA : ℤ), (d.nA : ℤ), (d.kB : ℤ), (d.nB : ℤ)] ++
  List.ofFn (fun i => Sum.elim (fun a : Fin d.kA => (a.val : ℤ))
    (fun b : Fin d.kB => ((d.kA + b.val : ℕ) : ℤ)) (d.rows i)) ++
  List.ofFn (fun j => Sum.elim (fun a : Fin d.nA => (a.val : ℤ))
    (fun b : Fin d.nB => ((d.nA + b.val : ℕ) : ℤ)) (d.cols j)) ++
  encMat d.A ++ encMat d.B ++ encVec d.e ++ encVec d.f ++ encVec d.g ++ encVec d.h

end Decomp

end CongruencyTU


