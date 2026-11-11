-- Prove2me | Definitions.Def_LowRankShifts_MatPoly_MatPoly
-- name    : LowRankShifts_MatPoly_MatPoly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:28.835237+00:00
-- url     : https://prove2.me/theorems/5e663593-9abe-4ebc-b06b-84abaa2ff645
-- title:
--   Non-commutative matrix polynomials with transposes as lists of monomials: evaluation, degree and number of monomials
-- statement:
--   Fix a field $F$ and a number $\ell$ of matrix variables. A **letter** is a pair $(i,t)$ of a variable index $i\in\{1,\dots,\ell\}$ and a transpose flag $t$; it stands for $X_i$ when $t$ is false and for $X_i^T$ when $t$ is true. A **word** is a finite sequence of letters. A **matrix polynomial** $P\in F\langle X_1,\dots,X_\ell,\cdot^T\rangle$ is a finite list of **monomials** $(c,w)$, each a coefficient $c\in F$ and a word $w$. At a tuple $A=(A_1,\dots,A_\ell)$ of $n\times n$ matrices over $F$ its value is
--
--   $$P(A)=\sum_{(c,w)\in P} c\,w(A),\qquad w(A)=Y_1Y_2\cdots Y_k,\quad Y_j=\begin{cases}A_i&\text{if the $j$-th letter is }(i,\text{false}),\\ A_i^T&\text{if it is }(i,\text{true}),\end{cases}$$
--
--   the empty word evaluating to the identity matrix. The **number of monomials** $s$ of $P$ is the length of the list, and its **degree** $d$ is the maximal length of a word in the list ($0$ for the empty list). $P$ is **transpose-free**, i.e. $P\in F\langle X_1,\dots,X_\ell\rangle$, when no letter carries the transpose flag.
--
--   This is the representation the paper fixes ("we assume that such polynomials are represented as lists of monomials"). A list in which every word occurs once and with a nonzero coefficient has as $s$ and $d$ the number of monomials and the degree of the polynomial it represents.
--
--   **Formalization Note.** Variable indices are `Fin ℓ` (0-based). `eval P A`, `size P`, `degree P` and `TransposeFree P` are the value, $s$, $d$ and transpose-freeness.
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 8 (PDF 11), §2.2

import Mathlib

open Matrix

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-!
# Non-commutative matrix polynomials with transposes, as lists of monomials

Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, *Worst-Case to Average-Case Reductions
for Linear Algebra: Optimal, Simple, and General*, STOC 2027 submission, p. 8, §2.2:
"We write F⟨X_1, . . . , X_ℓ, ·^T⟩ for the set of all non-commutative polynomials in matrix
variables and their transposes X_1, . . . , X_ℓ, X_1^T, . . . , X_ℓ^T. [...] We assume that such
polynomials P are represented as lists of monomials."

* A letter is a pair `(i, t)` with `i : Fin ℓ`; it stands for `X_i` when `t = false` and for
  `X_iᵀ` when `t = true`.
* A word is a list of letters; the empty word evaluates to the identity matrix.
* A polynomial is a list of monomials `(c, w)`: coefficient `c` and word `w`.
* `size P` (the paper's `s`) is the number of monomials in the list; `degree P` (the paper's `d`)
  is the maximal word length (`0` for the empty list).
* `TransposeFree P` says that no letter is transposed: these are the polynomials of
  `F⟨X_1, . . . , X_ℓ⟩` (Lemma 2.8).
-/

/-- A letter: variable index and transpose flag (`true` = transposed). -/
abbrev Letter (ℓ : ℕ) := Fin ℓ × Bool

/-- A word over the letters `X_i`, `X_iᵀ`. -/
abbrev Word (ℓ : ℕ) := List (Letter ℓ)

/-- A non-commutative matrix polynomial with transposes, as a list of (coefficient, word) pairs. -/
abbrev MatPolynomial (F : Type*) (ℓ : ℕ) := List (F × Word ℓ)

variable {F : Type*} [Field F] {ℓ n : ℕ}

/-- The value of one letter at the tuple `A`: `A_i` or `A_iᵀ`. -/
def letterEval (A : Fin ℓ → Matrix (Fin n) (Fin n) F) (x : Letter ℓ) : Matrix (Fin n) (Fin n) F :=
  if x.2 then (A x.1)ᵀ else A x.1

/-- The value of a word at the tuple `A`: the ordered product of its letters (`1` if empty). -/
def wordEval (A : Fin ℓ → Matrix (Fin n) (Fin n) F) (w : Word ℓ) : Matrix (Fin n) (Fin n) F :=
  (w.map (letterEval A)).prod

/-- The value `P(A_1, …, A_ℓ) = Σ c · w(A)` of a matrix polynomial at a tuple of `n × n`
matrices. -/
def eval (P : MatPolynomial F ℓ) (A : Fin ℓ → Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  (P.map fun m => m.1 • wordEval A m.2).sum

/-- The number `s` of monomials of `P` (the length of the list). -/
def size (P : MatPolynomial F ℓ) : ℕ := P.length

/-- The degree `d` of `P`: the maximal length of a word of `P` (`0` for the empty list). -/
def degree (P : MatPolynomial F ℓ) : ℕ := (P.map fun m => m.2.length).foldr max 0

/-- `P` has no transposed letter, i.e. `P ∈ F⟨X_1, …, X_ℓ⟩`. -/
def TransposeFree (P : MatPolynomial F ℓ) : Prop := ∀ m ∈ P, ∀ x ∈ m.2, x.2 = false

end LowRankShifts.MatPoly


