-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
-- name    : OAI_LinearAlgebra_CirculantHadamard_Witnesses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:47:35.152412+00:00
-- url     : https://prove2.me/theorems/2b35527f-c7ed-49e6-9fdf-1ef64b479633
-- title:
--   Explicit circulant Hadamard matrices of orders one and four
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Order one.** The first row $(1)$ and the $1\times1$ matrix $(1)$.
--   2. **Order four.** The first row $(1,1,1,-1)$ and the real matrix
--   $$
--   \begin{pmatrix}1&1&1&-1\\ -1&1&1&1\\ 1&-1&1&1\\ 1&1&-1&1\end{pmatrix},
--   $$
--   whose rows are the cyclic shifts of that first row. In both cases row $0$ of the matrix is the stated first row; these are the witnesses for the two orders that do occur.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/Witnesses.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/Witnesses.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CirculantHadamard mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic

namespace OAI

namespace CirculantHadamard

def firstRow_one : Fin 1 → ℝ := ![1]

def firstRow_four : Fin 4 → ℝ := ![1, 1, 1, -1]

def witness_one : Matrix (Fin 1) (Fin 1) ℝ := !![1]

def witness_four : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, -1;
    -1, 1, 1, 1;
     1, -1, 1, 1;
     1, 1, -1, 1]

@[simp] theorem witness_one_first_row : witness_one 0 = firstRow_one := rfl

@[simp] theorem witness_four_first_row : witness_four 0 = firstRow_four := rfl

end CirculantHadamard

end OAI


