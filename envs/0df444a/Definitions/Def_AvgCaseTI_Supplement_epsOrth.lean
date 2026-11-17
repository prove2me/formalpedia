-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_epsOrth
-- name    : AvgCaseTI_Supplement_epsOrth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:32:57.597594+00:00
-- url     : https://prove2.me/theorems/f98f4873-2b19-4fcc-9a91-82f7b66d21ac
-- title:
--   The tuple-centralizer exception probability $\varepsilon_{n,q}$
-- statement:
--   For an $n\times n\times n$ array $A$ over $\mathbb F_q$, let $A_1,\dots,A_n$ be its horizontal slices, $A_i(j,k)=a_{i,j,k}$. For $X\in\mathrm M(n,q)$ put
--   $$
--   \widehat X=\begin{pmatrix}0&X\\X^t&0\end{pmatrix},\qquad E=\begin{pmatrix}I_n&0\\0&0\end{pmatrix},\qquad \mathcal T_A=(I_{2n},E,\widehat{A_1},\dots,\widehat{A_n}).
--   $$
--   The **tuple centralizer** is $C_{\mathrm O}(\mathcal T_A)=\{h\in\mathrm O(2n,q): hT=Th\text{ for every entry }T\text{ of }\mathcal T_A\}$; it always contains $\pm I_{2n}$. Then
--   $$
--   \varepsilon_{n,q}:=\Pr_A\bigl[C_{\mathrm O}(\mathcal T_A)\ne\{\pm I_{2n}\}\bigr],
--   $$
--   the proportion of the $q^{n^3}$ arrays whose tuple centralizer is larger than $\{\pm I_{2n}\}$. It is one of the three error terms of Theorem 5.6.
--
--   **Formalization Note** $2n\times 2n$ matrices are indexed by two copies of $[n]$, matching the block structure.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Eqs. (23), (34), pp.29, 32 (PDF pp.31, 34)

import Mathlib
import Definitions.Def_AvgCaseTI_Tensor3

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The horizontal slice `A_i(j, k) = a_{i,j,k}` (§2.3, p.15, PDF p.17). -/
def horizontal (A : Tensor3 K n) (i : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k => A i j k

/-- `X̂ = [[0, X], [Xᵗ, 0]]`, Eq. (23), p.29 (PDF p.31), indexed by `Fin n ⊕ Fin n`. -/
def hatMat (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 X Xᵀ 0

/-- `E = [[I_n, 0], [0, 0]]`, Eq. (23). -/
def Emat (K : Type*) [Field K] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 1 0 0 0

/-- **The tuple centralizer `C_O(T_A)`**, §5.1, p.29 (PDF p.31): for `T_A = (I_{2n}, E, Â_1, …, Â_n)`,
"G_A := C_O(T_A) = {h ∈ O(2n, q) : hT = Th for every entry T of T_A}". -/
def tupleCent (A : Tensor3 K n) : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
  {h | hᵀ * h = 1 ∧ h * 1 = 1 * h ∧ h * Emat K n = Emat K n * h ∧
    ∀ i : Fin n, h * hatMat (horizontal A i) = hatMat (horizontal A i) * h}

/-- **`ε_{n,q} = Pr_A[C_O(T_A) ≠ {±I_{2n}}]`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Eq. (34), p.32 (PDF p.34): "Define ε_{n,q} := Pr_A [C_O(T_A) ≠ {±I_{2n}}]".

`epsOrth K n` is the proportion, among all `n × n × n` arrays `A` over `K`, of those whose tuple
centralizer is not `{I, −I}`.

**Formalization Note.** `O(2n, q)` is indexed by `Fin n ⊕ Fin n` (the block structure of Eq. (23)). The
value depends on `K` only through `q = |K|`. -/
noncomputable def epsOrth (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Tensor3 K n // tupleCent A ≠ {1, -1}} : ℝ) / (Nat.card (Tensor3 K n) : ℝ)

end AvgCaseTI.Supplement


