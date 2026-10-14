-- Prove2me | Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
-- name    : QAlgorithms_DeWolf_Ch03_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:28:03.714146+00:00
-- url     : https://prove2.me/theorems/465213de-dff2-4456-bd2a-1e7e2a30e208
-- title:
--   DeWolf Ch03: supporting definitions
-- statement:
--   de Wolf, Chapter 3: Simon's algorithm
--
--   ## QAlgorithms.DeWolf.simonBitsToZMod2
--
--   For any natural number $n$ and Boolean string $b$ indexed by $0,\ldots,n-1$, this defines the vector in $\mathbb F_2^n$ whose coordinate $k$ is $1$ when $b_k$ is true and $0$ otherwise. For $n=0$, the result is the unique vector with no coordinates.
--
--   ## QAlgorithms.DeWolf.simonSpanRank
--
--   For any natural numbers $m,n$ and indexed family $(l_k)_{0\leq k<m}$ of $n$-bit Boolean strings, this is the dimension over $\mathbb F_2$ of the linear span of the vectors obtained by replacing each true bit of each $l_k$ by $1$ and each false bit by $0$. Repetitions contribute no new generators. If $m=0$ the span is the zero subspace and the result is $0$; if $n=0$ it is also $0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/DeWolf/Ch03.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Query
/-!
# de Wolf, Chapter 3: Simon's algorithm

R. de Wolf, *Quantum Computing: Lecture Notes*, §3.1–§3.3 (PDF pp. 35–38).

`N = 2^n` and the index set `{0, …, N − 1}` is identified with `{0,1}^n = Qubits n`. The input
`x = (x_0, …, x_{N−1})` with `x_i ∈ {0,1}^n` is a function `x : Qubits n → Qubits n`; one query
returns the whole string `x_i`, in its unitary form `|i, y⟩ ↦ |i, y ⊕ x_i⟩` (`xorOracle x`).
Simon's promise "`x_i = x_j` iff `i = j` or `i = j ⊕ s`" is `SimonPromise x s`; the bitwise sum
`j ⊕ s` is `j + s` in `Fin n → Bool`. One run of the quantum subroutine is the fixed circuit
`(H^{⊗n} ⊗ I) O_x (H^{⊗n} ⊗ I)` applied to `|0^n⟩|0^n⟩` (`simonRunState x`), followed by a
measurement of the first register; the intermediate measurement of the second register is
"not necessary" (p. 36), so the first-register marginal is used.
-/

namespace QAlgorithms.DeWolf

/-- An `n`-bit string as a vector of `𝔽₂^n` (`ZMod 2`), so that linear (in)dependence of the
outcomes `j` "modulo 2" (de Wolf p. 36) can be expressed. -/
def simonBitsToZMod2 {n : ℕ} (b : Qubits n) : Fin n → ZMod 2 :=
  fun k => if b k then 1 else 0

/-- The dimension over `𝔽₂` of the span of the strings `l 0, …, l (m − 1)` (de Wolf p. 36:
"the j's you have generated at some point span a space of size `2^k`"; this is `k`). -/
noncomputable def simonSpanRank {m n : ℕ} (l : Fin m → Qubits n) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun k => simonBitsToZMod2 (l k)))



end QAlgorithms.DeWolf


