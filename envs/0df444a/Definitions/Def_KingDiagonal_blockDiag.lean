-- Prove2me | Definitions.Def_KingDiagonal_blockDiag
-- name    : KingDiagonal_blockDiag
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.452985+00:00
-- url     : https://prove2.me/theorems/3d6196dc-fe1d-4b44-b937-b6567d424f41
-- title:
--   Block-diagonal matrix $V = \mathrm{diag}(V_1,\dots,V_n)$ (eq. 23)
-- statement:
--   Given $n$ matrices $V_1,\dots,V_n$, each of size $r\times s$, the block-diagonal matrix
--
--   $$
--   V = \operatorname{diag}(V_1, V_2, \dots, V_n) = \begin{pmatrix} V_1 & 0 & \cdots & 0\\ 0 & V_2 & \cdots & 0\\ \vdots & & \ddots & \vdots\\ 0 & 0 & \cdots & V_n\end{pmatrix}
--   $$
--
--   is the $(nr)\times(ns)$ matrix with entries $V_{(i,a),(i',c)} = (V_i)_{a,c}$ if $i = i'$ and $0$ otherwise. In King's factorization $(\Phi\otimes\Psi)(\rho) = VKV^*$ the blocks are the block rows of $((I\otimes\Psi)(\tau))^{1/2}$, and the same construction describes the block-diagonal matrix $(V^*V)^p$ in (25).
--
--   **Formalization Note** Row and column indices are pairs with the block index first ($n\times r$, $n\times s$), matching the Kronecker order used throughout.
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (23), p.6 (also (20)–(21), pp.5–6, and (25), p.6)

import Mathlib

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (23), p.6 (also the outer factors of (20)–(21), pp.5–6,
and (25), p.6): the block-diagonal matrix `V = diag(V_1, V_2, …, V_n)` with the blocks `V_i` on the
diagonal and `0` elsewhere. For `V_i : r × s`, `V` is the `(n·r) × (n·s)` matrix with entries
`V_{(i,a),(i',c)} = (V_i)_{a,c}` if `i = i'` and `0` otherwise.

**Formalization Note.** Row and column indices are `n × r` and `n × s` with the block index
first, matching the Kronecker order `A ⊗ B` of the paper (`(A ⊗ₖ B) (i,a) (j,b) = A i j * B a b`).
In (23) the blocks are `V_i : m × nm` (the page's `k × kn`), so `V` is `nm × n²m`. -/
def blockDiag {n r s : Type*} [DecidableEq n] (V : n → Matrix r s ℂ) :
    Matrix (n × r) (n × s) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.1 p.2 q.2 else 0

end KingDiagonal


