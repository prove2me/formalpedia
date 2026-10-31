-- Prove2me | Definitions.Def_KempeCloning_FockIndex
-- name    : KempeCloning_FockIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:47.726448+00:00
-- url     : https://prove2.me/theorems/9c536494-01f7-431a-a07e-48682102fce5
-- title:
--   Occupation-number labels $n:\{a_1,a_2,b_1,b_2,c\}\to\mathbb N$
-- statement:
--   A Fock index is a map $n$ assigning to each of the five modes $k\in\{a_1,a_2,b_1,b_2,c\}$ an occupation number $n_k\in\mathbb N$. It labels the number state
--
--   $$|n\rangle = |n_{a_1}, n_{a_2}, n_{b_1}, n_{b_2}, n_c\rangle ,$$
--
--   the simultaneous eigenvector of the five number operators. These states form the orthonormal Fock basis of the five-mode system.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (13) and (15), p.4

import Definitions.Def_KempeCloning_Mode

namespace KempeCloning

/-- **Occupation-number labels of the five-mode Fock basis.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (13) and (15), p.4: number states
`|n_{a1}, n_{a2}, n_{b1}, n_{b2}, n_c⟩`.

A Fock index `n : FockIndex` assigns to every mode `k` its occupation number `n k ∈ ℕ`; the
paper's ket `|n_{a1}, n_{a2}, n_{b1}, n_{b2}, n_c⟩` is the basis vector labelled by `n`. -/
abbrev FockIndex : Type := Mode → ℕ

end KempeCloning


