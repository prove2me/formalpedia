-- Prove2me | Definitions.Def_Chi2QEC_pumpSubspace
-- name    : Chi2QEC_pumpSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:30.907415+00:00
-- url     : https://prove2.me/theorems/55c19487-70f7-4c6c-bc46-18f4366ec240
-- title:
--   The space $\mathcal H_{q-1}^{\otimes n}$
-- statement:
--   The pump-photon subspace of one qudit is
--   $$
--   \mathcal H_{q-1}=\mathrm{Span}\{|j,j,q-1-j\rangle:0\le j\le q-1\}.
--   $$
--   This is the $n$-fold tensor power $\mathcal H_{q-1}^{\otimes n}$, the span of the product states $\bigotimes_\ell|j_\ell,j_\ell,q-1-j_\ell\rangle$.
--
--   A $\chi^{(2)}$ code of $n$ physical qudits of dimension $q$ lies in this space, which is the constraint that distinguishes the photon-loss Hamming bound from a bound on arbitrary codes.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. III A, p.5; proof of Theorem 5, p.17

import Mathlib
import Definitions.Def_Chi2QEC_pumpIndex

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. III A, p.5 (`H_N ≡ Span{|0, 0, N⟩, |1, 1, N - 1⟩, …, |N, N, 0⟩}`), and
proof of Theorem 5, p.17: the space `H_{q-1}^{⊗n}` in which the code of `n` physical qudits of
dimension `q` lies, spanned by the product states `⊗_ℓ |j_ℓ, j_ℓ, q - 1 - j_ℓ⟩`. -/
noncomputable def pumpSubspace (n q : ℕ) : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q)) :=
  Submodule.span ℂ ((fun x => EuclideanSpace.single x (1 : ℂ)) '' pumpIndex n q)

end Chi2QEC


