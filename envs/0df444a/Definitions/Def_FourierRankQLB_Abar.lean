-- Prove2me | Definitions.Def_FourierRankQLB_Abar
-- name    : FourierRankQLB_Abar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:47.926193+00:00
-- url     : https://prove2.me/theorems/255723d3-def1-49a7-ae6b-a074f2e2ad15
-- title:
--   The padded matrix $\overline A_{n,Q}$
-- statement:
--   For $Q\in O(d_n)$,
--   $$
--   \overline A_{n,Q}=\begin{cases}A_Q,&\ell_n=0,\\ A_Q\oplus[1],&\ell_n=1.\end{cases}
--   $$
--   It extends the quadratic form of $A_Q$ to all of $\mathbb R^n$, one fixed coordinate being appended when $n$ is odd.
--
--   **Formalization Note** The block $A_Q$ occupies the first $d_n$ indices.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (36), p.25

import Mathlib
import Definitions.Def_FourierRankQLB_AQ
import Definitions.Def_FourierRankQLB_dn

open Matrix

namespace FourierRankQLB

/-- The padded matrix `Ā_{n,Q}` of Eq. (36): `A_Q` when `n` is even, `A_Q ⊕ [1]` when `n` is odd.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (36), p. 25.

**Formalization Note.** The block `A_Q` occupies the first `dn n` indices. An index outside them
exists only for odd `n` (the index `n - 1`), where the diagonal entry is `1`. -/
noncomputable def Abar {n : ℕ} (Q : Od (dn n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i.1 < dn n ∧ j.1 < dn n then AQ Q ⟨i.1, h.1⟩ ⟨j.1, h.2⟩
    else if i = j then 1 else 0

end FourierRankQLB


