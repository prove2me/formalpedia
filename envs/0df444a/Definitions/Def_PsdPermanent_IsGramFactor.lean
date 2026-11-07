-- Prove2me | Definitions.Def_PsdPermanent_IsGramFactor
-- name    : PsdPermanent_IsGramFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:41.254844+00:00
-- url     : https://prove2.me/theorems/9b144ddc-2d2b-4c14-bf88-8f6a89a9d260
-- title:
--   Full column rank Gram factor $A=VV^\dagger$
-- statement:
--   A **Gram factor** of an $n\times n$ Hermitian positive semidefinite matrix $A$ is a matrix $V\in\mathbb C^{n\times d}$ of full column rank with
--   $$A=VV^\dagger .$$
--   The $i$th row of $V$ is written $v_i^\dagger$, so that $A_{ij}=v_i^\dagger v_j$. The rank condition forces $d=\operatorname{rank}A$. The vectors $v_i$ are the data of the relaxation.
--
--   **Formalization Note** The vectors $v_i$ are not declared. By the row convention, $v_i^\dagger z=(Vz)_i$ and $v_i^\dagger Xv_i=\operatorname{Re}(VXV^\dagger)_{ii}$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3

import Mathlib
open Matrix

namespace PsdPermanent

/-- **Full column rank Gram factor.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3: "if A ⪰ 0 has rank d, then A = V V†, where V ∈ C^{n×d} has full column rank. The ith
row of V is denoted v_i†, so that A_ij = v_i† v_j."

`IsGramFactor A V` says `A = V * Vᴴ` and that `V : ℂ^{n×d}` has rank `d`.

**Formalization Note.** §3's row convention: `v_i` is the conjugate of row `i` of `V`, so
`v_i†z = (V *ᵥ z) i` and `v_i†Xv_i = ((V * X * Vᴴ) i i).re`; no separate vector `v_i` is declared.
The rank of a factor is forced to be `rank A`, so `d` need not be tied to `A` here. -/
def IsGramFactor {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin d) ℂ) : Prop :=
  A = V * Vᴴ ∧ V.rank = d

end PsdPermanent


