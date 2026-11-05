-- Prove2me | Definitions.Def_RepGQML_IrrepSum
-- name    : RepGQML_IrrepSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:29.182383+00:00
-- url     : https://prove2.me/theorems/7f8afb3d-4732-4e25-9389-9fd65d7d9d87
-- title:
--   The Hilbert direct sum of multiplicity spaces tensored with irreps
-- statement:
--   Given finitely many labels $k$, multiplicities $m_k$ and complex inner product spaces $V_k$, this is the Hilbert space
--   $$
--   \bigoplus_{k}\ \mathbb C^{m_k}\otimes V_k ,
--   $$
--   on which $\bigoplus_k \mathbb 1_{m_k}\otimes U_k$ acts. The first factor of each summand is the multiplicity space and the second carries the irrep, as in the source.
--
--   **Formalization Note** The sum is `PiLp 2`, and each summand has Mathlib's inner product on a tensor product.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Theorem 7, p.28

import Mathlib

namespace RepGQML

open scoped TensorProduct in
/-- The Hilbert direct sum `⨁_k ℂ^{m_k} ⊗ V_k` on which the decomposition
`U = ⨁_k 𝟙_{m_k} ⊗ U_k` of Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Theorem 7, p.28, acts. The first factor of each summand is the
multiplicity space and the second carries the irrep.

**Formalization Note** The factor order is the page's: multiplicity first, in (30) as well. `PiLp 2`
gives the orthogonal direct sum of inner product spaces, and each tensor product carries Mathlib's
product inner product. -/
abbrev IrrepSum {K : Type*} [Fintype K] (m : K → ℕ) (V : K → Type*)
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℂ (V k)] : Type _ :=
  PiLp 2 fun k => EuclideanSpace ℂ (Fin (m k)) ⊗[ℂ] V k

end RepGQML


