-- Prove2me | Definitions.Def_CubicProductLB_TriplePartition
-- name    : CubicProductLB_TriplePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:15:54.281449+00:00
-- url     : https://prove2.me/theorems/84c0e3ae-524d-4990-b5d8-839495d0221a
-- title:
--   Triple partitions and the identification map $\iota_P$
-- statement:
--   A **triple partition** of $[3M]$ is a family $P = \{T_1, \dots, T_M\}$ of pairwise disjoint three-element sets with union $[3M]$. Its **identification map** $\iota_P : \{0,1\}^M \to \{0,1\}^{3M}$ is given by
--   $$(\iota_P(y))_i = y_j \quad \text{whenever } i \in T_j,$$
--   so that all three coordinates of a block are identified with one clustered variable.
--
--   **Formalization Note** A partition is encoded by the labelling that sends a position to the index of its block, with every fibre of size three; this is the same thing up to naming the blocks. The length is written $3M$, so no division occurs.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (255)–(257), p.30

import Mathlib

namespace CubicProductLB

/-- A triple partition `P = {T_1, …, T_M}` of `[3M]` into three-element blocks, as the labelling
`block i = j ⟺ i ∈ T_j` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (255), p.30).

**Formalization Note** A partition into `M` blocks of size three is the same as such a labelling, up
to naming the blocks. The length is written `3 * M` so that no division by three occurs. -/
structure TriplePartition (M : ℕ) where
  /-- the index of the block containing a position -/
  block : Fin (3 * M) → Fin M
  /-- every block has exactly three elements -/
  card_block : ∀ j, (Finset.univ.filter fun i => block i = j).card = 3

/-- The identification map `ι_P : {0,1}^M → {0,1}^N`, `(ι_P y)_i = y_j` whenever `i ∈ T_j`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (256)–(257), p.30). -/
def TriplePartition.iota {M : ℕ} (P : TriplePartition M) (y : Fin M → Bool) :
    Fin (3 * M) → Bool :=
  fun i => y (P.block i)

end CubicProductLB


