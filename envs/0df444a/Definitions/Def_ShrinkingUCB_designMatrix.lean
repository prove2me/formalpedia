-- Prove2me | Definitions.Def_ShrinkingUCB_designMatrix
-- name    : ShrinkingUCB_designMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:34.353521+00:00
-- url     : https://prove2.me/theorems/050a1a06-fa13-4e0a-b235-c8e1c59f5981
-- title:
--   The matrices $A_{t,k}$ of an arbitrary array of vectors
-- statement:
--   Let $x_{(t,k)}\in\mathbb R^d$, for periods $t\ge1$ and $k\in[K]$, be any array of vectors. With $A_0=I$ and $A_t=A_{t-1}+\sum_{k=1}^Kx_{(t,k)}x_{(t,k)}^\top$, define
--
--   $$
--   A_{t,k}=A_{t-1}+\sum_{j=1}^kx_{(t,j)}x_{(t,j)}^\top
--   $$
--
--   for $k\in\{0,\dots,K\}$. These are the matrices of Lemma 2.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §3.2.1, p.11

import Mathlib

open Matrix

namespace ShrinkingUCB

/-- The matrix `A_{t,k}` of an arbitrary array of vectors `x_{(t,k)}`, `t ≥ 1`, `1 ≤ k ≤ K`
(arXiv:1903.07844v2, §3.2.1, p.11):
`A_{t,k} = A_{t-1} + ∑_{i=1}^k x_{(t,i)} x_{(t,i)}ᵀ`, where `A_{t-1} = I` plus the outer products
of all `K` vectors of each of the periods before `t`. -/
noncomputable def designMatrix {d : ℕ} (v : ℕ → ℕ → Fin d → ℝ) (K t k : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + ∑ s ∈ Finset.Ico 1 t, ∑ j ∈ Finset.Icc 1 K, vecMulVec (v s j) (v s j)
    + ∑ j ∈ Finset.Icc 1 k, vecMulVec (v t j) (v t j)

end ShrinkingUCB


