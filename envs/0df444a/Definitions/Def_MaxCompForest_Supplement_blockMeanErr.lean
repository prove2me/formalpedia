-- Prove2me | Definitions.Def_MaxCompForest_Supplement_blockMeanErr
-- name    : MaxCompForest_Supplement_blockMeanErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:01.330278+00:00
-- url     : https://prove2.me/theorems/5ee456d0-0f41-498b-9323-61d6f63d680c
-- title:
--   Weighted block-mean error of a feature map
-- statement:
--   For a feature map $\Phi:V\to\mathbb R^d$, masses $d_v$ and a partition $Q$ of $V$, the **weighted block-mean error** is
--
--   $$\sum_{B\in Q}\sum_{v\in B} d_v\,\|\Phi_v-\Phi_B\|^2,\qquad \Phi_B=\frac{\sum_{v\in B} d_v\Phi_v}{\sum_{v\in B} d_v}.$$
--
--   It is the error of quantizing $\Phi$ by the blocks of $Q$ with each block represented by its weighted mean, the quantity bounded in Lemma 5.1 and Theorem J.1.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 5.1, p.29 (PDF p.31); Theorem J.1, p.59 (PDF p.61)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The weighted block-mean error** `∑_{B ∈ Q} ∑_{v ∈ B} d_v ‖Φ_v − Φ_B‖²`, with `Φ_B = (∑_{v∈B} d_v Φ_v)/(∑_{v∈B} d_v)`
the weighted mean of the block.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 5.1, p.29; Theorem J.1 ("weighted mean error"), p.59. -/
noncomputable def blockMeanErr {d : ℕ} (W : V → ℝ) (x : V → EuclideanSpace ℝ (Fin d))
    (Q : Finpartition (Finset.univ : Finset V)) : ℝ :=
  ∑ B ∈ Q.parts, ∑ v ∈ B, W v * ‖x v - (∑ u ∈ B, W u)⁻¹ • ∑ u ∈ B, W u • x u‖ ^ 2

end MaxCompForest.Supplement


