-- Prove2me | Definitions.Def_GreedNorm_IsThreshold
-- name    : GreedNorm_IsThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:33.963893+00:00
-- url     : https://prove2.me/theorems/1398f88d-3b44-408f-a66b-e20a38ae0da3
-- title:
--   Threshold vector
-- statement:
--   A **threshold vector** is a vector $t=(t_\ell)_{\ell\in\mathrm{POS}}\in\mathbb R^{|\mathrm{POS}|}_{\ge0}$ whose entries are non-increasing: $\ell\le\ell'$ in $\mathrm{POS}$ implies $t_{\ell'}\le t_\ell$.
--
--   **Formalization Note** $t$ is a function $\mathbb N\to\mathbb R$ of which only the values on $\mathrm{POS}_{m,\epsilon}$ matter.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2, p.5 (PDF 7); Definition 2.1, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_POS

namespace GreedNorm

/-- **Threshold vector**: a nonnegative vector indexed by `POS_{m,ϵ}` whose entries are
non-increasing.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2, p.5 (PDF 7): "A threshold vector t is a |POS|-dimensional vector whose entries are
non-increasing", and Definition 2.1, "Let t ∈ R^{|POS|}_{≥0} be a threshold vector".

**Formalization Note** A threshold vector is a function `t : ℕ → ℝ` of which only the values
`t ℓ` for `ℓ ∈ POS m ε` matter: they are nonnegative, and `ℓ ≤ ℓ'` in POS gives
`t ℓ' ≤ t ℓ` (so `t 1` is the largest entry). -/
def IsThreshold (m : ℕ) (ε : ℝ) (t : ℕ → ℝ) : Prop :=
  (∀ ℓ ∈ POS m ε, 0 ≤ t ℓ) ∧ ∀ ℓ ∈ POS m ε, ∀ ℓ' ∈ POS m ε, ℓ ≤ ℓ' → t ℓ' ≤ t ℓ

end GreedNorm


