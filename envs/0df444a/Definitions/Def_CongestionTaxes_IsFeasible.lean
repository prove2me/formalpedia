-- Prove2me | Definitions.Def_CongestionTaxes_IsFeasible
-- name    : CongestionTaxes_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:01.186303+00:00
-- url     : https://prove2.me/theorems/1b0be9c6-78e6-4fe1-8d78-8bd962b7a36e
-- title:
--   Feasible points of the convex program (12)
-- statement:
--   A point $\bigl((y_i)_{i},(v_r)_{r}\bigr)$ is **feasible for program (12)** if each $y_i\in\Delta(s_i)$ is a probability vector over the $s_i=|\mathcal A_i|$ actions $a_{i,1},\dots,a_{i,s_i}$ of agent $i$, and
--
--   $$
--   v_r=\sum_{i=1}^N\ \sum_{k:\ r\in a_{i,k}}y_{i,k}\qquad\text{for every resource }r .
--   $$
--
--   So $v_r$ is the expected load of resource $r$ when each agent independently plays $y_i$.
--
--   **Formalization Note** $y_i$ is a weight on every subset of resources, nonnegative, zero outside $\mathcal A_i$ and summing to $1$ over $\mathcal A_i$.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (12), p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionTaxes

/-- **Feasibility for the convex program (12)** (Paccagnan, Gairing, arXiv:2105.07480v2, (12),
p.19): `y_i ∈ Δ(s_i)` is a probability vector over the `s_i = |𝓐_i|` actions of agent `i`, and
`v_r = ∑_{i=1}^N ∑_{k : r ∈ a_{i,k}} y_{i,k}` for every resource `r`.

**Formalization Note** `y i` is a weight on every subset of resources: nonnegative, zero outside
`G.strategies i`, and summing to `1` over `G.strategies i`. This is the simplex `Δ(s_i)` indexed
by the actions themselves, which the `Finset` makes distinct. The load `v r` sums `y i s` over the
actions `s` of agent `i` that contain `r`. -/
def IsFeasible {ι E : Type*} [Fintype ι] [DecidableEq E] (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (y : ι → Finset E → ℝ) (v : E → ℝ) : Prop :=
  (∀ i s, 0 ≤ y i s) ∧ (∀ i s, s ∉ G.strategies i → y i s = 0) ∧
    (∀ i, ∑ s ∈ G.strategies i, y i s = 1) ∧
    ∀ r, v r = ∑ i, ∑ s ∈ (G.strategies i).filter (fun s => r ∈ s), y i s

end CongestionTaxes


