-- Prove2me | Definitions.Def_FourierRankQLB_thresholdSet
-- name    : FourierRankQLB_thresholdSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:29.843571+00:00
-- url     : https://prove2.me/theorems/070360b0-aa99-47bf-9461-18bbeabb27ce
-- title:
--   The threshold set of $m_Q(y)=\mathbf 1[q(y)^TQq(y)\le\tau(y)]$
-- statement:
--   For $q:Y\to\mathbb R^d$, $\tau:Y\to\mathbb R$ and $Q\in O(d)$, the set of labels
--   $$
--   \{y\in Y: q(y)^TQq(y)\le\tau(y)\},
--   $$
--   where the Boolean predicate $m_Q$ equals one. The module also records that it is measurable for measurable $q$ and $\tau$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Corollary 4.5, p.27

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open Matrix

namespace FourierRankQLB

/-- The set of labels where the threshold predicate `m_Q(y) = 1[q(y)ᵀ Q q(y) ≤ τ(y)]` holds.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Corollary 4.5, p. 27. -/
def thresholdSet {d : ℕ} {Y : Type} (q : Y → Fin d → ℝ) (τ : Y → ℝ) (Q : Od d) : Set Y :=
  {y | q y ⬝ᵥ ((Q : Matrix (Fin d) (Fin d) ℝ) *ᵥ q y) ≤ τ y}

theorem measurableSet_thresholdSet {d : ℕ} {Y : Type} [MeasurableSpace Y] {q : Y → Fin d → ℝ}
    {τ : Y → ℝ} (hq : Measurable q) (hτ : Measurable τ) (Q : Od d) :
    MeasurableSet (thresholdSet q τ Q) := by
  have hqi : ∀ i, Measurable fun y => q y i := fun i => (measurable_pi_apply i).comp hq
  refine measurableSet_le ?_ hτ
  simp only [dotProduct, mulVec]
  exact Finset.measurable_sum _ fun i _ => (hqi i).mul
    (Finset.measurable_sum _ fun j _ => measurable_const.mul (hqi j))

end FourierRankQLB


