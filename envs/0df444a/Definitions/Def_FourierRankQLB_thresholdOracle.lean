-- Prove2me | Definitions.Def_FourierRankQLB_thresholdOracle
-- name    : FourierRankQLB_thresholdOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:26.680989+00:00
-- url     : https://prove2.me/theorems/3a2ac91b-64e6-492e-87ba-6c50c30de0dd
-- title:
--   Exact coherent query access to the predicate $m_Q$
-- statement:
--   For measurable $q:Y\to\mathbb R^d$ and $\tau:Y\to\mathbb R$, the unitary on $L^2(Y,\nu)\otimes\mathbb C^2\otimes W$ given by
--   $$
--   U_Q|y\rangle|b\rangle=|y\rangle|b\oplus m_Q(y)\rangle,\qquad m_Q(y)=\mathbf 1[q(y)^TQq(y)\le\tau(y)].
--   $$
--   Membership in the hard ellipsoids has this form, by (40)–(41).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Corollary 4.5, p.27 and Appendix A, p.50

import Mathlib
import Definitions.Def_FourierRankQLB_flipOn
import Definitions.Def_FourierRankQLB_thresholdSet

open MeasureTheory

namespace FourierRankQLB

/-- The exact coherent query to the Boolean predicate `m_Q(y) = 1[q(y)ᵀ Q q(y) ≤ τ(y)]`, that is
`|y⟩|b⟩ ↦ |y⟩|b ⊕ m_Q(y)⟩`, on `L²(Y, ν) ⊗ ℂ² ⊗ W`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Corollary 4.5, p. 27 and Appendix A, p. 50. -/
noncomputable def thresholdOracle {d : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] {q : Y → Fin d → ℝ} {τ : Y → ℝ}
    (hq : Measurable q) (hτ : Measurable τ) (Q : Od d) : QReg ν W ≃ₗᵢ[ℂ] QReg ν W :=
  flipOn ν W (thresholdSet q τ Q) (measurableSet_thresholdSet hq hτ Q)

end FourierRankQLB


