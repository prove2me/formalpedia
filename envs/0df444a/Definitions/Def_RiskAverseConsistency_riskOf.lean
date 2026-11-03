-- Prove2me | Definitions.Def_RiskAverseConsistency_riskOf
-- name    : RiskAverseConsistency_riskOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:12.161941+00:00
-- url     : https://prove2.me/theorems/22f0c3ed-a3e2-4b98-a1a8-6c28421d497a
-- title:
--   Risk $\rho(X)$ of a random variable $X:\Omega\to\mathbb R$
-- statement:
--   For $\rho:L^p(\Omega,\mathcal F,P)\to\mathbb R$ and a function $X:\Omega\to\mathbb R$, $\rho(X)$ denotes $\rho$ evaluated at the $L^p$-class of $X$ when $X\in L^p(\Omega,\mathcal F,P)$.
--
--   This lets the statements write $\mathcal R[F(\mathbf Bz)]$ and $\rho(\hat H^{-1}_N(G(\cdot)))$ for concrete functions on $\Omega$.
--
--   **Formalization Note** For $X\notin L^p$ the value is a junk $0$. Every use in the mission is at a function in $L^p$: $F(\mathbf Bz)$ for $z\in Z_{\mathrm{ad}}$ under Assumption 10, and empirical quantile functions composed with a uniform $G$, which are bounded and measurable (both facts are proved in the mission's verification file).
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.3, §2.1 ($\rho(X)$, $\rho(H_X)=\rho(H_X^{-1}(G(\cdot)))$); p.8 ($\mathcal R[F(\mathbf Bz)]$)

import Mathlib

open MeasureTheory Classical

namespace RiskAverseConsistency

/-- The risk `ρ(X)` of a function `X : Ω → ℝ` under `ρ : Lᵖ(Ω, F, P) → ℝ`: `ρ` applied to the
`Lᵖ` class of `X` when `X ∈ Lᵖ(Ω, F, P)`.

Milz, Surowiec, arXiv:2207.14756v2, §2.1, p.3 (`ρ(X)`, `ρ(H_X) = ρ(H_X⁻¹(G(·)))`) and §3, p.8
(`ℛ[F(Bz)]`).

Formalization Note: the paper applies `ρ` only to elements of `Lᵖ`. For an `X` outside `Lᵖ` this
wrapper returns the junk value `0`; every use in this mission is at a function that is in `Lᵖ`
(`F(Bz)` by Assumption 10.5, empirical quantiles composed with `G` because they are bounded and
measurable — checked in `Solutions/verification/RiskAverseConsistency_memLp_branch`). -/
noncomputable def riskOf {Ω : Type*} [MeasurableSpace Ω] {p : ENNReal} {P : Measure Ω}
    (ρ : Lp ℝ p P → ℝ) (X : Ω → ℝ) : ℝ :=
  if h : MemLp X p P then ρ (h.toLp X) else 0

end RiskAverseConsistency


