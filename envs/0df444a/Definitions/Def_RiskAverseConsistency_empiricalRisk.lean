-- Prove2me | Definitions.Def_RiskAverseConsistency_empiricalRisk
-- name    : RiskAverseConsistency_empiricalRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:02.272204+00:00
-- url     : https://prove2.me/theorems/ebf0c153-2f8f-4bef-8503-09206de53efc
-- title:
--   Plug-in risk $\rho(\hat H_N)=\rho(\hat H_N^{-1}(G(\cdot)))$ of a sample
-- statement:
--   Let $x_1,\dots,x_N$ be real numbers, let
--
--   $$
--   \hat H_N(t)=\frac1N\sum_{i=1}^N\mathbf 1_{(-\infty,t]}(x_i)
--   $$
--
--   be their empirical distribution function and $\hat H_N^{-1}(q)=\inf\{s\in\mathbb R:\hat H_N(s)\ge q\}$, $q\in(0,1)$, its quantile function. For a uniformly distributed $G:\Omega\to[0,1]$ and $\rho:L^p(\Omega,\mathcal F,P)\to\mathbb R$, the **plug-in risk** of the sample is
--
--   $$
--   \rho(\hat H_N):=\rho\bigl(\hat H_N^{-1}(G(\cdot))\bigr).
--   $$
--
--   For law invariant $\rho$ this is the risk of the empirical distribution; it is the building block of the empirical approximation (10) and of $\hat\phi_N$ in Theorem 21.
--
--   **Formalization Note** The sample is the first $N$ entries $x_0,\dots,x_{N-1}$ of a sequence. The quantile function and empirical distribution function are the published `CompetingAgents.quantile` and `CompetingAgents.empiricalCDF`. At levels outside $(0,1)$ the quantile is a junk value; for uniform $G$ this happens on a $P$-null set. At $N=0$ the value is junk; only $N\to\infty$ is used.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.3 (quantile function, $\rho(H)$); p.8 ($\hat H_{y,N}$); pp.16–17 ($\hat\phi_N$, $\rho(\hat H_N)$)

import Mathlib
import Definitions.Def_CompetingAgents_quantile
import Definitions.Def_RiskAverseConsistency_riskOf

open MeasureTheory

namespace RiskAverseConsistency

/-- The plug-in (empirical) risk `ρ(Ĥ_N) := ρ(Ĥ_N⁻¹(G(·)))` of the first `N` entries
`x 0, …, x (N-1)` of a real sequence: `Ĥ_N` is their empirical distribution function
`Ĥ_N(t) = (1/N) Σᵢ 1_{(−∞,t]}(xᵢ)`, `Ĥ_N⁻¹(q) = inf {s : Ĥ_N(s) ≥ q}` its quantile function, and
`G : Ω → [0,1]` a uniformly distributed random variable.

Milz, Surowiec, arXiv:2207.14756v2, §2.1, p.3 (quantile function, `ρ(H) := ρ(H⁻¹(G(·)))`), §3,
p.8 (`Ĥ_{y,N}`), Appendix A, pp.16–17 (`φ̂_N`, `ρ(Ĥ_N)`).

Formalization Note: the paper's sample is `x¹, …, x^N`; here it is `x 0, …, x (N-1)`. The
quantile function is the published `CompetingAgents.quantile` (`inf {r : q ≤ H r}`, a real `sInf`)
and the empirical distribution function is `CompetingAgents.empiricalCDF`. The paper defines the
quantile on `(0,1)`; at `G ω ∈ {0, 1}` or outside `[0,1]` the value here is a junk value, which
happens only on a `P`-null set when `G` is uniform on `[0,1]`. At `N = 0` the empirical distribution
function is `0` and the value is junk; only `N → ∞` is used. -/
noncomputable def empiricalRisk {Ω : Type*} [MeasurableSpace Ω] {p : ENNReal} {P : Measure Ω}
    (ρ : Lp ℝ p P → ℝ) (G : Ω → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  riskOf ρ (fun ω => CompetingAgents.quantile (G ω)
    (CompetingAgents.empiricalCDF (fun i : Fin N => x i)))

end RiskAverseConsistency


