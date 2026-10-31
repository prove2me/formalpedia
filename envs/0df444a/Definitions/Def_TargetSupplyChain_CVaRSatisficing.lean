-- Prove2me | Definitions.Def_TargetSupplyChain_CVaRSatisficing
-- name    : TargetSupplyChain_CVaRSatisficing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:10.348541+00:00
-- url     : https://prove2.me/theorems/f81e5920-7c79-463e-9001-de542604374a
-- title:
--   Extended CVaR $\mathrm{CVaR}_\eta$, $\eta\in(-1,1)$, and the CVaR-satisficing measure $\rho_\tau$ (Definition 1, (1))
-- statement:
--   Let $V$ be a real random variable with law $\mu$ and quantile function $Q_V(s)=\inf\{u:\ \mathbb P(V\le u)\ge s\}$.
--
--   **Extended CVaR.** For $\eta\in(-1,1)$,
--   $$
--   \mathrm{CVaR}_\eta(V)=\begin{cases}\dfrac{1}{1-\eta}\displaystyle\int_0^{1-\eta}Q_V(s)\,ds, & \eta\in[0,1),\\[2mm] \dfrac{1}{1+\eta}\displaystyle\int_{-\eta}^{1}Q_V(s)\,ds, & \eta\in(-1,0).\end{cases}
--   $$
--   For $\eta\ge 0$ this is the average of the worst $1-\eta$ fraction of outcomes (the paper's $\mathbb E[V\mid V\le q_{1-\eta}(V)]$); for $\eta<0$ it is the average of the best $1+\eta$ fraction (the paper's $\mathbb E[V\mid V\ge q_{-\eta}(V)]$). Both branches equal $\mathbb E[V]$ at $\eta=0$, and $\eta\mapsto\mathrm{CVaR}_\eta(V)$ is nonincreasing.
--
--   **CVaR-satisficing measure** (Brown and Sim 2009). For a target $\tau$,
--   $$
--   \rho_\tau(V)=\begin{cases}\sup\{\eta\in(-1,1):\ \mathrm{CVaR}_\eta(V)\ge\tau\}, & \text{if this set is nonempty (``feasible''),}\\ -1, & \text{otherwise.}\end{cases}
--   $$
--   A larger $\rho_\tau(V)$ means that $V$ attains the target $\tau$ more robustly: a positive value means even a lower-tail average reaches $\tau$, a negative value means only an upper-tail average does.
--
--   These are the decision criteria of the target-oriented retailer of the mission: the retailer maximizes $\rho_{\tau^r}$ of his random profit.
--
--   **Formalization Note** The paper's conditional expectations assume a unique $\eta$-quantile, which does not exist when $V$ has an atom (the retailer's profit has one); the quantile averages are the standard reading and agree with the printed formula whenever that quantile exists. The translated form (1), $\mathrm{CVaR}_\eta(V)\ge\tau$, is used in place of $\mathrm{CVaR}_\eta(V-\tau)\ge0$ (equivalent by translation invariance, p.6). The infeasible branch is the paper's $-1$, not Lean's $\sup\emptyset=0$. When every $\eta\in(-1,1)$ is feasible the measure is $1$, which is not attained. The quantile function is the published `RiskFunctionals.StochDominance.quantileFunction`; its junk values at $s=0$ (and at $s=1$ for unbounded laws) lie on a null set.
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §2.2, Definition 1 and eq. (1), p.6

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory Classical

namespace TargetSupplyChain

/-- The extended conditional value-at-risk `CVaR_η(V)` of a random variable with law `μ`,
`η ∈ (−1, 1)`, Chen–Tang, *Supply Chain Performance with Target-Oriented Firms*, SSRN 3533746
(version of July 6, 2021), §2.2, Definition 1, p.6:

* for `η ∈ [0, 1)`, the average of the worst `1 − η` of the distribution,
  `CVaR_η(V) = (1/(1 − η)) ∫_{(0, 1−η]} Q_V(s) ds` (the paper's `E[V | V ≤ q_{1−η}(V)]`);
* for `η ∈ (−1, 0)`, the average of the best `1 + η`,
  `CVaR_η(V) = (1/(1 + η)) ∫_{(−η, 1]} Q_V(s) ds` (the paper's `E[V | V ≥ q_{−η}(V)]`),

where `Q_V` is the quantile function `Q_V(s) = inf {u : P(V ≤ u) ≥ s}`.

**Formalization Note** The paper writes conditional expectations given `V ≤ q_{1−η}(V)` and
`V ≥ q_{−η}(V)` with "the unique η-quantile" `Prob(V ≤ q_η(V)) = η`. The retailer's profit has
an atom at `(p − w)y`, so no such quantile exists for most `η`; the quantile averages above are
the standard reading (Acerbi; Rockafellar–Uryasev), equal to the printed formula whenever the
quantile is unique, and the form the paper's Online Appendix computes with. The quantile
function's junk values (at `s = 0`, and at `s = 1` for unbounded laws) lie on a null set. The
value for `|η| ≥ 1` is never used. -/
noncomputable def extCVaR (μ : Measure ℝ) (η : ℝ) : ℝ :=
  if 0 ≤ η then
    (1 / (1 - η)) * ∫ s in (0 : ℝ)..(1 - η), RiskFunctionals.StochDominance.quantileFunction μ s
  else
    (1 / (1 + η)) * ∫ s in (-η)..(1 : ℝ), RiskFunctionals.StochDominance.quantileFunction μ s

/-- The CVaR-satisficing measure (CSM) `ρ_τ(V)` of a random variable with law `μ`, target `τ`
(Brown and Sim 2009), Chen–Tang, SSRN 3533746 (version of July 6, 2021), §2.2, Definition 1
and its translated form (1), p.6: `sup {η ∈ (−1, 1) : CVaR_η(V) ≥ τ}` if that set is nonempty
("if feasible"), and `−1` otherwise.

**Formalization Note** The (1) form is used; Definition 1's `CVaR_η(V − τ) ≥ 0` is the same
condition by translation invariance of `CVaR_η` (p.6). The set is bounded above by `1`, so the supremum is genuine; when every
`η ∈ (−1, 1)` is feasible it equals `1`, which is not attained. The infeasible branch is the
paper's `−1`, not Lean's `sSup ∅ = 0`. -/
noncomputable def csm (μ : Measure ℝ) (τ : ℝ) : ℝ :=
  if (∃ η, η ∈ Set.Ioo (-1 : ℝ) 1 ∧ τ ≤ extCVaR μ η) then
    sSup {η | η ∈ Set.Ioo (-1 : ℝ) 1 ∧ τ ≤ extCVaR μ η}
  else -1

end TargetSupplyChain


