-- Prove2me | Definitions.Def_TentNoise_pathW1
-- name    : TentNoise_pathW1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:11.314195+00:00
-- url     : https://prove2.me/theorems/ce374af5-2c94-48ae-b4ad-b6af3120c6da
-- title:
--   The normalized path metric $\rho_{1,T}$ and the path Wasserstein distance $W_{1,\rho_{1,T}}$
-- statement:
--   For paths $x=(x_0,\dots,x_T)$ and $y=(y_0,\dots,y_T)$ in $[0,1]^{T+1}$, the **length-normalized $\ell^1$ path metric** is
--
--   $$
--   \rho_{1,T}(x,y):=\frac1{T+1}\sum_{t=0}^{T}|x_t-y_t| .
--   $$
--
--   For probability measures $\mathbb P_T,\mathbb Q_T$ on path space, the **path Wasserstein distance** is
--
--   $$
--   W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb Q_T):=\inf_{\gamma\in\Gamma(\mathbb P_T,\mathbb Q_T)}\mathbb E_\gamma\bigl[\rho_{1,T}(X,Y)\bigr],
--   $$
--
--   where $\Gamma(\mathbb P_T,\mathbb Q_T)$ is the set of couplings, i.e. probability measures on pairs of paths whose marginals are $\mathbb P_T$ and $\mathbb Q_T$.
--
--   The normalization by $T+1$ keeps the distance from growing merely because more time points are compared; all of the mission's bounds are uniform in $T$ for this distance.
--
--   **Formalization Note** Paths are functions $\mathrm{Fin}(T+1)\to\mathbb R$. The distance is the published optimal transport cost `ModelRiskOT.WorstProb.transportCost` with cost $\rho_{1,T}$: an infimum of lower Lebesgue integrals, valued in $[0,\infty]$. It is $\infty$ only when no coupling exists, which never happens for the probability path laws of the mission. Only the primal (coupling) form of the paper's Definition 2.5 is used.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.4, p.4 (PDF p.4), eq. (4) with p = 1; Definition 2.5, p.4, primal form

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_TransportBall

open MeasureTheory
open scoped ENNReal

namespace TentNoise

/-- The length-normalized `ℓ¹` path metric
`ρ_{1,T}(x, y) = (1/(T+1)) ∑_{t=0}^{T} |x_t − y_t|`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.4, p.4, eq. (4), case p = 1).

**Formalization Note** Paths `x_{0:T}` are functions `Fin (T+1) → ℝ`; the paper's paths lie in
`[0,1]^{T+1}`, and every measure the mission compares is concentrated there. -/
noncomputable def pathDist (T : ℕ) (x y : Fin (T + 1) → ℝ) : ℝ :=
  (1 / ((T : ℝ) + 1)) * ∑ t, |x t - y t|

/-- The path Wasserstein distance `W_{1,ρ_{1,T}}(P, Q) = inf_{γ ∈ Γ(P,Q)} E_γ[ρ_{1,T}(X, Y)]`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.5, p.4, primal form, p = 1).

**Formalization Note** This is the published optimal transport cost
`ModelRiskOT.WorstProb.transportCost` with cost `ρ_{1,T}`: the infimum, over probability measures
`γ` on pairs of paths with marginals `P` and `Q`, of the lower Lebesgue integral of `ρ_{1,T}`.
It takes values in `[0, ∞]`; it is `∞` only when there is no coupling (e.g. when `P`, `Q` are
not both probability measures), which never happens for the path laws of the mission. -/
noncomputable def pathW1 (T : ℕ) (P Q : Measure (Fin (T + 1) → ℝ)) : ℝ≥0∞ :=
  ModelRiskOT.WorstProb.transportCost (pathDist T) P Q

end TentNoise


