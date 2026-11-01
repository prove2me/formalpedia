-- Prove2me | Definitions.Def_LocalDOvS_SUS_InMC
-- name    : LocalDOvS_SUS_InMC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:19.342097+00:00
-- url     : https://prove2.me/theorems/9b3c4455-7d03-4ea7-8fae-24225a98c6c3
-- title:
--   The class $\mathcal M_C$ of convex sub-Gaussian models
-- statement:
--   A model belongs to the class $\mathcal M_C$ on $X=[N]$ with sub-Gaussian parameter bound $\sigma^2$ if
--
--   1. (Assumption 1) its objective $f$ is discretely convex on $[N]$;
--   2. (Assumption 2) for every $x\in[N]$ the centred output $F(x,\xi_x)-f(x)$ is sub-Gaussian with parameter $\sigma^2$:
--
--   $$
--   \mathbb E\big[e^{t(F(x,\xi_x)-f(x))}\big]\le e^{\sigma^2t^2/2}\qquad\text{for all }t\in\mathbb R .
--   $$
--
--   These are the models on which the algorithms of the paper must deliver their guarantee.
--
--   **Formalization Note** Mathlib's `HasSubgaussianMGF` with parameter $\sigma^2$; it includes integrability of the exponential moments and implies that the centred output has mean zero. Since it is monotone in the parameter, "upper bound $\sigma^2$ on the parameter" is the same condition. Assumption 3 ($X=[N]$, $d=1$, $N\ge 2$) is the role of $N$; $N\ge2$ is a hypothesis of the theorems.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Assumptions 1–3, pp.8–10; §3, p.11

import Mathlib
import Definitions.Def_LocalDOvS_SUS_DiscConvex
import Definitions.Def_LocalDOvS_SUS_meanFn

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LocalDOvS.SUS

/-- Membership in the class `M_C` of convex models on `X = [N]` with known sub-Gaussian
parameter bound `σ²` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Assumptions 1–3, pp.8–10, with
the discrete convexity of §3, p.11):

1. (Assumption 1) `f = meanFn M` is discretely convex on `[N]`;
2. (Assumption 2) for every `x ∈ [N]`, the centred output `F(x, ξ_x) − f(x)` is sub-Gaussian
   with parameter `σ²`.

**Formalization Note.** Sub-Gaussianity is Mathlib's `HasSubgaussianMGF … (σ ^ 2)`:
`E[e^{t(Y − f(x))}] ≤ e^{σ² t² / 2}` for all real `t`, which also forces `E[Y − f(x)] = 0` and
integrability of the output. It is monotone in the parameter, so "upper bound `σ²` on the
parameter" and "parameter `σ²`" coincide. Assumption 3 (`X = [N]`, `d = 1`, `N ≥ 2`) is the
role of `N` here; `N ≥ 2` is a hypothesis of each theorem. -/
def InMC (N : ℕ) (σ : ℝ≥0) (M : Model) : Prop :=
  DiscConvex N (meanFn M) ∧
    ∀ x ∈ Finset.Icc 1 N, HasSubgaussianMGF (fun y => y - meanFn M x) (σ ^ 2) (M.law x)

end LocalDOvS.SUS


