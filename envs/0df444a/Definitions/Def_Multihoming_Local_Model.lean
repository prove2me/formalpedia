-- Prove2me | Definitions.Def_Multihoming_Local_Model
-- name    : Multihoming_Local_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:53.119361+00:00
-- url     : https://prove2.me/theorems/f5aca54c-1d0d-4ff9-9a00-17df4e848226
-- title:
--   §3, (5), (14)–(18), PDF pp. 14, 17–18 — multihoming demand, reaction function, candidate prices, outputs, singlehomers, multihomers and profits
-- statement:
--   Two firms $i\in\{0,1\}$ sit at the ends of a Hotelling line of unit length, on which a unit mass of consumers is uniformly distributed. The mismatch cost is $t>0$, the strength of the network effect is $\mu\ge0$, and $e_i$ denotes the value of the exclusive features of good $i$. Throughout, $j$ denotes the rival of $i$. When some consumers buy both goods and expectations are fulfilled ($z_i=x_i$), the demand for good $i$ at prices $(p_i,p_j)$ is
--
--   $$
--   x_i^M(p_i,p_j)=\frac{\mu}{t+\mu}+t\,\frac{e_i-p_i}{t^2-\mu^2}-\mu\,\frac{e_j-p_j}{t^2-\mu^2}. \qquad (14)
--   $$
--
--   This file defines the following objects.
--
--   1. **Demand** $x_i^M(p_i,p_j)$ as in (14).
--   2. **Reaction function** of firm $i$: $p_i^M(p_j)=\dfrac{t\mu-\mu^2+te_i}{2t}+\mu\,\dfrac{p_j-e_j}{2t}$, as in (15).
--   3. **Candidate partial-multihoming price** of firm $i$: $p_i^M=\dfrac{t-\mu}{2t-\mu}(\mu+e_i)+\dfrac{\mu t}{4t^2-\mu^2}(e_i-e_j)$, as in (16).
--   4. **Output** $x_i^M=x_i^M(p_i^M,p_j^M)$, the demand (14) at the candidate prices (16).
--   5. **Singlehomers** of good $i$ (consumers who buy only good $i$): $s_i=1-x_j$, as in (17).
--   6. **Multihomers** (consumers who buy both goods): $m=1-s_0-s_1$, as in (18).
--   7. **Profit** of firm $i$ at the candidate prices: $\pi_i=p_i^M x_i^M$, as in (5) with marginal costs normalized to zero.
--
--   Every function takes the parameters in the order $(t,\mu,e_i,e_j)$, own exclusive features first, so firm 1's objects are obtained by swapping $e_0$ and $e_1$.
--
--   These are the objects of the paper's comparative statics in $\mu$ near $\mu=0$ (Proposition 1).
--
--   **Formalization Note** All parameters are real numbers. The overlapping features $o$ cancel from every object here and are not a parameter. The derivation of (14) from the consumer's choice problem (10)–(13) with fulfilled expectations, and the full pricing game, are not formalized: (14) is taken as the model's demand. The definitions are total functions of real arguments; all denominators $t+\mu$, $t^2-\mu^2$, $2t-\mu$, $4t^2-\mu^2$, $2t$ are positive when $t>0$ and $0\le\mu<t$, and every theorem that uses them carries the hypotheses that make them so (or, for derivatives at $\mu=0$, only $t>0$).
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 14 (printed p. 8), (5); PDF pp. 17–18 (printed pp. 11–12), (14), (15), (16), (17), (18)

import Mathlib

namespace Multihoming.Local

/-- (14), PDF p. 17: multihoming demand for good `i` at prices `(pi, pj)` under fulfilled
expectations, `x_i^M(p_i, p_j) = μ/(t+μ) + t(e_i − p_i)/(t²−μ²) − μ(e_j − p_j)/(t²−μ²)`. -/
noncomputable def demandM (t μ ei ej pi pj : ℝ) : ℝ :=
  μ / (t + μ) + t * (ei - pi) / (t ^ 2 - μ ^ 2) - μ * (ej - pj) / (t ^ 2 - μ ^ 2)

/-- (15), PDF p. 17: firm `i`'s reaction function under multihoming,
`p_i^M(p_j) = (tμ − μ² + t e_i)/(2t) + μ(p_j − e_j)/(2t)`. -/
noncomputable def reactM (t μ ei ej pj : ℝ) : ℝ :=
  (t * μ - μ ^ 2 + t * ei) / (2 * t) + μ * (pj - ej) / (2 * t)

/-- (16), PDF p. 18: candidate partial-multihoming price of firm `i`,
`p_i^M = (t−μ)/(2t−μ)·(μ + e_i) + μt/(4t²−μ²)·(e_i − e_j)`. -/
noncomputable def priceM (t μ ei ej : ℝ) : ℝ :=
  (t - μ) / (2 * t - μ) * (μ + ei) + μ * t / (4 * t ^ 2 - μ ^ 2) * (ei - ej)

/-- (16), PDF p. 18: firm `i`'s output, the demand (14) evaluated at the prices (16). -/
noncomputable def outM (t μ ei ej : ℝ) : ℝ :=
  demandM t μ ei ej (priceM t μ ei ej) (priceM t μ ej ei)

/-- (17), PDF p. 18: consumers who buy only good `i`, `s_i = 1 − x_j`. -/
noncomputable def singleM (t μ ei ej : ℝ) : ℝ := 1 - outM t μ ej ei

/-- (18), PDF p. 18: consumers who buy both goods, `m = 1 − s₀ − s₁`. -/
noncomputable def multiM (t μ e0 e1 : ℝ) : ℝ := 1 - singleM t μ e0 e1 - singleM t μ e1 e0

/-- (5), PDF p. 14: firm `i`'s profit `π_i = p_i x_i` (zero marginal cost) at the
partial-multihoming prices (16). -/
noncomputable def profitM (t μ ei ej : ℝ) : ℝ := priceM t μ ei ej * outM t μ ei ej

end Multihoming.Local


