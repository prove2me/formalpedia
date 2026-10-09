-- Prove2me | Definitions.Def_EmpiricalDRO_Coverage_Setting
-- name    : EmpiricalDRO_Coverage_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:40.166736+00:00
-- url     : https://prove2.me/theorems/a281dc3c-4983-4f40-a41a-531e070f5dda
-- title:
--   (19), (22), (24), (26)–(27), pp. 6–11 — the Burg generator, the lower value Z_n of the empirical Burg ball, and −2 log R(μ)
-- statement:
--   This file fixes the three objects on which the empirical divergence-based DRO of Lam is built.
--
--   **The Burg generator.** For $t\in\mathbb R$,
--   $$
--   \varphi(t)=\begin{cases}-\log t+t-1, & t>0,\\ +\infty, & t\le 0.\end{cases}
--   $$
--   With reference weights $1/n$, the $\varphi$-divergence of a weight vector $w=(w_1,\dots,w_n)$ is $\sum_i \frac1n\varphi(nw_i)$. On the simplex $\sum_i w_i=1$ this equals $-\frac1n\sum_i\log(nw_i)$, so the ball $\{w\ge 0:\ \sum_i w_i=1,\ \sum_i\frac1n\varphi(nw_i)\le\eta\}$ is exactly the **empirical Burg-entropy divergence ball**
--   $$
--   \mathcal U_n(\eta)=\Big\{w:\ -\frac1n\sum_{i=1}^n\log(nw_i)\le\eta,\ \sum_{i=1}^n w_i=1,\ w_i\ge 0\Big\}
--   $$
--   of (19). A zero weight has infinite divergence, as with the convention $\log 0=-\infty$.
--
--   **The lower value.** For a sample $z=(z_1,\dots,z_n)$, a generator $f$ and $\rho\in\mathbb R$,
--   $$
--   \underline{Z}(f,\rho,z)=\inf\Big\{\sum_{i=1}^n w_iz_i:\ w\ge 0,\ \sum_i w_i=1,\ \sum_i\tfrac1n f(nw_i)\le \rho/n\Big\}.
--   $$
--   This is the lower counterpart of the published robust mean $\overline Z(f,\rho,z)$ (the supremum over the same ball). With $f=\varphi$ and $\rho=\chi^2_{1,1-\alpha}/2$, the pair $(\underline Z,\overline Z)$ is $(\underline Z_n(x),\overline Z_n(x))$ of (26)–(27), evaluated at $z_i=h(x;\xi_i)$.
--
--   **The empirical-likelihood statistic.** For a sample $z$ and a value $\mu$,
--   $$
--   -2\log R(\mu)=\inf\Big\{-2\sum_{i=1}^n\log(nw_i):\ w_i>0,\ \sum_i w_i=1,\ \sum_i w_iz_i=\mu\Big\}\in[0,+\infty],
--   $$
--   with the value $+\infty$ when no weight vector is feasible. This is $-2\log$ of the profile nonparametric likelihood ratio $R(\mu)=\max\{\prod_i nw_i\}$ of (22) and (24).
--
--   These objects are shared by every statement of the mission: the goal (Theorem 2) is about $\underline Z_n,\overline Z_n$, and the empirical likelihood theorem (Theorem 1) is about $-2\log R$.
--
--   **Formalization Note.** The generator is valued in extended reals, with value $+\infty$ for $t\le 0$, so a weight vector with a zero coordinate is outside every ball. In the statistic, weights are strictly positive: with $\log 0=-\infty$, a zero weight makes $\prod_i nw_i=0$, which never improves the maximum in (22), and if every feasible weight has a zero coordinate the infimum over the empty family is $+\infty$, which is the paper's convention. For the Burg generator, $n\ge1$, and $\rho\ge0$, the set of values $\sum_i w_iz_i$ over the ball is nonempty (it contains the uniform weights) and bounded (it lies in the simplex), so infimum and supremum are the paper's minimum and maximum. The radius parameter is $\rho$ with ball radius $\rho/n$, so $\mathcal U_n(\chi^2_{1,1-\alpha}/(2n))$ corresponds to $\rho=\chi^2_{1,1-\alpha}/2$.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 6 (Burg generator φ(x) = −log x + x − 1), pp. 8–9 (19), p. 10 (22), p. 11 (24), (26)–(27)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_robustMean

namespace EmpiricalDRO.Coverage

/-- The Burg generator `φ(t) = −log t + t − 1` (Lam, arXiv:1605.09349v1, p. 6), valued in `EReal`.
For `t ≤ 0` it is `⊤`: the paper's convention `log 0 = −∞` gives a zero weight infinite divergence.
With this generator and reference weights `1/n`, the published
`PhiDivRobust.Counterpart.probUncertaintySet burg (fun _ => 1/n) η` is the empirical Burg ball
`U_n(η) = {w : −(1/n) ∑ log(n wᵢ) ≤ η, ∑ wᵢ = 1, w ≥ 0}` of (19), p. 8. -/
noncomputable def burg (t : ℝ) : EReal :=
  if 0 < t then ((-Real.log t + t - 1 : ℝ) : EReal) else ⊤

/-- The lower robust value `inf { ∑ pᵢ zᵢ : p ∈ U_n(ρ/n) }` of the sample `z = (z₁, …, zₙ)` over the
empirical divergence ball with generator `f` and radius `ρ/n`, the `sInf` twin of the published
`GenEmpLik.Expansion.robustMean`. With `f = burg` and `ρ = χ²_{1,1−α}/2` it is `Z_n(x)` of (26),
p. 11. When `f = burg`, `0 < n`, and `0 ≤ ρ`, the value set is nonempty (it contains the
uniform vector) and bounded (it lies in the simplex), so the real `sInf` is the minimum. -/
noncomputable def robustLower {n : ℕ} (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → ℝ) : ℝ :=
  sInf ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
    PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n))

/-- The empirical-likelihood statistic `−2 log R(μ)` of the sample `z = (z₁, …, zₙ)` at the value `μ`
((22), p. 10, and (24), p. 11):
`inf { −2 ∑ log(n wᵢ) : wᵢ > 0, ∑ wᵢ = 1, ∑ wᵢ zᵢ = μ }`, valued in `EReal`.
The infimum of the empty family is `⊤`, the paper's "defined as ∞ if there is no feasible solution".
Weights are strictly positive: with `log 0 = −∞` a zero weight makes `∏ (n wᵢ) = 0`, which never
improves the maximum in (22), and gives `−2 log R = ∞` when every feasible weight has a zero. -/
noncomputable def elStat {n : ℕ} (z : Fin n → ℝ) (μ : ℝ) : EReal :=
  ⨅ (w : Fin n → ℝ) (_ : (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i * z i = μ),
    ((-2 * ∑ i, Real.log (n * w i) : ℝ) : EReal)

end EmpiricalDRO.Coverage


