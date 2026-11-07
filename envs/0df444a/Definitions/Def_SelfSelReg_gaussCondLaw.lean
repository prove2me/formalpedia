-- Prove2me | Definitions.Def_SelfSelReg_gaussCondLaw
-- name    : SelfSelReg_gaussCondLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:35.077717+00:00
-- url     : https://prove2.me/theorems/7a696852-1fbe-4a60-9e2b-2fabcb1e21ea
-- title:
--   The conditional law of a centered Gaussian pair $(G,Y)$ given $Y=t$
-- statement:
--   Let $G\sim N(0,I_n)$ and $Y$ be centered jointly Gaussian with $\mathrm{Var}(Y)=\sigma^2>0$ and $v=\mathbb E[GY]$; then $\|v\|_2^2\le\sigma^2$ and $(G,Y)$ has the law of $(G,\langle v,G\rangle+\sqrt{\sigma^2-\|v\|_2^2}\,g)$ with $g\sim N(0,1)$ independent of $G$. Proposition 4.3 gives
--   $$G\mid Y=t\ \sim\ N\Big(\frac{vt}{\sigma^2},\ I_n-\frac{vv^\top}{\sigma^2}\Big)\qquad(t\in\mathbb R).$$
--   This file defines that conditional law explicitly, for every $t$: it is the image of $N(0,I_n)\otimes N(0,1)$ under $(x,g)\mapsto(x,g)-c\,(v,\sqrt{\sigma^2-\|v\|^2})$ with $c=(\langle v,x\rangle+\sqrt{\sigma^2-\|v\|^2}\,g-t)/\sigma^2$. Its image lies on $\{Y=t\}$ and its first marginal is the Gaussian above.
--
--   It is the meaning of "$\mathbb E[\,\cdot\mid Y=t]$" in Propositions 5.2 and 5.5.
--
--   **Formalization Note** Conditioning on the null event $\{Y=t\}$ is made precise by this explicit regression-residual law, the continuous version of the conditional distribution, instead of an almost-everywhere defined conditional expectation evaluated at a point.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 4.3, p.16 (PDF p.19); Propositions 5.2, 5.5, pp.20–21 (PDF pp.23–24)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- The conditioning map for a pair `(G, Y)` with `G ∼ N(0, I_n)`, `Y = ⟨v, G⟩ + √(σ² − ‖v‖²)·g`,
`g ∼ N(0, 1)` independent of `G`: `(x, g) ↦ (x, g) − ((y − t)/σ²)·(v, √(σ² − ‖v‖²))`, where
`y = ⟨v, x⟩ + √(σ² − ‖v‖²)·g`. Its image has `Y = t`. -/
noncomputable def gaussCondMap {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (σsq t : ℝ)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) : EuclideanSpace ℝ (Fin n) × ℝ :=
  let a := Real.sqrt (σsq - ‖v‖ ^ 2)
  let c := (inner ℝ v z.1 + a * z.2 - t) / σsq
  (z.1 - c • v, z.2 - c * a)

/-- **The conditional law of a centered Gaussian pair given `Y = t`** (Proposition 4.3).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 4.3, p.16 (PDF p.19): "Let G ∈ ℝⁿ and Y ∈ ℝ be centered
jointly Gaussian. Write Σ = E_G[GGᵀ], v = E_{G,Y}[GY], and σ² = E_Y[Y²] > 0. For every t ∈ ℝ,
G | Y = t ∼ N(vt/σ², Σ − vvᵀ/σ²)."

For `G ∼ N(0, I_n)`, `Var(Y) = σ²` and `v = E[GY]` (so `‖v‖² ≤ σ²`), `gaussCondLaw v σ² t` is the law
of `(G, g)` given `Y = t`, as the pushforward of `N(0, I_n) ⊗ N(0, 1)` under `gaussCondMap`; its first
marginal is `N(tv/σ², I_n − vvᵀ/σ²)`.

**Formalization Note.** Every centered jointly Gaussian pair with `G ∼ N(0, I_n)` has the law of
`(G, ⟨v, G⟩ + √(σ² − ‖v‖²)·g)`, so the pair is determined in law by `v` and `σ²`. "E[· | Y = t]" is the
integral against this explicit law, defined for every `t` (the regression-residual version of the
conditional expectation), not an almost-everywhere defined conditional expectation evaluated at a
point. -/
noncomputable def gaussCondLaw (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (σsq t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (gaussianReal 0 1)).map (gaussCondMap v σsq t)

end SelfSelReg


