-- Prove2me | Definitions.Def_LogLogJam_fisherInfo
-- name    : LogLogJam_fisherInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:57.987908+00:00
-- url     : https://prove2.me/theorems/fb796222-5b19-47d5-8917-4555ec1b9f1b
-- title:
--   Fisher information of a parametric family, Fisher information on the circle, and $f(x)=x+\sqrt x$
-- statement:
--   For a family of probability densities $q_\theta$ on a measure space $(X,\mu)$, the **Fisher information** at $\theta$ is
--
--   $$
--   J(\theta)=\mathbb E_{x\sim q_\theta}\big[(\partial_\theta\log q_\theta(x))^2\big]=\int_X q_\theta(x)\,(\partial_\theta\log q_\theta(x))^2\,d\mu(x)\in[0,\infty].
--   $$
--
--   For a probability density $p$ on the circle $\mathbb T=\mathbb R/\pi\mathbb Z$, its Fisher information (as a location family) is
--
--   $$
--   F(p)=\mathbb E_{\theta\sim p}\big[(\partial_\theta\log p(\theta))^2\big]=\int_0^\pi p(\theta)\,(\partial_\theta\log p(\theta))^2\,d\theta .
--   $$
--
--   Finally $f(x)=x+\sqrt x$, and $f^{\circ n}$ denotes its $n$-fold composition ($f^{\circ0}=\mathrm{id}$). The first quantity measures how much one experiment reveals about $\theta$; the second, how concentrated a posterior is; the third drives the $\log\log E$ recursion of §6.2.2.
--
--   **Formalization Note** Both Fisher informations are lower Lebesgue integrals in $[0,\infty]$, so they never collapse to a junk $0$; where the density is $\le0$ the integrand is $0$.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §5.3, p.23 (PDF p.26) ($J_M$); §5.5, p.26 and Lemma 5.11, p.27 ($F(p)$); §6.2.2, p.32 (PDF p.35) ($f$, $f^{\circ k}$)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- The **Fisher information** at `θ` of a one-parameter family of densities `q θ` on a measure space
`(X, μ)`: `J(θ) = E_{x ∼ q_θ}[(∂_θ log q_θ(x))²] = ∫ q_θ(x) (∂_θ log q_θ(x))² dμ(x)`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §5.3, p.23: "J_M(θ) =
E_{y∼f^M_θ}[(∂_θ log f^M_θ(y))²]"; the same definition gives `J_t`, `J_X`, `J_{X,Y}` and
`J_{Y|X}` of §5.3–5.4).

**Formalization Note** The value is in `[0, ∞]` (a lower Lebesgue integral of a nonnegative
integrand), so no integrability side condition can make it collapse to `0`. Where `q θ x ≤ 0` the
integrand is `0`. The derivative is Mathlib's `deriv` in `θ`. -/
noncomputable def fisherInfo {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ → X → ℝ)
    (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (q θ x) * ENNReal.ofReal ((deriv (fun θ' => Real.log (q θ' x)) θ) ^ 2) ∂μ

/-- The Fisher information `F(p) = E_{θ∼p}[(∂_θ log p(θ))²] = ∫_0^π p(θ) (∂_θ log p(θ))² dθ` of a
probability density `p` on the circle `𝕋 = ℝ/πℤ` (arXiv:2607.12983, version of November 3, 2026,
sha256 97b751ca…, §5.5, p.26, and Lemma 5.11, p.27).

**Formalization Note** `p` is a function on `ℝ`, `π`-periodic in the applications, and the
integral is over one period `[0, π)`. Valued in `[0, ∞]`. -/
noncomputable def circFisher (p : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ico 0 Real.pi,
    ENNReal.ofReal (p θ) * ENNReal.ofReal ((deriv (fun θ' => Real.log (p θ')) θ) ^ 2)

/-- `f(x) = x + √x` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §6.2.2,
p.32). -/
noncomputable def fStep (x : ℝ) : ℝ :=
  x + Real.sqrt x

/-- The `n`-fold composition `f^{∘n}` of `f(x) = x + √x` (arXiv:2607.12983, version of November 3,
2026, sha256 97b751ca…, §6.2.2, p.32); `f^{∘0}` is the identity. -/
noncomputable def fIter (n : ℕ) (x : ℝ) : ℝ :=
  fStep^[n] x

end LogLogJam


